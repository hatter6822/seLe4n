# SM8 — Information Flow Under SMP (WS-SM Phase 8)

> **Phase**: SM8 of WS-SM
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Audited cut**: `v0.31.2`
> **Target releases**: v0.91.0 .. v0.97.x (parallel with SM7)
> **Calendar estimate**: 5-8 weeks
> **Sub-task count**: 40-55 across ~15-22 PRs

## 1. Phase goal

SM8 extends the existing non-interference (NI) proofs to per-
core observers; documents the new lock-contention covert
channel; per-core declassification audit.

**Concrete deliverables**:

1. **Per-core observable state** (SM8.A): `ObservableState.onCore
   (c) (L) (s)` — projection at (core, label).
2. **Per-core NI proofs** (SM8.B): existing NI proofs generalized;
   `crossCoreNonInterference` theorem.
3. **Lock-contention covert channel** (SM8.C): documented as a
   5th accepted channel (existing 4 + this one).
4. **Per-core declassification audit** (SM8.D):
   `DeclassificationEvent` extended with `originatingCore`.
5. **Information flow under fine locks** (SM8.D extension).
6. **Tests + closure** (SM8.E).

## 2. Dependencies

- **SM4**: per-core SchedulerState.
- **SM5**: per-core scheduler.
- **SM6**: cross-core IPC (for NI through IPC).

## 3. Mathematical foundations

### 3.1 Per-core observer

**Definition 3.1.1** (Observer). An *observer* is a pair `(c, L)`
of (core, security-label) — an attacker thread running on core c
with label L.

### 3.2 Per-core observable state

**Definition 3.2.1** (Per-core projection).

```lean
def ObservableState.onCore
    (c : CoreId) (L : SecurityLabel) (s : SystemState) :
    ObservableState :=
  { current      := s.scheduler.currentOnCore c
  , runQueue     := s.scheduler.runQueueOnCore c
  , activeDomain := s.scheduler.activeDomainOnCore c
  , objects      := { o ∈ s.objects | labelOf o ⊑ L }
  , serviceRegistry := ...
  , -- other label-filtered fields
  }
```

The projection includes:
- **Per-core fields** (current, runQueue, activeDomain) restricted
  to `c`.
- **Shared fields** (objects, serviceRegistry) filtered by label
  flow.

### 3.3 Cross-core NI

**Theorem 3.3.1** (`crossCoreNonInterference`). For observers
`(c, L)`, if a transition τ on a different core c' ≠ c does not
mutate any object o with `labelOf o ⊑ L` AND does not signal a
notification observable by `(c, L)`, then
`ObservableState.onCore c L` is unchanged across τ.

```lean
theorem crossCoreNonInterference
    (s : SystemState) (τ : KernelTransition) (args : Args)
    (c c' : CoreId) (L : SecurityLabel) :
    c ≠ c' →
    transitionRunsOnCore τ c' →
    transitionDoesntMutateLabelLeqObjects τ args L →
    transitionDoesntSignalLabelObservableNotification τ args L →
    let s' := τ.body args s
    ObservableState.onCore c L s = ObservableState.onCore c L s'
```

*Proof.* The transition on c' holds a lock-set whose objects
(by hypothesis) are disjoint from c's L-observable objects. By
serializability (Cor 2.1.11), c-observable state writes happen
only with c's locks held, which c' does not have. The projection
therefore is unchanged. □

### 3.4 Lock-contention as a covert channel

**Definition 3.4.1** (Lock-contention timing channel). When core
c spins on a contended lock l held by another core c', c can
measure the spin duration. This duration leaks information about
c''s critical-section length, which may correlate with confidential
data on c'.

```lean
def acceptedCovertChannel_lockContention : CovertChannel :=
  { name := "lock-contention timing"
    description := "Core spinning on contended lock can measure
      the duration of another core's critical section, leaking
      information about the held lock's holder."
    mitigation := "WS-W (CCA/MPAM partitioning) narrows the
      channel via partition-aware lock scheduling."
    severity := .medium }
```

### 3.5 Total accepted covert channels under SMP

Existing 4 (from V6-L):
1. CC-1: Scheduling state (`activeDomain`, etc.).
2. CC-2: Machine timer (`CNTVCT_EL0`).
3. CC-3: TCB metadata.
4. CC-4: Object store metadata.

SM8 adds:
5. **CC-5: Lock-contention timing**.

`enforcementBoundaryExtended` grows from 22 entries (V6-L) to
23+ entries.

## 4. Architectural choices

### 4.1 Why per-core observers (not per-thread)

Per-core observers because:
- An attacker thread is bound to a specific core (via
  `cpuAffinity`).
- Cross-core leakage flows through scheduling decisions, lock
  contention, and IPC — all per-core operations.
- The proof structure is cleaner: each core's view is a function
  of its per-core state plus label-filtered shared state.

### 4.2 Why lock-contention is "accepted" (not closed)

Eliminating the lock-contention channel would require:
- Lock-free data structures (very high proof cost).
- Per-domain lock partitioning (a CCA/MPAM-level feature).

For v1.0.0, the channel is **documented and accepted** as a
known covert channel. Mitigation is deferred to WS-W (post-1.0).

### 4.3 Why `DeclassificationEvent.originatingCore`

When a thread on c₁ declassifies state observed on c₂ (e.g., via
cross-core IPC), the audit trail must record the originating
core. The field's added; the audit invariant preserved.

## 5. Detailed sub-task breakdown

### SM8.A — Per-core observable state (3 PRs, 6 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM8.A.1 | `ObservableState.onCore (c, L, s)` | (def) | M |
| SM8.A.2 | `onCore_isProjection_of_globalProjection` | Theorem | M |
| SM8.A.3 | `onCore_decidable` | Instance | S |
| SM8.A.4 | `onCore_perCore_independence` | Theorem | M |
| SM8.A.5 | `onCore_label_monotone` | Theorem | M |
| SM8.A.6 | Start `tests/SmpInformationFlowSuite.lean` | M |

### SM8.B — Per-core NI proofs (5 PRs, 14 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM8.B.1 | `nonInterference_perCore` (existing NI generalized) | Theorem | XL |
| SM8.B.2 | `crossCoreNonInterference` (Thm 3.3.1) | Theorem | XL |
| SM8.B.3 | Per-core NI for each of 32 `kernelOperationNi` constructors | 32 theorems | L |
| SM8.B.4 | NI under per-object lock-set | Theorem | L |
| SM8.B.5 | `niStepCoverage_perCore` | Theorem | M |
| SM8.B.6 | `enforcementBoundaryExtended_perCore` (23 entries) | Definition + theorem | M |
| SM8.B.7 | Boundary completeness witness | Theorem | M |
| SM8.B.8 | `acceptedCovertChannel_lockContention` | Definition | M |
| SM8.B.9 | Mitigation note (WS-W partitioning) | Documentation | S |
| SM8.B.10 | `acceptedCovertChannel_perCoreCount = 5` | Theorem | T |
| SM8.B.11 | `endpointPolicyRestricted_perCore` | Theorem | M |
| SM8.B.12 | Per-core NI bridge to NI release | Theorem | M |
| SM8.B.13 | `crossCoreLeakage_bounded` | Theorem | L |
| SM8.B.14 | 15+ NI scenarios (tests) | L |

### SM8.C — Per-core declassification audit (3 PRs, 7 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM8.C.1 | `DeclassificationEvent.originatingCore : CoreId` extension | Structure | M |
| SM8.C.2 | Cross-core declassification chains in audit trail | Theorem | M |
| SM8.C.3 | Every declass event has valid originatingCore | Theorem | S |
| SM8.C.4 | `DeclassificationEvent_perCore_audit` | Theorem | M |
| SM8.C.5 | `authorizationBasis_perCore` extending V6-H | Theorem | M |
| SM8.C.6 | Cross-core declass rules | Theorem | M |
| SM8.C.7 | Per-core declass test scenarios | M |

### SM8.D — Information flow under fine locks (3 PRs, 6 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM8.D.1 | Lock state visibility documented | docstring | M |
| SM8.D.2 | Reader-multiplicity not directly observable | Theorem | M |
| SM8.D.3 | Writer-exclusion observable to blocked readers | docstring | T |
| SM8.D.4 | Biba-integrity under per-core locks | Theorem | M |
| SM8.D.5 | Secure-information-flow witness under fine locks | Theorem | M |
| SM8.D.6 | Lock-contention IF scenarios (5 tests) | M |

### SM8.E — Tests + closure (2 PRs, 3 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM8.E.1 | Surface anchors for ~18 SM8 theorems | `tests/SmpSurfaceAnchors.lean` | S |
| SM8.E.2 | `smp_information_flow.expected` fixture | M |
| SM8.E.3 | Update `enforcementBoundaryExtended` count 22 → 23+ | Theorem | T |

## 6. Verification strategy

### 6.1 What SM8 proves

~18 substantive theorems including:
- `onCore_isProjection_of_globalProjection`
- `nonInterference_perCore` (the headline)
- `crossCoreNonInterference`
- `enforcementBoundaryExtended_perCore`
- `acceptedCovertChannel_lockContention`
- 32 per-NI-constructor variants

### 6.2 What SM8 assumes

- SM3's serializability theorem.
- SM4 + SM5's per-core scheduler state.
- Existing R4 NI proof framework.

## 7. Risk inventory

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Per-core projection missing a field | LOW | HIGH | Field-by-field migration; SM8.A.4 independence test |
| 32 per-NI-constructor variants tedious | HIGH | LOW | Mechanical migration like SM4.C |
| `crossCoreNonInterference` proof has hole | LOW | HIGH | Theorem proved by direct application of Cor 2.1.11 |
| Lock-contention channel mitigation unclear | KNOWN | MED | Deferred to WS-W; documented |
| Cross-core declass audit trail gaps | LOW | MED | Field added to DeclassificationEvent; all writers updated |

## 8. Acceptance gate

- [ ] `ObservableState.onCore` defined and proven a projection.
- [ ] `nonInterference_perCore` proven.
- [ ] `crossCoreNonInterference` proven.
- [ ] All 32 NI constructor per-core variants proven.
- [ ] Lock-contention channel documented; boundary expanded.
- [ ] `DeclassificationEvent.originatingCore` field; audit trail updated.
- [ ] Tier 0..3 green.

## 9. Cross-references

- **Previous**: [`SMP_PER_CORE_SCHEDULER_PLAN.md`](SMP_PER_CORE_SCHEDULER_PLAN.md), [`SMP_CROSS_CORE_IPC_PLAN.md`](SMP_CROSS_CORE_IPC_PLAN.md)
- **Parallel**: [`SMP_TLB_SHOOTDOWN_PLAN.md`](SMP_TLB_SHOOTDOWN_PLAN.md)
- **Next**: [`SMP_RELEASE_CLOSURE_PLAN.md`](SMP_RELEASE_CLOSURE_PLAN.md)

## 10. Theorem catalogue for SM8

~18 substantive theorems (§6.1).

## Appendix A — Verification commands

```bash
source ~/.elan/env
lake build SeLe4n.Kernel.InformationFlow
lake build SmpInformationFlowSuite
```

---

*SM8 extends the existing NI machinery to per-core observers.
The proof leverages Cor 2.1.11: cross-core transitions don't
mutate the observer's lock-set objects, so the projection is
unchanged.*
