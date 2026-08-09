# SM8 — Information Flow Under SMP (WS-SM Phase 8)

> **Phase**: SM8 of WS-SM
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Audited cut**: `v0.31.2`
> **Target releases**: v0.91.0 .. v0.97.x (parallel with SM7)
> **Calendar estimate**: 5-8 weeks
> **Sub-task count**: 40-55 across ~15-22 PRs
> **Status**: SM8.A LANDED at v0.33.1; SM8.B–SM8.E pending

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

`enforcementBoundaryExtended` grows by one entry.

> **Count re-anchored at the SM8.A cut (v0.33.1).**  The "22 entries
> (V6-L)" figure above was written against the `v0.31.2` audited cut.
> The live surface is **38** (`enforcementBoundaryExtended_count`,
> `Enforcement/Soundness.lean`), so SM8 takes it 38 → 39.  Asserting the
> plan's original number in a closure cut would have produced a *false*
> `rfl`; re-anchor against the theorem, not against this document.

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

### SM8.A — Per-core observable state (3 PRs, 6 sub-tasks) — **LANDED v0.33.1**

| Sub | Description | Theorem | Est | Status |
|-----|-------------|---------|-----|--------|
| SM8.A.1 | `ObservableState.onCore (c, L, s)` | (def) | M | LANDED |
| SM8.A.2 | `onCore_isProjection_of_globalProjection` | Theorem | M | LANDED |
| SM8.A.3 | `onCore_decidable` | Instance | S | LANDED |
| SM8.A.4 | `onCore_perCore_independence` | Theorem | M | LANDED |
| SM8.A.5 | `onCore_label_monotone` | Theorem | M | LANDED |
| SM8.A.6 | Start `tests/SmpInformationFlowSuite.lean` | M | LANDED |

**Landing record (v0.33.1).** New staged module
`SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean` (staged-only
count 54 → 55; SM8.B's `crossCoreNonInterference` is the first consumer),
layered on the SM4.D per-core projections in `ProjectionPerCore.lean`.
Zero `sorry`/`axiom`; every theorem depends only on `propext` /
`Quot.sound` / `Classical.choice`.  No transition changed, so the golden
trace is byte-identical.

* **SM8.A.1** — `PerCoreObserver` makes the `(c, L)` pair of Definition
  3.1.1 a value rather than a convention spread over two argument
  positions, and `ObservableState.onCore ctx c L s` is Definition 3.2.1.
  It is *defined as* `projectStateOnCore ctx ⟨L⟩ s c` rather than as a
  second structure literal, so the SM8 observer and the SM4.D projection
  layer cannot drift; `onCore_bootCore` is therefore `rfl` and connects
  every SM8 theorem instantiated at `bootCoreId` to the live single-core
  `projectState`.  `lowEquivalentForObserver` + the
  `lowEquivalent_smp_iff_forall_observer` bridge give SM8.B its substrate:
  the SM6 cross-core NI theorems already stated in `lowEquivalent_smp`
  form are, definitionally, statements about all per-core observers.
* **SM8.A.2** — the thirteen `ObservableState` components partition into
  seven shared and six per-core (`SharedObservableFragment` /
  `PerCoreObservableFragment`).  **The partition is total by
  construction**: `ObservableState.ext_fragments` rebuilds an observable
  state from its two fragments, so a fourteenth field registered in
  neither leaves that theorem unprovable — the §7 risk "per-core
  projection missing a field" becomes a build error rather than a review
  checklist item.  The headline `onCore_isProjection_of_globalProjection`
  states the factoring (the per-core observer learns exactly the global
  projection plus core `c`'s six slots);
  `onCore_sharedFragment_determined_by_globalProjection` is the
  information-content form, and `onCore_sharedFragment_core_independent`
  is the orthogonality of the two observer dimensions.  Thirteen `@[simp]`
  component accessors are the working form.
* **SM8.A.3** — observable-state equality is **not** decidable: five
  components are functions over unbounded domains and `machineRegs`
  carries a `RegisterFile` whose structural `BEq` is provably not lawful
  (`RegisterFile.not_lawfulBEq`).  The `onCore_decidable` instance decides
  `lowEquivalentSliceOnCore`, a deliberately distinct relation over the
  `PerCoreObservableSlice` (the five `DecidableEq` per-core scheduler
  components plus the register bank's *observability*).  Both halves of
  the limitation ship as theorems:
  `lowEquivalentSliceOnCore_of_lowEquivalentOnCore` (equal views ⇒ equal
  slices, so a decided mismatch is a genuine observable difference) and
  `perCoreSlice_erases_register_content` /
  `perCoreSlice_erases_shared_content` (the converse fails, on both halves
  of the SM8.A.2 partition), so no caller can mistake the decision
  procedure for a decision about the observable state.
* **SM8.A.4** — `onCore_perCore_independence` characterises the read set:
  six shared state components plus core `c`'s five scheduler slots and its
  register bank, and nothing else.  This does **not** follow from the
  SM4.D `projectStateOnCore_congr`, whose `hBase` hypothesis is equality
  of the whole *global* projection and therefore reads the **boot** core's
  slots; a cross-core transition on core `c'` generally breaks it when
  `c' = bootCoreId`, which is exactly the case SM8.B must reason about.
  Twelve corollaries instantiate it against the SM4.B per-core store/load
  algebra: the six per-core scheduler setters and `setRegsOnCore` at
  `c ≠ c'`, plus the components outside the read set entirely
  (replenishment queue, timeout log, `scThreadIndex`, the machine timer,
  the SM7.C `perCoreTlb` view) — invisible on *every* core, including the
  one written.  `onCore_machineTimer` is the per-core restatement of the
  `ObservableState` timer exclusion: under SMP the exclusion has to hold
  on each core separately.
* **SM8.A.5** — `onCore_label_monotone` over the new
  `ObservableState.visibilityLe` preorder, proved gate by gate from
  `securityFlowsTo_trans`.  Deliberately a *visibility* order rather than
  component equality: a wider clearance may legitimately reveal more of an
  object it can already see, which `projectCNode_lookup_monotone` makes
  precise (a CNode slot visible at the narrower clearance survives at the
  wider one) and `projectKernelObject_observer_independent_off_cnode`
  bounds (the CNode arm is the only one that reads the observer at all).
  The four scheduling components are label-*invariant*:
  `onCore_schedulingTransparency` restates accepted covert channel CC-1
  per core, which under SMP means one copy of the channel per core.
  Substrate: the RobinHood filter-lookup characterisation was only
  half-stated (`filter_get_subset` + `filter_get_pred` give the
  left-to-right direction), so a monotone predicate change could not be
  transported through a filter; `RHTable.filter_getElem?_of_pred` supplies
  the forward direction and `RHTable.filter_getElem?_iff` states the
  characterisation as the `iff`.
* **SM8.A.6** — `tests/SmpInformationFlowSuite.lean`
  (`smp_information_flow_suite`): 83 `#check` surface anchors, 15
  elaboration-time examples, and **68 runtime assertions across 8 groups**
  on a four-thread / four-core fixture under a non-trivial labeling (core
  0 runs low threads, core 1 runs high ones; low and high endpoints,
  services and IRQ handlers shared).  §3.0 is a fixture non-vacuity gate
  so no later group can pass on an empty state.  Every group carries a
  load-bearing negative: §3.4 shows the *same* write applied to the
  observer's own core does change its view (so the `c ≠ c'` hypothesis is
  necessary, not decorative), §3.5 shows the high observer strictly
  outsees the low one on six separate components (so monotonicity is not
  equality in disguise), §3.6 shows two cores reporting different active
  domains (so CC-1 really is per core), and §3.7 shows a purely high
  remote reshuffle invisible to the low observer on every core while the
  high observer's own view does move.  Tier-2 (`test_tier2_negative.sh`)
  and Tier-3 (surface anchors, including the negative anchors for the
  strictness witnesses) wired; fixture OID band 1000–1013 registered in
  `SeLe4n/Testing/Helpers.lean`.

**Deliberately not in SM8.A** (each is a later sub-phase, not an
omission): the per-core NI *preservation* theorems over transitions are
SM8.B; the lock-contention channel CC-5 is SM8.B.8; the
`DeclassificationEvent.originatingCore` extension is SM8.C.

### SM8.B — Per-core NI proofs (5 PRs, 14 sub-tasks)

> **Constructor count re-anchored at the SM8.A cut (v0.33.1).**  This
> phase was scoped against a 32-constructor NI surface at the `v0.31.2`
> audited cut.  The live surface is **35**: `KernelOperation` has 35
> variants (`kernelOperation_count`) and `kernelOperationNiConstructor`
> maps them to 35 distinct names (`niStepCoverage_count`,
> `niStepCoverage_injective`), with `niStepConstructorCoverage` an
> exhaustive match that makes a missed variant a compile error.  SM8.B.3
> must cover all 35: building to the plan's original 32 would leave three
> constructors without a per-core lift, and the exhaustive-match
> tripwire only fires on a *new* variant, not on a per-core lift that
> stops short.  Scope against the theorems, not against this document.

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM8.B.1 | `nonInterference_perCore` (existing NI generalized) | Theorem | XL |
| SM8.B.2 | `crossCoreNonInterference` (Thm 3.3.1) | Theorem | XL |
| SM8.B.3 | Per-core NI for each of the 35 `kernelOperationNi` constructors (re-anchored at SM8.A — see note below) | 35 theorems | L |
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
| SM8.E.3 | Update `enforcementBoundaryExtended` count 38 → 39 (re-anchored at SM8.A) | Theorem | T |

## 6. Verification strategy

### 6.1 What SM8 proves

~18 substantive theorems including:
- `onCore_isProjection_of_globalProjection`
- `nonInterference_perCore` (the headline)
- `crossCoreNonInterference`
- `enforcementBoundaryExtended_perCore`
- `acceptedCovertChannel_lockContention`
- 35 per-NI-constructor variants (re-anchored — see §5 SM8.B)

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

- [x] `ObservableState.onCore` defined and proven a projection (SM8.A,
      v0.33.1 — `onCore_isProjection_of_globalProjection`, with the field
      partition made total by `ObservableState.ext_fragments`).
- [ ] `nonInterference_perCore` proven.
- [ ] `crossCoreNonInterference` proven.
- [ ] All 35 NI constructor per-core variants proven (count re-anchored at SM8.A; `kernelOperation_count` / `niStepCoverage_count` are the authority).
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
