# SM8 — Information Flow Under SMP (WS-SM Phase 8)

> **Phase**: SM8 of WS-SM
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Audited cut**: `v0.31.2`
> **Target releases**: v0.91.0 .. v0.97.x (parallel with SM7)
> **Calendar estimate**: 5-8 weeks
> **Sub-task count**: 40-55 across ~15-22 PRs
> **Status**: SM8.A COMPLETE at v0.33.3, review cut v0.33.4 (landed
> v0.33.2); SM8.B LANDED at v0.33.5; SM8.C LANDED at v0.33.7 (with SM8.B's
> registered debt (a) closed in the same cut), completion cut v0.33.8
> (SM8.C.8 the mounted audit trail + SM8.C.9 the live `.declassify` syscall);
> SM8.D LANDED at v0.33.9 (review cuts v0.33.10 … v0.33.22, completion cut
> v0.33.11); **SM8.E LANDED at v0.33.23 — the phase is CLOSED**

## 1. Phase goal

SM8 extends the existing non-interference (NI) proofs to per-
core observers; documents the new lock-contention covert
channel; per-core declassification audit.

**Concrete deliverables**:

1. **Per-core observable state** (SM8.A): `ObservableState.onCore
   (c) (L) (s)` — projection at (core, label).
2. **Per-core NI proofs** (SM8.B): existing NI proofs generalized;
   `crossCoreNonInterference` theorem.
3. **Lock-contention covert channel**: documented as a
   5th accepted channel (existing 4 + this one).  *Delivered by SM8.B* as CC-5
   of the seven-entry inventory — this list said SM8.C, which §5's sub-task
   table (the authority) has always assigned to the declassification audit.
4. **Per-core declassification audit** (SM8.C):
   `DeclassificationEvent` extended with `originatingCore`.
5. **Information flow under fine locks** (SM8.D).
6. **Tests + closure** (SM8.E): the SM8 headline surface anchored across all five
   sub-phases, the phase-level `smp_information_flow.expected` golden trace, and
   the promotion of the two-phase-locking bracket into the canonical enforcement
   boundary.

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
5. **CC-5: Lock-contention timing** (SM8.B.8).
6. **CC-6: Per-core TLB residency** (registered at SM8.A — see below).
7. **CC-7: Per-core instruction-cache residency** (registered at SM8.A).

`enforcementBoundaryExtended` grows by one entry per channel that reaches
the enforcement boundary.

> **CC-6 / CC-7 registered at the SM8.A cut (v0.33.3).**  SM7.C and SM7.D
> mounted `SystemState.perCoreTlb` and `SystemState.perCoreICache` — two
> genuinely *per-core* views of hardware caches that did not exist when the
> CC-1…CC-4 inventory was written.  SM8.A proved both **outside the per-core
> observable state's read set** (`onCore_perCoreTlb`,
> `onCore_perCoreICache`; also `onCore_tlbShootdown`,
> `onCore_pendingIcacheMaintenance`, `onCore_tlb`), so no *model-level* flow
> exists through them.
>
> That is exactly the CC-2 situation, and it warrants the same treatment.
> The machine timer is likewise excluded from `ObservableState`, and is
> nonetheless a registered accepted channel because the exclusion is a
> statement about the *model*, not about the hardware: a real observer
> measures TLB and instruction-cache residency by timing its own accesses,
> and that measurement is not something a kernel-level projection can
> deny it.  Under SMP each core carries its own view, so — like CC-1 —
> the channel exists **once per core**.
>
> Scope: SM8.A registers them; SM8.B.8 gives them the formal
> `CovertChannel` treatment alongside CC-5, and SM8.E.3 settled the
> resulting `enforcementBoundaryExtended` count at **40** (the 2PL bracket
> promoted in; the residency channels add no boundary entry, since neither
> is an operation whose authority the kernel derives).  Mitigation is the same
> class as CC-2's — hardware partitioning (CCA/MPAM), deferred to WS-W.
> Recording them here rather than in a source docstring is deliberate:
> a channel that lives only in a comment ages out with the code around it.

> **Count re-anchored at the SM8.A cut.**  The "22 entries
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

**Accepted is not unbounded** (SM8.D, v0.33.9).  `lockContention_delay_bounded`
composes the SM2.C wait-depth cap with the admission-step bound to give a
contending core's observation a ceiling of `(numCores - 1) × (maxDelay + 1)`
steps, and `lockContentionChannel_alphabet_bounded` /
`lockContentionChannel_trace_capacity` turn that into a per-acquisition alphabet
a pacing bound (`lockContentionChannel_observation_rate_bounded` — distinct
acquisitions have distinct enqueue steps, so a core cannot observe more often
than the execution has steps) and a run capacity: the same three-part shape §5
SM8.B.9 gave CC-1.  The bound is **conditional on the SM2.C `FairTrace`
assumption**, which nothing in the kernel establishes —
`lockContention_unbounded_without_fairness` is the execution that makes the
premise load-bearing.  `lockContentionChannel_two_codes_reachable`
is the standing negative — two fair, in-premise executions in which the *same*
contending core reads different codes, so the bound never claims the channel is
closed, which is why it stays *accepted* rather than discharged.  The ceiling is
in **lock operations**; `lockContention_wallClock_bounded` is the timing reading
and carries a per-critical-section bound as an explicit hypothesis.

### 4.3 Why `DeclassificationEvent.originatingCore`

When a thread on c₁ declassifies state observed on c₂ (e.g., via
cross-core IPC), the audit trail must record the originating
core. The field's added; the audit invariant preserved.

## 5. Detailed sub-task breakdown

### SM8.A — Per-core observable state (1 PR by decision, 6 sub-tasks) — **LANDED v0.33.2, COMPLETE v0.33.3, REVIEW CUT v0.33.4**

| Sub | Description | Theorem | Est | Status |
|-----|-------------|---------|-----|--------|
| SM8.A.1 | `ObservableState.onCore (c, L, s)` | (def) | M | LANDED |
| SM8.A.2 | `onCore_isProjection_of_globalProjection` | Theorem | M | LANDED |
| SM8.A.3 | `onCore_decidable` | Instance | S | LANDED |
| SM8.A.4 | `onCore_perCore_independence` | Theorem | M | LANDED |
| SM8.A.5 | `onCore_label_monotone` | Theorem | M | LANDED |
| SM8.A.6 | Start `tests/SmpInformationFlowSuite.lean` | M | LANDED |

*Landed. What each cut changed, and what its review rounds found, is in
[`CHANGELOG.md`](../../CHANGELOG.md) under the versions above.*

### SM8.B — Per-core NI proofs (14 sub-tasks)

> **Constructor count re-anchored at the SM8.A cut (v0.33.2).**  This
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
| Sub | Description | Theorem | Est | Status |
|-----|-------------|---------|-----|--------|
| SM8.B.1 | `nonInterference_perCore` (existing NI generalized) | Theorem | XL | LANDED |
| SM8.B.2 | `crossCoreNonInterference` (Thm 3.3.1) | Theorem | XL | LANDED |
| SM8.B.3 | Per-core NI for each of the 35 `kernelOperationNi` constructors (re-anchored at SM8.A — see note above) | 35 theorems | L | LANDED |
| SM8.B.4 | NI under per-object lock-set | Theorem | L | LANDED |
| SM8.B.5 | `niStepCoverage_perCore` | Theorem | M | LANDED |
| SM8.B.6 | `enforcementBoundaryPerCore` (54 entries — re-anchored) | Definition + theorem | M | LANDED |
| SM8.B.7 | Boundary completeness witness | Theorem | M | LANDED |
| SM8.B.8 | `acceptedCovertChannel_lockContention` | Definition | M | LANDED |
| SM8.B.9 | Mitigation note (WS-W partitioning) | Documentation | S | LANDED |
| SM8.B.10 | `acceptedCovertChannel_perCoreCount = 7` (re-anchored) | Theorem | T | LANDED |
| SM8.B.11 | `endpointPolicyRestricted_perCore` | Theorem | M | LANDED |
| SM8.B.12 | Per-core NI bridge to NI release | Theorem | M | LANDED |
| SM8.B.13 | `crossCoreLeakage_bounded` | Theorem | L | LANDED |
| SM8.B.14 | 15+ NI scenarios (tests) | L | LANDED |

*Landed. What each cut changed, and what its review rounds found, is in
[`CHANGELOG.md`](../../CHANGELOG.md) under the versions above.*

### SM8.C — Per-core declassification audit (7 sub-tasks, + 2 added) — **LANDED v0.33.7; COMPLETE v0.33.8**

| Sub | Description | Theorem | Est | Status |
|-----|-------------|---------|-----|--------|
| SM8.C.1 | `DeclassificationEvent.originatingCore : CoreId` extension | Structure | M | LANDED |
| SM8.C.2 | Cross-core declassification chains in audit trail | Theorem | M | LANDED |
| SM8.C.3 | Every declass event has valid originatingCore | Theorem | S | LANDED |
| SM8.C.4 | `DeclassificationEvent_perCore_audit` | Theorem | M | LANDED |
| SM8.C.5 | `authorizationBasis_perCore` extending V6-H | Theorem | M | LANDED |
| SM8.C.6 | Cross-core declass rules | Theorem | M | LANDED |
| SM8.C.7 | Per-core declass test scenarios | M | LANDED |
| SM8.C.8 | Mount the audit trail in `SystemState`, bounded and fail-closed | Structure | M | LANDED v0.33.8 |
| SM8.C.9 | The live `.declassify` syscall | ABI + Theorem | L | LANDED v0.33.8 |

*Landed. What each cut changed, and what its review rounds found, is in
[`CHANGELOG.md`](../../CHANGELOG.md) under the versions above.*

### SM8.D — Information flow under fine locks (6 sub-tasks) — **LANDED v0.33.9, review cut v0.33.10**

| Sub | Description | Theorem | Est | Status |
|-----|-------------|---------|-----|--------|
| SM8.D.1 | Lock state visibility documented | docstring → **Theorem** | M | LANDED |
| SM8.D.2 | Reader-multiplicity not directly observable | Theorem | M | LANDED |
| SM8.D.3 | Writer-exclusion observable to blocked readers | docstring → **refuted + bounded** | T | LANDED |
| SM8.D.4 | Biba-integrity under per-core locks | Theorem | M | LANDED |
| SM8.D.5 | Secure-information-flow witness under fine locks | Theorem | M | LANDED |
| SM8.D.6 | Lock-contention IF scenarios (5 tests) | M | LANDED (7 groups) |

*Landed. What each cut changed, and what its review rounds found, is in
[`CHANGELOG.md`](../../CHANGELOG.md) under the versions above.*

### SM8.E — Tests + closure (3 sub-tasks) — **LANDED v0.33.23**

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM8.E.1 | Surface anchors for ~18 SM8 theorems | `tests/SmpSurfaceAnchors.lean` | S |
| SM8.E.2 | `smp_information_flow.expected` fixture | M |
| SM8.E.3 | Update `enforcementBoundaryExtended` count 39 → 40 for the `withLockSet` bracket (SM8.C's completion cut already took 38 → 39 for `declassifyObjectFromCore`, so this row is now the lock-bracket entry alone) | Theorem | T |

*Landed. What each cut changed, and what its review rounds found, is in
[`CHANGELOG.md`](../../CHANGELOG.md) under the versions above.*

## 6. Verification strategy

### 6.1 What SM8 proves

~18 substantive theorems including:
- `onCore_isProjection_of_globalProjection`
- `nonInterference_perCore` (the headline)
- `crossCoreNonInterference`
- `enforcementBoundaryPerCore_count` + `enforcementBoundaryExtended_count`
  (the plan wrote `enforcementBoundaryExtended_perCore`, which never existed —
  corrected at SM8.E.1, where every name on this list had to resolve)
- `acceptedCovertChannel_lockContention`
- 35 per-NI-constructor variants (re-anchored — see §5 SM8.B)
- `declassifyStoreOnCore_never_unaudited` +
  `authorizeDeclassificationOnCore_denied_before_capacity` +
  `crossCoreChain_not_within_one_view` (SM8.C)
- `projectKernelObject_setLock` + `lockWritesOnly_preserves_onCore` (SM8.D.1)
- `lockContention_delay_bounded` + `lockContentionChannel_alphabet_bounded` (SM8.D.3)
- `bibaIntegrity_underLockSet` + `authorityIntegrity_underLockSet` (SM8.D.4)
- `secureInformationFlow_underFineLocks` (SM8.D.5)

**Every name on this list resolves in `tests/SmpSurfaceAnchors.lean` §8**
(SM8.E.1).  That is the list's job: a "what the phase proves" enumeration whose
entries are not anchored anywhere is prose, and this one had drifted — one name
never existed, SM8.C contributed none, and two of the SM8.D names were
unanchored.

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
| Lock-contention channel mitigation unclear | KNOWN | MED | Mitigation still deferred to WS-W, but the channel is no longer merely *documented*: SM8.D (v0.33.9) proves it carries no model-level flow (`onCore_lock_indistinguishable`) and **bounds** the timing it does carry (`lockContention_delay_bounded` → `lockContentionChannel_alphabet_bounded` → `lockContentionChannel_trace_capacity`), with `lockContentionChannel_two_codes_reachable` the standing negative that it is bounded rather than closed, and the bound denominated in lock operations (`lockContention_wallClock_bounded` for the timing reading) |
| Cross-core declass audit trail gaps | LOW | MED | DISCHARGED at SM8.C (v0.33.7).  The risk was understated: there were no writers to update — nothing constructed a `DeclassificationEvent`.  Closed by building the producer (`declassifyStoreOnCore`) and the attributed entry point (`declassifyStoreFromCore`), with `crossCoreChain_not_within_one_view` the theorem that decides one global log over per-core logs |

## 8. Acceptance gate

- [x] `ObservableState.onCore` defined and proven a projection (SM8.A,
      v0.33.2 / v0.33.3 — `onCore_isProjection_of_globalProjection` as an
      exact `iff` against `observableFactorOnCore`, with the field partition
      established as a *bijection* by `ObservableState.ofFragments` +
      `ofFragments_eta`).
- [x] `nonInterference_perCore` proven (SM8.B, v0.33.5 — with the confinement
      premise *derived* for thirty-one of the thirty-five operations, which also
      discharges the SM4.C / SM4.D `hOtherIdle` obligation for them).
- [x] `crossCoreNonInterference` proven (SM8.B, v0.33.5 — from the frame
      premises rather than from serializability, which SM3.C.9 still defers;
      `crossCoreNonInterference_of_disjoint_lockSet` is the bridge that makes
      the plan's own argument a corollary once the fine locks go live).
- [x] All 35 NI constructor per-core variants proven (SM8.B, v0.33.5; count
      re-anchored at SM8.A — `kernelOperation_count` / `niStepCoverage_count`
      are the authority, and `niStepCoverage_perCore_count` matches them).
- [x] Lock-contention channel documented; boundary expanded (SM8.B, v0.33.5 —
      CC-5 registered with `withLockSet_preserves_projection` as its witness,
      which required erasing the per-object `lock` from the projection;
      `enforcementBoundaryPerCore` at **54** entries —
      `enforcementBoundaryPerCore_count` is the authority, so read the figure
      there rather than here; the *canonical* list's separate promotion was
      SM8.E.3's, landed at v0.33.23 and taking it 39 → 40.  This item said 39
      until PR #861 review round 30, which conflated the two lists: the
      canonical boundary is the one SM8.E.3 moved, not the per-core one, whose
      total is unchanged because the bracket only changed which of the two
      definitions holds it.)
- [x] `DeclassificationEvent.originatingCore` field; audit trail updated
      (SM8.C, v0.33.7 — the field is *undefaulted*, and the audit trail was not
      merely "updated": before this cut nothing in the tree constructed a
      `DeclassificationEvent` at all, so the producer `declassifyStoreOnCore`
      and the attributed entry point `declassifyStoreFromCore` are the closure).
- [x] Lock-state visibility settled as a **theorem** rather than a docstring, and
      the plan's D.3 row refuted at the model level rather than reinstated
      (SM8.D, v0.33.9 — `projectKernelObject_setLock` is the factoring,
      `blockedAcquirer_observes_nothing` the refutation).
- [x] The lock-contention channel **bounded**, not only registered (SM8.D,
      v0.33.9 — `lockContention_delay_bounded` /
      `lockContentionChannel_alphabet_bounded` /
      `lockContentionChannel_trace_capacity`), at **every** contending access
      mode (v0.33.11 — `blockedReaderContention_delay_bounded` over the
      mode-generic SM2.C-defer D-3.10 liveness chain).
- [x] Biba integrity under per-core locks proven in **both** integrity
      directions (SM8.D, v0.33.9 — `writeRules_differ` is why that is two
      results and not one restated).
- [x] Secure-information-flow witness for a 2PL-bracketed live syscall entry,
      with the fail-closed statement sharpened from state equality to
      `lockWritesOnly` (SM8.D, v0.33.9).
- [x] Every theorem §6.1 names anchored in `tests/SmpSurfaceAnchors.lean`, across
      all five sub-phases (SM8.E.1, v0.33.23 — SM8.C had no anchors there at all,
      and the CC-5 alphabet / trace-capacity pair was unanchored).
- [x] `smp_information_flow.expected` — the phase-level golden trace, computed
      from the live projection, transitions and inventories, verified
      byte-for-byte in-suite and hash-gated by Tier 2 (SM8.E.2, v0.33.23).
- [x] `enforcementBoundaryExtended` 39 → 40: the 2PL bracket promoted into the
      canonical boundary, classified exactly once, with the per-core list
      unchanged at 55 (SM8.E.3, v0.33.23 — `enforcementBoundaryExtended_count`
      and `enforcementBoundaryPerCore_classifies_withLockSet_once` are the
      authorities).
- [x] Tier 0..3 green.

## 9. Cross-references

- **Previous**: [`SMP_PER_CORE_SCHEDULER_PLAN.md`](SMP_PER_CORE_SCHEDULER_PLAN.md), [`SMP_CROSS_CORE_IPC_PLAN.md`](SMP_CROSS_CORE_IPC_PLAN.md)
- **Parallel**: [`SMP_TLB_SHOOTDOWN_PLAN.md`](SMP_TLB_SHOOTDOWN_PLAN.md)
- **Next**: [`SMP_RELEASE_CLOSURE_PLAN.md`](SMP_RELEASE_CLOSURE_PLAN.md)

## 10. Theorem catalogue for SM8

~18 substantive theorems (§6.1).  Landed so far: SM8.A's five headline
theorems (§5 SM8.A landing record) and SM8.B's `crossCoreNonInterference`,
`nonInterference_perCore`, the 35 per-operation lifts, `niStepCoverage_perCore`,
`withLockSet_preserves_projection` / `nonInterference_perCore_underLockSet`,
`enforcementBoundaryPerCore` + its completeness witness,
`acceptedCovertChannel_lockContention` (CC-5) with the seven-entry inventory,
`endpointPolicyRestricted_perCore`, the release bridge, and
`crossCoreLeakage_bounded`.  SM8.C adds `declassifyStoreOnCore` +
`declassifyStoreOnCore_ok_inv` / `…_records_one`, `declassifyStoreFromCore` +
`declassifyStoreFromCore_event_attributable` (with the negative
`declassifyStoreOnCore_admits_unattributable`),
`declassificationAuditLog_partitions_by_core` +
`DeclassificationEvent_perCore_audit`,
`declassificationChain_recorded_across_cores` +
`crossCoreChain_not_within_one_view`,
`declassificationChain_hop_authorization_does_not_compose` + `chainLaunders`,
`endpointOverride_is_not_a_declassification_basis` and its live, hypothesis-free
form `liveEndpointOverride_is_not_a_declassification_basis`,
`authorizationBasis_perCore`, `declassifyStoreOnCore_perCore_NI`,
`declassifyStoreOnCore_state_log_independent`, and the eight-rule inventory with
its dependently-typed `declassificationRuleEvidence`; plus, from the debt (a)
closure, `endpointFlowGate` with `endpointFlowGate_implies_securityFlowsTo`,
`endpointFlowGate_eq_securityFlowsTo_of_no_override` and the non-vacuity witness
`endpointFlowGate_is_not_securityFlowsTo`.  SM8.D adds
`KernelObject.setLock` / `eraseLock` with the factoring `projectKernelObject_setLock`,
`lockWritesOnly` + `lockWritesOnly_preserves_onCore` and the acquire / release /
fold / bracket instances, `onCore_lock_indistinguishable`,
`readerMultiplicity_not_observable` (+ the reachable-witness form),
`writerExclusion_not_observable` and `blockedAcquirer_observes_nothing`,
`lockContention_delay_bounded` + `lockContentionChannel_alphabet_bounded` +
`lockContentionChannel_trace_capacity` + `lockContentionCode_injective`,
`writeRules_differ` + `lockWrite_carries_no_subject_data` +
`bibaIntegrity_underLockSet` / `authorityIntegrity_underLockSet` +
`lockPhases_integrity_clean_on_every_core`, and
`syscallEntryChecked_preserves_projection` +
`syscallEntryUnderLockSet_preserves_projectionOnCore` +
`syscallEntryUnderLockSet_failClosed{,_invisible}` +
`secureInformationFlow_underFineLocks` +
`suspendUnderDeclaredLockSet_preserves_projectionOnCore`, with the eleven-claim
`FineLockClaimId` inventory and its dependently-typed evidence
(`fineLockClaims_count` is the authority; the figure grew across the review
cuts).  SM8.E adds `enforcementBoundary_classifies_withLockSet`,
`enforcementBoundaryPerCore_classifies_withLockSet_once` and
`crossCoreEnforcementEntries_omits_withLockSet` — the three that survive the
retired `enforcementBoundaryPerCore_entry_is_new` — and, as the substrate the
phase-level fixture computes from, `KernelOperation.all` with
`KernelOperation.mem_all` / `all_nodup` and the three counts restated against
them (`kernelOperation_count`, `perCoreConfinementDerived_count`,
`perCoreConfinementNotDerived_count`, `niStepCoverage_perCore_count`).

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
