# SM8 — Information Flow Under SMP (WS-SM Phase 8)

> **Phase**: SM8 of WS-SM
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Audited cut**: `v0.31.2`
> **Target releases**: v0.91.0 .. v0.97.x (parallel with SM7)
> **Calendar estimate**: 5-8 weeks
> **Sub-task count**: 40-55 across ~15-22 PRs
> **Status**: SM8.A COMPLETE at v0.33.3, review cut v0.33.4 (landed
> v0.33.2); SM8.B LANDED at v0.33.5; SM8.C–SM8.E pending

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
> `CovertChannel` treatment alongside CC-5, and SM8.E.3 settles the
> resulting `enforcementBoundaryExtended` count.  Mitigation is the same
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

**Landing record (v0.33.2, completed v0.33.3, review cut v0.33.4).**  New
staged module `SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean` (119
declarations; staged-only count 54 → 55; SM8.B's `crossCoreNonInterference`
is the first consumer), layered on the SM4.D per-core projections in
`ProjectionPerCore.lean`.  Zero `sorry`/`axiom` — of the module's
119 declarations, the 113 term-level ones each depend only on `propext` /
`Quot.sound` / `Classical.choice` (checked exhaustively, not by sampling);
the remaining 6 are structures.  No
transition changed, so the golden trace is byte-identical.

*Delivered as one PR rather than the three this table projected — the
slicing was for reviewability and the phase is a single coherent layer
(observer, partition, decidability, independence, monotonicity) whose
parts do not stand alone.*

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
  `PerCoreObservableFragment`).  **The partition is a bijection**:
  `ObservableState.ofFragments` reassembles a state from the pair and
  `ofFragments_eta` proves the round trip, so the "a fourteenth field is a
  compile error" property is a *checked fact* rather than an argument — a
  new component leaves `ofFragments` unable to supply it.  `ext_fragments`
  and `fragments_injective` are the determination half.  The headline
  `onCore_isProjection_of_globalProjection` is an **`iff`**: two states are
  indistinguishable to `(c, L)` exactly when they agree on
  `observableFactorOnCore` — the global projection's shared fragment paired
  with core `c`'s per-core fragment.  Both directions carry weight; `←` is
  the one the SM4.D congruence could not give, since it needs the partition
  to be total.  (`onCore_congr_of_globalProjection` keeps the state-level
  convenience form.)  Plus `onCore_sharedFragment_core_independent` (the
  orthogonality of the two observer dimensions) and thirteen `@[simp]`
  component accessors.
* **SM8.A.3** — observable-state equality is **not** decidable: five
  components are functions over unbounded domains and `machineRegs`
  carries a `RegisterFile` whose structural `BEq` is provably not lawful
  (`RegisterFile.not_lawfulBEq`).  The `onCore_decidable` instance decides
  `lowEquivalentSliceOnCore`, a deliberately distinct relation over the
  `PerCoreObservableSlice`.  A **finer** register-aware check
  (`lowEquivalentSliceOnCoreCheckWithRegs`) carries the ARM64 structural
  comparison of `pc` / `sp` / the 32 GPRs, so the decidable surface is as
  informative as computation allows.  Every limitation is a theorem, not a
  comment: `lowEquivalentSliceOnCore_of_lowEquivalentOnCore` and
  `…CheckWithRegs_of_lowEquivalentOnCore` (sound refuters),
  `…CheckWithRegs_le_slice` (the refinement),
  `perCoreSlice_erases_register_content` / `_shared_content` and
  `machineRegs_beq_not_injective` (both checks are *strict*, on both halves
  of the partition and on the register content).
* **SM8.A.4** — `onCore_perCore_independence` characterises the read set:
  six shared state components plus core `c`'s five scheduler slots and its
  register bank, and nothing else.  This does **not** follow from the
  SM4.D `projectStateOnCore_congr`, whose hypothesis is equality of the
  whole *global* projection and therefore reads the **boot** core's slots;
  a cross-core transition on core `c'` generally breaks it when
  `c' = bootCoreId`, which is exactly the case SM8.B must reason about.
  **Fifteen** corollaries instantiate it against the SM4.B per-core
  store/load algebra: six for the per-core scheduler setters and
  `setRegsOnCore` at `c ≠ c'`, and nine for state outside the read set
  entirely — the replenishment queue, the timeout log, `scThreadIndex`,
  the machine timer, and the whole SM7 memory-subsystem surface
  (`perCoreTlb`, `perCoreICache`, `pendingIcacheMaintenance`,
  `tlbShootdown`, the scalar `tlb`) — invisible on *every* core, including
  the one written.  `onCore_machineTimer` is the per-core restatement of
  the `ObservableState` timer exclusion: under SMP it has to hold on each
  core separately.
* **SM8.A.5** — `onCore_label_monotone` over the new
  `ObservableState.visibilityLe` preorder, proved gate by gate from
  `securityFlowsTo_trans`, with `onCore_label_monotone_smp` /
  `visibilityLe_smp` the ∀-core aggregate in the SM4.D idiom.  Every clause
  is as strong as the truth allows: the two list components are compared by
  **`List.Sublist`**, not membership — both are filters of the *same*
  underlying list, so order is preserved, and a run queue's order is its
  dispatch order (`filter_sublist_filter_of_imp` is the substrate;
  `visibilityLe_mem_runnable` / `_mem_objectIndex` derive the membership
  forms so nothing is lost).  `objects` is the one component whose *content*
  may widen, and it is compared by `objectVisibilityLe`, which pins that
  widening exactly: equality on every arm but `.cnode` (which is what
  `projectKernelObject_observer_independent_off_cnode` makes true — CNode
  redaction is the *only* observer-dependent part of object projection), and
  `cnodeVisibilityLe` on the CNode arm, where the five non-slot fields are
  fixed and slots may only be un-redacted.  `eq_of_objectVisibilityLe_of_not_cnode`
  and `ObservableState.visibilityLe_{objects_eq_of_not_cnode,cnode_lookup}` are
  the consumer forms, derivable from a `visibilityLe` hypothesis with no access
  to the underlying state — as is `visibilityLe_objects_isSome`, the weakest.
  The four scheduling components are **unfiltered** (CC-1), so their clauses are
  equality; `ObservableState.eq_of_visibilityLe_antisymm` is the completeness
  check on the whole clause list (mutual domination plus agreement on `objects`
  is equality, so a fourteenth component with no clause leaves a goal nothing
  can close).  The state-level forms
  `onCore_objects_label_invariant_off_cnode`, `onCore_objects_cnode` and
  `onCore_objects_cnode_slot_monotone` remain as the two-projections-of-one-state
  statements, and `projectCNode_visibilityLe_monotone` /
  `projectKernelObject_visibilityLe_monotone` are the bridges that discharge the
  `objects` clause.
  `onCore_schedulingTransparency` states CC-1 against the **raw** scheduler
  reads — what the observer gets, not merely that two clearances agree,
  which any constant function satisfies — with
  `_label_invariant` the two-observer corollary.  Substrate: the RobinHood
  filter-lookup characterisation was only half-stated
  (`filter_get_subset` + `filter_get_pred` give one direction), so a
  monotone predicate change could not be transported through a filter;
  `RHTable.filter_getElem?_of_pred` supplies the forward direction and
  `RHTable.filter_getElem?_iff` states the characterisation as the `iff`.
* **SM8.A.6** — `tests/SmpInformationFlowSuite.lean`
  (`smp_information_flow_suite`): **123 `#check` surface anchors** (every
  one of the module's 119 declarations, verified by set difference), 25
  elaboration-time examples, and **125 runtime assertions across 14
  groups**.  The fixture is four threads on four cores under a
  three-clearance labeling `low ⊏ mid ⊏ high`, with low/mid/high endpoints,
  low/high services and IRQ handlers, a **CNode carrying one low-target and
  one high-target capability**, and a **configured memory-ownership model**
  — the last two exist so that CNode slot redaction and
  `memoryAddressObservable` are exercised on real values rather than
  vacuously.  §3.0 is a fixture non-vacuity gate.  Every group carries a
  load-bearing negative: §3.4 the same write on the observer's own core
  *does* change its view; §3.5 the high observer strictly outsees the low
  one on six components; §3.6 two cores report different active domains;
  §3.7 a purely high remote reshuffle is invisible to low on every core
  while high's own view moves; §3.8 the low observer is denied the
  high-target CNode slot the high observer gets, end-to-end through the
  observable state; §3.9 the same address is observable under the ownership
  model and to nobody without it; §3.11 the middle clearance sees strictly
  more than low and strictly less than high; §3.12 the finer check rejects
  a register difference the coarse slice accepts.  Tier-2
  (`test_tier2_negative.sh`) and Tier-3 wired — the Tier-3 block pins
  **every** module symbol including the `@[simp]` definition-pinning layer,
  verified by set difference — with headline anchors additionally in
  `tests/SmpSurfaceAnchors.lean`, the file §5 SM8.E.1 names as the SM8
  anchor home.  Fixture OID band 1000–1019 registered in
  `SeLe4n/Testing/Helpers.lean`.

**Review cut (v0.33.4).**  Three findings from the automated review of the
SM8.A pull request, all valid, all closed.  Two concern
`ObservableState.visibilityLe`, whose docstring claimed every clause was "as
strong as the truth allows" while two were not — the project's
implement-the-improvement case, so the relation was strengthened rather than
the claim weakened.

1. **The `objects` clause preserved only `isSome`** (P1).  A consumer holding
   `v₁.visibilityLe v₂` could conclude an object was still *present*, not that
   it was the same object: the relation admitted replacing a visible endpoint,
   TCB or Reply with an unrelated object at the same id, which is the opposite
   of "a wider clearance sees at least as much".  The state-level lemmas that
   bound the widening (`onCore_objects_label_invariant_off_cnode`,
   `onCore_objects_cnode_slot_monotone`) did not help, since neither follows
   from a `visibilityLe` hypothesis alone.  Closed by comparing content:
   `objectVisibilityLe` is equality on every arm but `.cnode` and
   `cnodeVisibilityLe` on that one — five non-slot fields pinned, slots only
   un-redacted — with `eq_of_cnodeVisibilityLe_of_slots_eq` the tripwire that
   fails if `CNode` grows a sixth non-slot field.  The consumer forms
   (`visibilityLe_objects_eq_of_not_cnode`, `visibilityLe_cnode_lookup`,
   `visibilityLe_objects_isSome`) all derive from the order alone.
2. **The four scheduling components had no clause at all** (P1).  `activeDomain`,
   `domainTimeRemaining`, `domainSchedule` and `domainScheduleIndex` are
   unfiltered (CC-1), so the truth about them is equality — and with no clause
   the order held in *both directions* between two states that differed in
   them, silently discarding the CC-1 content an SM8.B consumer would read as
   preserved.  Closed by adding the four equality clauses, and
   `ObservableState.eq_of_visibilityLe_antisymm` now states the property that
   was false: mutual domination plus agreement on `objects` is equality.  That
   theorem is also the standing completeness check on the clause list — it
   discharges one goal per `ObservableState` field, so a fourteenth component
   with no clause leaves a goal nothing can close, the same discipline
   `ofFragments_eta` applies to the field partition.  `visibilityLe` became a
   **structure** in the process, one named field per component in declaration
   order, so the clause list can be read against the component list and
   consumers write `h.runnable` rather than a projection chain.
3. **The fixture's TCBs named roots that did not exist** (P2).  Every
   `probeState` TCB declared `cspaceRoot := cnRoot` and `vspaceRoot := vsRoot`,
   but the builder inserted neither, so all four failed
   `KernelObject.wellFormed` — which `lifecycleRetype` validates before
   installing an object.  The evidence was therefore computed on a state no
   construction path can reach.  Closed by building both roots (§3.0 now checks
   TCB and CNode well-formedness, with the load-bearing negative that a TCB
   naming an absent root is rejected); OID band 1000–1015 → 1000–1019.

Suite 112 → **125 runtime assertions / 14 groups** (new §3.13 exercises the
object-content order and the four scheduling clauses, and shows the shifted-
`activeDomain` view that dominated the real one before this cut); module 104 →
**119 declarations**, all 113 term-level ones re-checked axiom-clean; Tier-3
anchors extended, including negative pins that the four scheduling clauses stay
equalities.  Theorems and tests only — no transition changed, trace
byte-identical.

**Deliberately not in SM8.A** (each is a later sub-phase, not an
omission): the per-core NI *preservation* theorems over transitions are
SM8.B; the lock-contention channel CC-5 is SM8.B.8; the
`DeclassificationEvent.originatingCore` extension is SM8.C.

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
| SM8.B.6 | `enforcementBoundaryPerCore` (39 entries — re-anchored) | Definition + theorem | M | LANDED |
| SM8.B.7 | Boundary completeness witness | Theorem | M | LANDED |
| SM8.B.8 | `acceptedCovertChannel_lockContention` | Definition | M | LANDED |
| SM8.B.9 | Mitigation note (WS-W partitioning) | Documentation | S | LANDED |
| SM8.B.10 | `acceptedCovertChannel_perCoreCount = 7` (re-anchored) | Theorem | T | LANDED |
| SM8.B.11 | `endpointPolicyRestricted_perCore` | Theorem | M | LANDED |
| SM8.B.12 | Per-core NI bridge to NI release | Theorem | M | LANDED |
| SM8.B.13 | `crossCoreLeakage_bounded` | Theorem | L | LANDED |
| SM8.B.14 | 15+ NI scenarios (tests) | L | LANDED |

**PR #861 review cut (v0.33.9).**  Seven automated-review findings, all
verified against the code and all valid.  The load-bearing one:
`endpointCallLiveWriteSet` walked the *caller* at the *pre-state*, while the live
arm runs `propagatePipChainCrossCore st'' receiverTid` — the resolved **receiver**
at the **post-donation** state.  Those are different chains (the call blocks the
caller on reply and the donation rewrites SchedContext bindings, so
`blockingServer` moves), so the union could omit cores the live arm writes.  No
theorem was false — none asserted the live bound — but the definition was wrong
for its stated purpose.  `chainState` / `chainStart` are now explicit parameters
whose docstring says what they must be instantiated to and why the pre-state
cannot supply them, with `endpointCallLive_confinedToCores` composing the legs.

Also closed: `crossCoreTransitionWakesRemote` renamed to `…WritesRemote` (reply,
deschedule and cancellation write remotely without waking); three **fail-open
gates** repaired — `run_negative_check` accepted `rg` exit 2 as absence,
`confinedCheck` omitted the register banks from a six-field predicate, and the
axiom sweep silently dropped unrecognised declaration kinds; the flow-gate
non-vacuity witness moved off the reserved sentinel thread id; and the
staged-module headline corrected 57 → 58.

Left open deliberately: whether the branch's four patch bumps collapse into one
for the merge — that rewrites pushed commits, so it is the maintainer's call.

**Audit cut (v0.33.7).**  A deep audit of the v0.33.6 follow-up found two
further items, both closed.

1. **The live `.call` arm writes cores no write set named.**
   `endpointCallOnCore_confinedToCores` is true of that *transition*, but the
   live arm is `endpointCallCrossCoreDispatch` = transition +
   `applyCallDonation` + `propagatePipChainCrossCore`, and the chain walk
   re-buckets each boosted server's run queue on that server's **home** core.
   The `syscallEntry_preserves_projectionOnCore` docstring nonetheless said the
   dispatch is "invisible on every core outside that set" — false for the live
   arm, and the same documentation-ahead-of-code failure the v0.33.6 cut existed
   to remove, reintroduced one layer up.  Closed by making it true:
   `pipChainWriteSet` (the walk's own write set, mirroring its fuel recursion)
   with `propagatePipChainCrossCore_confinedToCores` by induction,
   `applyCallDonation_confinedToCores` (per-core silent), and
   `endpointCallLiveWriteSet` — the union that actually bounds the live arm —
   with projection lemmas so a caller discharges membership once.
2. **Both marquee write sets were tested only in their degenerate branches.**
   The suite computed `notificationSignalWriteSet` with no waiter (`= []`) and
   `endpointCallWriteSet` with no receiver (`= [c0]`), so the two-element set —
   the flagship case, the whole reason `observableSlotsConfinedToCores` exists —
   had **zero runtime coverage**, and the group's "not a singleton" negative was
   `[c0] ≠ [c0, c2]`, trivially true.  Closed with a real rendezvous fixture
   (receiver and waiter both homed on core 2): §5.0 checks the call's set is
   `[c2, c0]` — two distinct cores — that the notification's names the waiter's
   home core and not the signaller's, and that the set genuinely *varies* with
   the state, which is what rules out a constant satisfying the theorem.

Suite 186 → 193 assertions / 29 groups; 359 declarations axiom-clean.

**Follow-up cut (v0.33.6) — the self-audit closure.**  A review of the v0.33.5
landing against the code rather than the prose found six things short of
optimal.  All are closed; the headline is the first.

1. **`crossCoreNonInterference` had no instantiation at a genuinely cross-core
   transition.**  Every one of the forty-odd confinement lemmas was for a
   single-core transition, so every application in the module had
   `c' = bootCoreId`; the only `c' ≠ bootCoreId` uses were in the test suite,
   against a hand-built record update rather than a transition.  Closed by the
   new staged module `InformationFlow/NonInterferenceCrossCore.lean` (staged
   57 → 58), which required generalising confinement from one core to a **set**
   (`observableSlotsConfinedToCores`, factored through the new
   `observableSlotsAgreeOn` primitive so the substantive proof exists once and
   the thirty-five existing lifts do not churn) — because `endpointCallOnCore`
   writes the receiver's home core *and* the caller's own, two targets that in
   the interesting case differ.  Six transitions instantiated over pre-state
   write sets, on a reusable home-core frame layer (a store preserves a home
   core unless it is a *migration*, which no IPC-pipeline store is).  Coherence
   with SM3: the write sets are keyed on the same pre-resolutions the lock sets
   use (`notificationSignalWriteSet_eq_lockSet_waiter`, `endpointCallReceiver?`).
   **What it buys over SM6**: those results are conditional on the woken thread
   being non-observable; this holds for a *fully visible* one, because the
   remote core's slots did not move.
2. **`endpointFlowCheck_state_independent` was a tautology** — `X = X` by `rfl`
   with unused state/core binders, cited in five prose sites as evidence, and
   provable for a function that *does* read state.  Replaced by
   `endpointFlowCheckAtCore` (which genuinely takes a state and a core) plus
   `…_depends_only_on_subject`, the SMP corollary
   `…_stable_under_confined_transition` (a transition on other cores cannot flip
   core `c`'s gate), and `…_is_not_constant`.  A Tier-3 **negative** anchor
   forbids the old symbol.  `endpointPolicyRestricted_perCore` keeps its vacuous
   `∀ _c` — it is the `…_smp` naming idiom — but the docstring now says so and
   credits the `iff`, not the tautology.
3. **Two docstrings over-claimed** (the module header's "§5 instantiates
   `crossCoreNonInterference` at cross-core transitions", and
   `syscallEntry_preserves_projectionOnCore`'s "§4 discharges the obligation for
   each operation the dispatch routes to" — false for the `…OnCore` arms the
   live cross-core dispatch actually routes to).  Both corrected against the new
   module.
4. **Two coverage tables were unverified data**: `perCoreConfinementDerived`
   ended in a wildcard (so a new variant would be silently misclassified — all
   thirty-five arms are now enumerated), and both theorem-name tables were plain
   strings with no link to a declaration (now through `niName!`, a compile-time
   identifier-validating macro in the `pcist!` idiom).
5. **The axiom check was not exhaustive** despite being published as such: its
   regex missed three `@[simp] theorem` declarations.  Replaced by
   `scripts/check_module_axioms.py`, driven by `docs/codebase_map.json` and
   **run** from Tier 3; it reports the two `private` helpers it cannot probe
   rather than dropping them.  351 declarations, all axiom-clean.
6. **Scenario count**: 167 → 186 assertions / 28 groups, four new groups driving
   real cross-core transitions with load-bearing negatives.

**CLOSED at v0.33.8**: `cancelIpcBlockingOnCore`'s *composed* confinement.  The
blocker was the missing frame, not a hard proof — per-core confinement reads each
core's register bank as well as its scheduler slots, and only
`cancelIpcBlocking_scheduler_eq` existed.  `cancelIpcBlocking_machine_eq` now
sits beside it on a new leaf layer (`restoreToReady` / `clearTcbIpcFields` /
the reply-link legs / both queue sweeps, the sweeps by the same
`RHTable.fold_preserves` argument SM7.B used for `tlbShootdown`), giving
`cancelIpcBlocking_confinedToCores` (`[]`) and
`cancelIpcBlockingOnCore_confinedToCores` (`[] ++ [home]`) with its NI
instantiation.  Coverage 6 → 7 transitions.

Remaining scoped follow-on: the `endpointReceiveDualOnCore` /
`endpointReplyRecvOnCore` composites, which compose the same primitives.

**Landing record (v0.33.5).**  Two new staged modules (staged-only count 55 →
57), 188 declarations, zero `sorry`/`axiom` — every one of the 184 term-level
declarations depends only on `propext` / `Quot.sound` / `Classical.choice`,
checked exhaustively rather than by sampling.  No transition changed, so the
golden trace is byte-identical.

* `SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean` (151
  declarations) — SM8.B.1 … SM8.B.5 and SM8.B.13.
* `SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean` (37 declarations) —
  SM8.B.6 … SM8.B.12.

* **SM8.B.2 first, because SM8.B.1 is its corollary.**
  `crossCoreNonInterference` (plan Theorem 3.3.1) rests on SM8.A's field
  partition being a *bijection*: the view is determined by its two fragments, so
  proving both halves unchanged **is** proving the view unchanged.  The two
  premises are the plan's two, restated as frames —
  `observableSlotsConfinedToCore st st' c'` (the plan's `transitionRunsOnCore`:
  every per-core slot outside core `c'` comes through unchanged, register banks
  included, which under SM5.I is a genuine obligation rather than a structural
  fact) and `sharedViewUnchanged` (the plan's
  `transitionDoesntMutateLabelLeqObjects` **and**
  `transitionDoesntSignalLabelObservableNotification` together, since signalling
  a notification writes its object).  *The plan's own proof sketch is not
  available*: it discharges Theorem 3.3.1 from serializability, and SM3.C.9
  still defers wrapping the `@[export]` bodies in `withLockSet` while v0.32.142
  serialises kernel entry with one global ticket lock.  The theorem is therefore
  proven from the frame premises, which assumes strictly less and so concludes
  strictly more; `crossCoreNonInterference_of_disjoint_lockSet` supplies the
  plan's argument as a *bridge*, so once SM3.C.9 lands it is a corollary rather
  than an assumption.
* **SM8.B.1** — `nonInterference_perCore` splits by core: at `bootCoreId` the
  per-core view **is** `projectState`, so the existing
  `step_preserves_projection` applies verbatim; at every other core it is
  SM8.B.2 at `c' = bootCoreId`, with the shared half free because the shared
  fragment of the per-core view *is* the shared fragment of the global
  projection.  `lowEquivalent_smp_of_projection_and_confinement` is the reusable
  core, factored out because §6 (the lock bracket) and §4 of the boundary module
  (the release bridge) supply the same two premises without being
  `NonInterferenceStep`s.  Plus the two-sided `composedNonInterference_step_perCore`
  and the trace form.
* **SM8.B.3 — the confinement premise is *derived*, not assumed.**  All
  thirty-five per-operation lifts, each taking exactly the hypotheses its
  `NonInterferenceStep` constructor takes.  Thirty-one discharge
  `observableSlotsConfinedToCore … bootCoreId` from the operation's own
  semantics — including `schedule`, `handleYield`, `timerTick` and all seven IPC
  transitions, whose case skeletons mirror the SM6.D.2
  `…_passiveServerIdleFrameOnCore` proofs.  **This strengthens the SM4.C / SM4.D
  precedent**, whose per-core preservation theorems carry the same fact as an
  `hOtherIdle` / `hNonBootIdle` hypothesis with a "SM5 discharges it" note: for
  these operations it is now discharged.  The remaining four
  (`syscallDispatchHigh`, `endpointCallWithDonationHigh`,
  `endpointReplyWithReversionHigh`, `handleInterrupt`) carry a whole-state
  projection hypothesis and no operational one, so they range over transitions
  that genuinely *do* write a remote core — the live cross-core dispatch among
  them — and take the premise explicitly.  `perCoreConfinementDerived` records
  the 31/4 split as a decidable function and `perCoreConfinementDerived_count`
  as a checked fact, so a new catch-all cannot be added silently.  Suite §4.9 is
  the load-bearing negative: a core-1 write preserves the *global* projection
  and still moves core 1's own view, so the premise is necessary.
* **SM8.B.4 — and the security fix it forced.**  The 2PL bracket is
  non-interference transparent: `withLockSet_preserves_projection` holds with
  **no** hypothesis about which objects the lock set names and none about
  contention.  Getting there required closing a real gap.  `RwLockState` carries
  `writerHeld : Option CoreId`, `readers : List CoreId` and
  `waiters : List (CoreId × AccessMode)` — every field a core identity — and
  `projectKernelObject` carried the per-object `lock` straight through (its
  `.reply` arm even documented "only `lock` survives (an `RwLockState` carrying
  no cross-domain identity)", which is false).  An observer that can see an
  object would therefore read off the set of cores operating on it: the
  *placement* channel WS-SM SM5.B closed by stripping `TCB.cpuAffinity`,
  re-opened through another field and on every object kind rather than just
  TCBs.  `lock` is now erased structurally on every projected arm — per SM5.B's
  own stated discipline, *not* justified by "no live operation sets it yet"
  (true today only because SM3.C.9 defers the fine locks).  With the erasure,
  CC-5 is a hardware **timing** channel and nothing more, exactly as plan
  Definition 3.4.1 describes it.  The whole library rebuilt unchanged and the
  trace is byte-identical.
* **SM8.B.5** — `niStepCoverage_perCore` (the exhaustive-match tripwire, one
  layer up from `niStepConstructorCoverage`), `kernelOperationPerCoreNiTheorem`
  naming each operation's per-core theorem with
  `niStepCoverage_perCore_injective` / `_count` making the correspondence 1:1
  and complete at 35.
* **SM8.B.6 / SM8.B.7** — `enforcementBoundaryPerCore`: the canonical 38-entry
  boundary plus the one operation SMP adds, the 2PL bracket, classified
  capability-only for the same reason as `storeObject`'s (an internal building
  block used under an already-capability-guarded context, consulting no
  information-flow policy).  **Re-anchored**: the plan's "23 entries" figure was
  written against the `v0.31.2` cut, and the live canonical count is 38, so the
  per-core boundary is 39.  A *separate* list rather than an edit to the
  canonical one, because promoting the entry is SM8.E.3's sub-task and moving
  the base count here would leave SM8.E a figure to reconcile.  Completeness in
  three parts: the per-core list extends the canonical one (`rfl`), every
  `SyscallId` is still covered (`decide`, not `native_decide`), and the added
  entry is genuinely new.
* **SM8.B.8 / SM8.B.9 / SM8.B.10** — the accepted covert channels as **data**:
  a `CovertChannel` record carrying the plan's CC-number, the description, the
  WS-W mitigation note, the severity, whether the channel is *model-visible*
  (carried by `ObservableState`) and whether SMP gives it one instance per core.
  Seven entries, CC-1 … CC-7, with `acceptedCovertChannel_perCore_ids` pinning
  the numbering by `rfl`.  **Re-anchored**: the plan's sub-task line reads
  `= 5`, written before CC-6 and CC-7 existed — the SM8.A cut registered them
  when SM7.C and SM7.D mounted the per-core TLB and instruction-cache views, and
  §3.5 lists all seven, so asserting 5 would produce a false count.  The split
  is checked, not asserted: three model-visible, four hardware-only, five
  per-core.  Every entry carries the theorem that fixes its status —
  `withLockSet_preserves_projection` for CC-5, `onCore_perCoreTlb` /
  `onCore_perCoreICache` for CC-6 / CC-7, `onCore_schedulingTransparency` for
  CC-1 — so an entry cannot be reclassified without the theorem moving.
* **SM8.B.11** — `endpointPolicyRestricted_perCore` in the SM4.D `…_smp` idiom,
  with `_iff` recording that the core coordinate cannot change the decision and
  `endpointFlowCheck_state_independent` the fact that makes it true: the
  enforcement gate reads the labeling context and the two domains and **no
  per-core state**, so a transition running elsewhere can never flip it.
  `endpointPolicyRestricted_perCore_is_necessary` is the non-vacuity witness —
  an all-permitting override over an all-denying policy really is a bypass.
* **SM8.B.12** — the bridge to the release-grade witnesses, both ways: *up*,
  `syscallEntry_preserves_projection` plus boot-core confinement gives the
  per-core statement (`syscallEntry_preserves_projectionOnCore`,
  `syscallEntry_success_perCore_NI`, and the hypothesis-free failure case);
  *down*, the per-core statement implies the release-grade one at `bootCoreId`,
  so SM8.B strengthens the release surface rather than running beside it.  The
  two inner witnesses are reached through the entry point because
  `dispatchCapabilityOnly` / `dispatchWithCapChecked` are `private` to
  `API.lean`.
* **SM8.B.13** — `crossCoreLeakage_bounded` as an `↔`, which is what makes it a
  bound: a transition confined to core `c'` freezes core `c`'s per-core fragment
  outright, so the observer's view moves **if and only if** the shared fragment
  moves.  `crossCoreLeakage_bounded_reconstruction` states it constructively —
  the post-view is literally rebuilt from the new shared half and the observer's
  *own* pre-transition per-core half — so six of the thirteen components carry
  no cross-core flow at all.
* **SM8.B.14** — `tests/SmpInformationFlowSuite.lean` grows to **167 runtime
  assertions across 24 groups** (was 125 / 14) on the same four-thread /
  four-core fixture, extended with a high and a low notification so real
  transitions can be run.  Ten new groups (§4.1 … §4.10) cover cross-core
  invisibility, `nonInterference_perCore` on a real `notificationSignal`, the
  derived confinement, the lock bracket, the leakage bound, per-core coverage,
  the boundary, the channel inventory, the catch-all premise and the policy /
  release bridge.  Load-bearing negatives: §4.1 (the same write on the
  observer's *own* core is visible), §4.2 (signalling a *low* notification is
  visible), §4.3 (a core-1 write is not boot-core-confined), §4.4 (the raw lock
  field genuinely changed — so the invisibility is the projection's doing, not a
  no-op), §4.8 (CC-1 is on the model-visible side, so the split is real), §4.9
  (global-projection preservation does not imply the per-core statement), §4.10
  (the policy-restriction hypothesis is necessary).  188 `#check` anchors — every
  declaration of both modules — plus headline anchors in
  `tests/SmpSurfaceAnchors.lean` and a Tier-3 block that pins every module
  symbol by set difference, the 31/4 split, and the `lock` erasure on each
  projected arm.

**AK7 re-anchor.**  `RAW_LOOKUP_TID` 1310 → 1314.  The four increments are the
`hRecvQueueNextHigh` / `hSendQueueNextHigh` hypotheses of the four IPC
per-operation lifts, which are *verbatim copies* of the corresponding
`NonInterferenceStep` constructor fields and so must mention
`st.objects[receiver.toObjId]?` to typecheck — the metric counts the same
hypothesis twice.  No new live raw read: the confinement proofs reduce the
operations' own object-store matches with `split` rather than naming the
scrutinee.  `GETTCB_ADOPTION` 2157 → 2163 and `GETVSPACEROOT_ADOPTION` 43 → 46
grow (should-grow metrics).

**Deliberately not in SM8.B** (each a later sub-phase, not an omission): the
`DeclassificationEvent.originatingCore` extension and the cross-core
declassification audit are SM8.C; the lock-state visibility documentation and
the reader-multiplicity / writer-exclusion theorems are SM8.D (whose D.1–D.3
this cut partly pre-empts and partly falsifies — see the note under that
table, since the erasure means there is no lock state left to be visible);
promoting the
`withLockSet` boundary entry into the canonical `enforcementBoundary` (38 → 39)
and the `smp_information_flow.expected` fixture are SM8.E.

### SM8.C — Per-core declassification audit (7 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM8.C.1 | `DeclassificationEvent.originatingCore : CoreId` extension | Structure | M |
| SM8.C.2 | Cross-core declassification chains in audit trail | Theorem | M |
| SM8.C.3 | Every declass event has valid originatingCore | Theorem | S |
| SM8.C.4 | `DeclassificationEvent_perCore_audit` | Theorem | M |
| SM8.C.5 | `authorizationBasis_perCore` extending V6-H | Theorem | M |
| SM8.C.6 | Cross-core declass rules | Theorem | M |
| SM8.C.7 | Per-core declass test scenarios | M |

### SM8.D — Information flow under fine locks (6 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM8.D.1 | Lock state visibility documented | docstring | M |
| SM8.D.2 | Reader-multiplicity not directly observable | Theorem | M |
| SM8.D.3 | Writer-exclusion observable to blocked readers | docstring | T |
| SM8.D.4 | Biba-integrity under per-core locks | Theorem | M |
| SM8.D.5 | Secure-information-flow witness under fine locks | Theorem | M |
| SM8.D.6 | Lock-contention IF scenarios (5 tests) | M |

**Note — SM8.B moved the ground under D.1–D.3.**  This table was written
while `projectKernelObject` carried each object's `lock : RwLockState` into
the observable state, which is what made "lock state visibility" something to
document and "reader multiplicity" something to prove unobservable.  SM8.B
erased the field on every projected arm (it is three fields of `CoreId`s, so
it re-opened the SM5.B placement channel through a different field and on
every object kind), so at the model level:

- **D.1** is no longer a docstring about what an observer sees of the lock —
  it is the statement that an observer sees *nothing* of it.  The erasure
  itself, plus the Tier-3 anchors pinning `lock := …unheld` on each arm, is
  the evidence; what remains for D.1 is the *hardware* side, where a real
  observer times its own acquisitions.
- **D.2** is now structurally true rather than a theorem to prove:
  `withLockSet_preserves_projection` holds unconditionally, with no
  hypothesis on which objects the lock set names or whether they are
  contended, and reader multiplicity is not a component of `ObservableState`
  at all.  D.2 should be restated as the *timing* claim (CC-5), which is the
  only form that is still open.
- **D.3** is **false as written** at the model level — a blocked reader
  observes nothing of writer exclusion in the projection.  It is true only as
  wall-clock delay, i.e. CC-5 again.  Restate it as such rather than
  reinstating the field.

D.4–D.6 are unaffected: Biba integrity and the secure-flow witness are about
which subjects may write which objects, not about the lock word, and the
contention scenarios are timing scenarios.

### SM8.E — Tests + closure (3 sub-tasks)

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
      `enforcementBoundaryPerCore` at 39 entries, the canonical list's promotion
      to 39 remaining as SM8.E.3).
- [ ] `DeclassificationEvent.originatingCore` field; audit trail updated.
- [ ] Tier 0..3 green.

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
`crossCoreLeakage_bounded`.

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
