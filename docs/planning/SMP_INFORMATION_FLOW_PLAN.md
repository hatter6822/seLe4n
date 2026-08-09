# SM8 — Information Flow Under SMP (WS-SM Phase 8)

> **Phase**: SM8 of WS-SM
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Audited cut**: `v0.31.2`
> **Target releases**: v0.91.0 .. v0.97.x (parallel with SM7)
> **Calendar estimate**: 5-8 weeks
> **Sub-task count**: 40-55 across ~15-22 PRs
> **Status**: SM8.A COMPLETE at v0.33.3, review cut v0.33.4 (landed
> v0.33.2); SM8.B–SM8.E pending

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
