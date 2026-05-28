-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Invariant
-- WS-SM SM4.C audit-pass-3: cross-subsystem per-core predicates per plan §5.6
-- require `schedContextRunQueueConsistent` (CrossSubsystem) and
-- `PriorityInheritance.blockingAcyclic` (PriorityInheritance/BlockingGraph).
import SeLe4n.Kernel.CrossSubsystem
import SeLe4n.Kernel.Scheduler.PriorityInheritance.BlockingGraph

-- The boot-core bridge proofs in §2 use `cases h : X` substitution to
-- substantively case-analyse on `objects[…]?` lookups.  The `simp [h]`
-- calls at the leaves uniformly include the equation hypothesis: in some
-- arms `h` is genuinely required for simp to discharge (verified
-- empirically — removing `[h]` from e.g. line 428 / 446 / 474 / 504
-- breaks the proof with "unsolved goals"); in others the surrounding
-- `cases` substitution makes `[h]` redundant.  The unused-args linter
-- flags the redundant arms but cannot distinguish the two patterns
-- automatically (they have the same surface syntax).  Suppress
-- file-locally so the uniform defensive pattern compiles cleanly;
-- the "unused" warnings are false positives in the `cases h : X`
-- context.
set_option linter.unusedSimpArgs false

/-!
# WS-SM SM4.C — Per-core scheduler invariant migration

This module is the SM4.C deliverable of the WS-SM path-a per-core state
replacement (plan `docs/planning/SMP_PER_CORE_STATE_PLAN.md` §5.3, §5.6).

The SM4.B foundation flipped every per-core `SchedulerState` field to
`Vector α numCores` and routed the existing single-core invariant surface
through the boot core (`…OnCore bootCoreId`).  SM4.C lifts the scheduler
invariant *predicates* to an explicit `(c : CoreId)` parameter — the
migration pattern of plan §3.4: each per-core invariant `P` gains a
sibling `P…OnCore s c` whose body is `P`'s body with `bootCoreId`
replaced by `c` and `s.runnable` (the boot-core run-queue projection)
replaced by `(s.runQueueOnCore c).toList`.

The migration is **additive and soundness-preserving**: every per-core
form at `bootCoreId` is *provably* equivalent to the existing
single-core form (the §2 boot-core bridge lemmas).  The existing
cross-subsystem invariant surface (`schedulerInvariantBundle*`,
`crossSubsystemInvariant`, and the hundreds of preservation theorems
that consume them) is therefore untouched and stays green; SM4.C
strictly *adds* the per-core layer.

**AK7 typed-accessor discipline**: all sixteen per-core predicate bodies
route their object-store lookups through the typed `getTcb?` /
`getSchedContext?` accessors.  Single-level-lookup bridges go through
`getTcb?_eq_some_iff` plus per-variant case analysis on `objects[…]?`;
two-level-lookup bridges (TCB-then-SchedContext: `currentBudgetPositive*`,
`budgetPositive*`, `effectiveParamsMatchRunQueue*`) `unfold` each typed
accessor's underlying `match` and discharge via nested `cases h :
objects[…]?` (binding-arm-shared SchedContext lookup case-analysed under
each `bound`/`donated` arm).

## What this module proves (plan §5.6 + §8 acceptance gate)

1. **Per-core predicate forms** — `…OnCore s c` for every genuinely
   per-core scheduler invariant (the per-core slice of
   `schedulerInvariantBundleExtended`).  System-wide invariants
   (`schedContextsWellFormed`, `schedContextBindingConsistent`,
   `boundThreadDomainConsistent`, `domainScheduleEntriesPositive`,
   `configTimeSlicePositive`) are core-independent and need no `c`.
2. **Boot-core bridges** — `…_bootCore_iff` proving each per-core form
   at `bootCoreId` is equivalent to the existing single-core predicate
   (the non-orphan connection to the live surface).
3. **Per-core frame lemmas** — each `…OnCore s c` depends only on core
   `c`'s slots (plus `objects` / `machine.regs`), so a modification that
   frames those reads preserves it.  This is the substantive content
   SM5's per-core scheduler consumes.
4. **`schedulerInvariant_perCore`** (SM4.C.29) — the aggregate per-core
   invariant, mirroring `schedulerInvariantBundleFull`'s per-core slice,
   plus `schedulerInvariant_smp := ∀ c, …` and the `aggregateForall`
   bridge.
5. **`schedulerInvariant_perCore_pairwise`** (SM4.C.30) — distinct cores'
   per-core invariants are independent: writing core `c₂`'s slots never
   affects core `c₁`'s invariant.  This *strengthens* the plan's
   trivial `P ↔ P` documentation form into a real cross-core
   independence theorem (per the implement-the-improvement rule).
6. **Default-state** — every core satisfies the per-core invariant on the
   freshly-booted (empty) system.

Axiom-clean: every headline theorem depends only on the standard
foundational axioms (`propext` / `Quot.sound` / `Classical.choice`),
verified via `#print axioms` on each in the suite.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (numCores CoreId bootCoreId allCores)

-- ============================================================================
-- §1  Per-core predicate forms (plan §3.4 migration pattern)
-- ============================================================================

/-- SM4.C: per-core dequeue-on-dispatch consistency.  Per-core form of
`queueCurrentConsistent` (plan §3.4 Pattern 1): when core `c`'s current
thread is `some tid`, `tid` is not in core `c`'s run queue. -/
def queueCurrentConsistentOnCore (s : SchedulerState) (c : CoreId) : Prop :=
  match s.currentOnCore c with
  | none => True
  | some tid => tid ∉ (s.runQueueOnCore c).toList

/-- SM4.C: per-core run-queue uniqueness.  Per-core form of
`runQueueUnique`: core `c`'s runnable list has no duplicate TIDs. -/
def runQueueUniqueOnCore (s : SchedulerState) (c : CoreId) : Prop :=
  (s.runQueueOnCore c).toList.Nodup

/-- SM4.C (plan §5.6): per-core run-queue well-formedness.  Asserts that
core `c`'s `RunQueue` satisfies its internal `RunQueue.wellFormed` invariant
(`byPriority` ↔ `membership` / `threadPriority` consistency).  This is the
per-core analog of "the queue's priority index is in sync with its
membership index" — the property the WS-G4 bucketed-RunQueue structure
provides intrinsically and that SM5's per-core scheduler will preserve. -/
def runQueueOnCoreWellFormed (s : SchedulerState) (c : CoreId) : Prop :=
  (s.runQueueOnCore c).wellFormed

/-- SM4.C: per-core current-thread validity.  Per-core form of
`currentThreadValid`: core `c`'s current thread (if any) resolves to a
TCB in the object store.  Uses the typed `getTcb?` accessor (AK7
discipline). -/
def currentThreadValidOnCore (st : SystemState) (c : CoreId) : Prop :=
  match st.scheduler.currentOnCore c with
  | none => True
  | some tid => ∃ tcb : TCB, st.getTcb? tid = some tcb

/-- SM4.C: per-core current-in-active-domain.  Per-core form of
`currentThreadInActiveDomain`: core `c`'s current thread belongs to core
`c`'s active scheduling domain. -/
def currentThreadInActiveDomainOnCore (st : SystemState) (c : CoreId) : Prop :=
  match st.scheduler.currentOnCore c with
  | none => True
  | some tid =>
      match st.getTcb? tid with
      | some tcb => tcb.domain = (st.scheduler.activeDomainOnCore c)
      | none => True

/-- SM4.C: per-core time-slice positivity for runnable threads.  Per-core
form of `timeSlicePositive`. -/
def timeSlicePositiveOnCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ tid, tid ∈ (st.scheduler.runQueueOnCore c).toList →
    match st.getTcb? tid with
    | some tcb => tcb.timeSlice > 0
    | none => True

/-- SM4.C: per-core current-thread time-slice positivity.  Per-core form
of `currentTimeSlicePositive`. -/
def currentTimeSlicePositiveOnCore (st : SystemState) (c : CoreId) : Prop :=
  match st.scheduler.currentOnCore c with
  | none => True
  | some tid =>
    match st.getTcb? tid with
    | some tcb => tcb.timeSlice > 0
    | none => True

/-- SM4.C: per-core EDF.  Per-core form of `edfCurrentHasEarliestDeadline`:
core `c`'s current thread has the earliest deadline among same-domain,
same-priority runnable threads on core `c`. -/
def edfCurrentHasEarliestDeadlineOnCore (st : SystemState) (c : CoreId) : Prop :=
  match st.scheduler.currentOnCore c with
  | none => True
  | some curTid =>
      match st.getTcb? curTid with
      | some curTcb =>
          ∀ tid, tid ∈ (st.scheduler.runQueueOnCore c).toList →
            match st.getTcb? tid with
            | some tcb =>
                tcb.domain = curTcb.domain →
                effectiveRunQueuePriority tcb = effectiveRunQueuePriority curTcb →
                tcb.priority = curTcb.priority →
                curTcb.deadline.toNat = 0 ∨
                (tcb.deadline.toNat = 0 ∨ curTcb.deadline.toNat ≤ tcb.deadline.toNat)
            | none => True
      | none => True

/-- SM4.C: per-core register-context match.  Per-core form of
`contextMatchesCurrent`: when core `c` has a current thread, the machine
register file matches that thread's saved context.  (At SM4.C the machine
register file is still system-wide; SM5 introduces per-core register
banks, at which point this reads core `c`'s bank.) -/
def contextMatchesCurrentOnCore (st : SystemState) (c : CoreId) : Prop :=
  match st.scheduler.currentOnCore c with
  | some tid =>
      match st.getTcb? tid with
      | some tcb => (st.machine.regs == tcb.registerContext) = true
      | none => True
  | none => True

/-- SM4.C: per-core runnable-threads-are-TCBs.  Per-core form of
`runnableThreadsAreTCBs`. -/
def runnableThreadsAreTCBsOnCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ tid, tid ∈ (st.scheduler.runQueueOnCore c).toList →
    ∃ tcb : TCB, st.getTcb? tid = some tcb

/-- SM4.C: per-core priority-match.  Per-core form of
`schedulerPriorityMatch`: core `c`'s run-queue priority index agrees with
the effective priority of every member. -/
def schedulerPriorityMatchOnCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ tid, tid ∈ (st.scheduler.runQueueOnCore c) →
    match st.getTcb? tid with
    | some tcb =>
        (st.scheduler.runQueueOnCore c).threadPriority[tid]? = some (effectiveRunQueuePriority tcb)
    | none => True

/-- SM4.C: per-core domain-time positivity.  Per-core form of
`domainTimeRemainingPositive`. -/
def domainTimeRemainingPositiveOnCore (st : SystemState) (c : CoreId) : Prop :=
  (st.scheduler.domainTimeRemainingOnCore c) > 0

/-- SM4.C: per-core current-budget positivity.  Per-core form of
`currentBudgetPositive`.  Uses the typed `getTcb?` / `getSchedContext?`
accessors (AK7 discipline); the boot-core bridge converts via nested
`cases` on `objects[…]?` (the typed accessors' underlying lookups). -/
def currentBudgetPositiveOnCore (st : SystemState) (c : CoreId) : Prop :=
  match st.scheduler.currentOnCore c with
  | none => True
  | some tid =>
    match st.getTcb? tid with
    | some tcb =>
      match tcb.schedContextBinding with
      | .unbound => True
      | .bound scId | .donated scId _ =>
        match st.getSchedContext? scId with
        | some sc => sc.budgetRemaining.val > 0
        | none => True
    | none => True

/-- SM4.C: per-core budget positivity for runnable threads.  Per-core form
of `budgetPositive`.  Uses the typed `getTcb?` / `getSchedContext?`
accessors. -/
def budgetPositiveOnCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ tid, tid ∈ (st.scheduler.runQueueOnCore c).toList →
    match st.getTcb? tid with
    | some tcb =>
      match tcb.schedContextBinding with
      | .unbound => True
      | .bound scId | .donated scId _ =>
        match st.getSchedContext? scId with
        | some sc => sc.budgetRemaining.val > 0
        | none => True
    | none => True

/-- SM4.C: per-core replenishment-pipeline ordering.  Per-core form of
`replenishmentPipelineOrder`: every entry of core `c`'s replenish queue is
eligible strictly after the machine timer. -/
def replenishmentPipelineOrderOnCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ (pair : SchedContextId × Nat),
    pair ∈ (st.scheduler.replenishQueueOnCore c).entries → pair.2 > st.machine.timer

/-- SM4.C: per-core replenish-queue validity.  Per-core form of
`replenishQueueValid`. -/
def replenishQueueValidOnCore (st : SystemState) (c : CoreId) : Prop :=
  replenishQueueSorted (st.scheduler.replenishQueueOnCore c) ∧
  replenishQueueSizeConsistent (st.scheduler.replenishQueueOnCore c)

/-- SM4.C: per-core effective-params-match.  Per-core form of
`effectiveParamsMatchRunQueue`.  Uses the typed `getTcb?` /
`getSchedContext?` accessors. -/
def effectiveParamsMatchRunQueueOnCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ tid, tid ∈ (st.scheduler.runQueueOnCore c) →
    match st.getTcb? tid with
    | some tcb =>
      match tcb.schedContextBinding with
      | .unbound =>
        (st.scheduler.runQueueOnCore c).threadPriority[tid]? = some tcb.priority
      | .bound scId | .donated scId _ =>
        match st.getSchedContext? scId with
        | some sc =>
          (st.scheduler.runQueueOnCore c).threadPriority[tid]? = some sc.priority
        | none => True
    | none => True

-- ============================================================================
-- §1.5  Object-accessor congruence helpers (frame-lemma plumbing)
-- ============================================================================

/-- A private helper for the frame lemma below: if two `SystemState`s
agree on `objects`, every `getTcb?` query agrees too. -/
private theorem getTcb?_congr_objects
    {st st' : SystemState} (h : st'.objects = st.objects)
    (tid : SeLe4n.ThreadId) : st'.getTcb? tid = st.getTcb? tid := by
  unfold SystemState.getTcb?; rw [h]


-- ============================================================================
-- §2  Boot-core bridges (the non-orphan connection to the live surface)
-- ============================================================================
--
-- Each per-core form at `bootCoreId` is provably equivalent to the
-- existing single-core predicate.  Bridges where the per-core body and
-- the legacy body coincide syntactically (those without `getTcb?` /
-- `getSchedContext?`) close by `Iff.rfl`; bridges that go through the
-- typed accessors close via `getTcb?_eq_some_iff` /
-- `getSchedContext?_eq_some_iff` plus case analysis on the underlying
-- `objects[...]?` lookup.  These connect the SM4.C per-core layer to
-- the live `schedulerInvariantBundle*` surface so the new predicates
-- are never orphaned.

theorem queueCurrentConsistentOnCore_bootCore_iff (s : SchedulerState) :
    queueCurrentConsistentOnCore s bootCoreId ↔ queueCurrentConsistent s := Iff.rfl

theorem runQueueUniqueOnCore_bootCore_iff (s : SchedulerState) :
    runQueueUniqueOnCore s bootCoreId ↔ runQueueUnique s := Iff.rfl

theorem currentThreadValidOnCore_bootCore_iff (st : SystemState) :
    currentThreadValidOnCore st bootCoreId ↔ currentThreadValid st := by
  unfold currentThreadValidOnCore currentThreadValid
  cases h : st.scheduler.currentOnCore bootCoreId with
  | none => simp
  | some tid =>
    simp only
    constructor
    · rintro ⟨tcb, hTcb⟩; exact ⟨tcb, (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb⟩
    · rintro ⟨tcb, hObj⟩; exact ⟨tcb, (SystemState.getTcb?_eq_some_iff st tid tcb).mpr hObj⟩

theorem currentThreadInActiveDomainOnCore_bootCore_iff (st : SystemState) :
    currentThreadInActiveDomainOnCore st bootCoreId ↔ currentThreadInActiveDomain st := by
  unfold currentThreadInActiveDomainOnCore currentThreadInActiveDomain
  cases hCur : st.scheduler.currentOnCore bootCoreId with
  | none => simp
  | some tid =>
    simp only
    unfold SystemState.getTcb?
    cases hObj : (st.objects[tid.toObjId]? : Option KernelObject) with
    | none => simp [hObj]
    | some obj => cases obj <;> simp [hObj]

theorem timeSlicePositiveOnCore_bootCore_iff (st : SystemState) :
    timeSlicePositiveOnCore st bootCoreId ↔ timeSlicePositive st := by
  unfold timeSlicePositiveOnCore timeSlicePositive
  constructor
  all_goals
    intro h tid hMem
    have hSpec := h tid hMem
    unfold SystemState.getTcb? at *
    cases hObj : (st.objects[tid.toObjId]? : Option KernelObject) with
    | none => rw [hObj] at *; trivial
    | some obj => cases obj <;> (rw [hObj] at hSpec; simp_all)

theorem currentTimeSlicePositiveOnCore_bootCore_iff (st : SystemState) :
    currentTimeSlicePositiveOnCore st bootCoreId ↔ currentTimeSlicePositive st := by
  unfold currentTimeSlicePositiveOnCore currentTimeSlicePositive
  cases hCur : st.scheduler.currentOnCore bootCoreId with
  | none => simp
  | some tid =>
    simp only
    unfold SystemState.getTcb?
    cases hObj : (st.objects[tid.toObjId]? : Option KernelObject) with
    | none => simp [hObj]
    | some obj => cases obj <;> simp [hObj]

theorem edfCurrentHasEarliestDeadlineOnCore_bootCore_iff (st : SystemState) :
    edfCurrentHasEarliestDeadlineOnCore st bootCoreId ↔ edfCurrentHasEarliestDeadline st := by
  unfold edfCurrentHasEarliestDeadlineOnCore edfCurrentHasEarliestDeadline
  cases hCur : st.scheduler.currentOnCore bootCoreId with
  | none => simp
  | some curTid =>
    simp only
    unfold SystemState.getTcb?
    cases hObjCur : (st.objects[curTid.toObjId]? : Option KernelObject) with
    | none => simp [hObjCur]
    | some objCur =>
      cases objCur with
      | tcb curTcb =>
        simp [hObjCur]
        constructor
        all_goals
          intro h tid hMem
          have hSpec := h tid hMem
          cases hObj : (st.objects[tid.toObjId]? : Option KernelObject) with
          | none => rw [hObj] at *; trivial
          | some obj => cases obj <;> (rw [hObj] at hSpec; simp_all)
      | _ => simp [hObjCur]

theorem contextMatchesCurrentOnCore_bootCore_iff (st : SystemState) :
    contextMatchesCurrentOnCore st bootCoreId ↔ contextMatchesCurrent st := by
  unfold contextMatchesCurrentOnCore contextMatchesCurrent
  cases hCur : st.scheduler.currentOnCore bootCoreId with
  | none => simp
  | some tid =>
    simp only
    unfold SystemState.getTcb?
    cases hObj : (st.objects[tid.toObjId]? : Option KernelObject) with
    | none => simp [hObj]
    | some obj => cases obj <;> simp [hObj]

theorem runnableThreadsAreTCBsOnCore_bootCore_iff (st : SystemState) :
    runnableThreadsAreTCBsOnCore st bootCoreId ↔ runnableThreadsAreTCBs st := by
  unfold runnableThreadsAreTCBsOnCore runnableThreadsAreTCBs
  constructor
  · intro h tid hMem
    obtain ⟨tcb, hTcb⟩ := h tid hMem
    exact ⟨tcb, (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb⟩
  · intro h tid hMem
    obtain ⟨tcb, hObj⟩ := h tid hMem
    exact ⟨tcb, (SystemState.getTcb?_eq_some_iff st tid tcb).mpr hObj⟩

theorem schedulerPriorityMatchOnCore_bootCore_iff (st : SystemState) :
    schedulerPriorityMatchOnCore st bootCoreId ↔ schedulerPriorityMatch st := by
  unfold schedulerPriorityMatchOnCore schedulerPriorityMatch
  constructor
  all_goals
    intro h tid hMem
    have hSpec := h tid hMem
    unfold SystemState.getTcb? at *
    cases hObj : (st.objects[tid.toObjId]? : Option KernelObject) with
    | none => rw [hObj] at *; trivial
    | some obj => cases obj <;> (rw [hObj] at hSpec; simp_all)

theorem domainTimeRemainingPositiveOnCore_bootCore_iff (st : SystemState) :
    domainTimeRemainingPositiveOnCore st bootCoreId ↔ domainTimeRemainingPositive st := Iff.rfl

/-- Boot-core bridge for `currentBudgetPositiveOnCore`.  The per-core form
uses the typed `getTcb?` / `getSchedContext?` accessors; unfolding each
accessor exposes its underlying `match`-on-`objects[…]?`, and per-variant
case analysis on each lookup makes both sides reduce to the same body. -/
theorem currentBudgetPositiveOnCore_bootCore_iff (st : SystemState) :
    currentBudgetPositiveOnCore st bootCoreId ↔ currentBudgetPositive st := by
  unfold currentBudgetPositiveOnCore currentBudgetPositive
  cases st.scheduler.currentOnCore bootCoreId with
  | none => rfl
  | some tid =>
    unfold SystemState.getTcb?
    cases h : (st.objects[tid.toObjId]? : Option KernelObject) with
    | none => simp [h]
    | some obj =>
      cases obj with
      | tcb tcb =>
        simp [h]
        cases tcb.schedContextBinding with
        | unbound => rfl
        | bound scId =>
          unfold SystemState.getSchedContext?
          cases h2 : (st.objects[scId.toObjId]? : Option KernelObject) with
          | none => simp [h2]
          | some objSc => cases objSc <;> simp [h2]
        | donated scId _owner =>
          unfold SystemState.getSchedContext?
          cases h2 : (st.objects[scId.toObjId]? : Option KernelObject) with
          | none => simp [h2]
          | some objSc => cases objSc <;> simp [h2]
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ =>
        simp [h]

/-- Boot-core bridge for `budgetPositiveOnCore`.  Same pattern as
`currentBudgetPositiveOnCore_bootCore_iff` but under an outer ∀-tid binder. -/
theorem budgetPositiveOnCore_bootCore_iff (st : SystemState) :
    budgetPositiveOnCore st bootCoreId ↔ budgetPositive st := by
  unfold budgetPositiveOnCore budgetPositive
  apply forall_congr'; intro tid
  apply imp_congr_right; intro _hMem
  unfold SystemState.getTcb?
  cases h : (st.objects[tid.toObjId]? : Option KernelObject) with
  | none => simp [h]
  | some obj =>
    cases obj with
    | tcb tcb =>
      simp [h]
      cases tcb.schedContextBinding with
      | unbound => rfl
      | bound scId =>
        unfold SystemState.getSchedContext?
        cases h2 : (st.objects[scId.toObjId]? : Option KernelObject) with
        | none => simp [h2]
        | some objSc => cases objSc <;> simp [h2]
      | donated scId _owner =>
        unfold SystemState.getSchedContext?
        cases h2 : (st.objects[scId.toObjId]? : Option KernelObject) with
        | none => simp [h2]
        | some objSc => cases objSc <;> simp [h2]
    | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ =>
      simp [h]

theorem replenishmentPipelineOrderOnCore_bootCore_iff (st : SystemState) :
    replenishmentPipelineOrderOnCore st bootCoreId ↔ replenishmentPipelineOrder st := Iff.rfl

theorem replenishQueueValidOnCore_bootCore_iff (st : SystemState) :
    replenishQueueValidOnCore st bootCoreId ↔ replenishQueueValid st := Iff.rfl

/-- Boot-core bridge for `effectiveParamsMatchRunQueueOnCore`.  Same pattern
as `budgetPositiveOnCore_bootCore_iff` but the `.unbound` arm has a
non-`True` body (a `threadPriority[tid]?` equality). -/
theorem effectiveParamsMatchRunQueueOnCore_bootCore_iff (st : SystemState) :
    effectiveParamsMatchRunQueueOnCore st bootCoreId ↔ effectiveParamsMatchRunQueue st := by
  unfold effectiveParamsMatchRunQueueOnCore effectiveParamsMatchRunQueue
  apply forall_congr'; intro tid
  apply imp_congr_right; intro _hMem
  unfold SystemState.getTcb?
  cases h : (st.objects[tid.toObjId]? : Option KernelObject) with
  | none => simp [h]
  | some obj =>
    cases obj with
    | tcb tcb =>
      simp [h]
      cases tcb.schedContextBinding with
      | unbound => rfl
      | bound scId =>
        unfold SystemState.getSchedContext?
        cases h2 : (st.objects[scId.toObjId]? : Option KernelObject) with
        | none => simp [h2]
        | some objSc => cases objSc <;> simp [h2]
      | donated scId _owner =>
        unfold SystemState.getSchedContext?
        cases h2 : (st.objects[scId.toObjId]? : Option KernelObject) with
        | none => simp [h2]
        | some objSc => cases objSc <;> simp [h2]
    | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ =>
      simp [h]

-- ============================================================================
-- §3  Aggregate per-core invariant (SM4.C.29) + the SMP forall form (§5.6)
-- ============================================================================

/-- WS-SM SM4.C.29: the aggregate per-core scheduler invariant at core `c`.

This is the per-core slice of `schedulerInvariantBundleFull`: the same ten
conjuncts (the base triad + the five WS-F6/H6 structural invariants +
`schedulerPriorityMatch` + `domainTimeRemainingPositive`), each lifted to
core `c`.  The full bundle's one *system-wide* conjunct
(`domainScheduleEntriesPositive`, which reads the immutable, core-shared
`domainSchedule`) is core-independent and so is not parameterised by `c`;
it is restored in the `…_to_bundleFull_bootCore` bridge below.

The per-core form (`schedulerInvariant_perCore s c`) is the slice at a
specific core, used for proving preservation by a per-core operation; the
system-wide form (`schedulerInvariant_smp`, the `∀ c` aggregate below) is
used for cross-subsystem composition.  Both connect via
`schedulerInvariant_perCore_aggregateForall`. -/
def schedulerInvariant_perCore (st : SystemState) (c : CoreId) : Prop :=
  queueCurrentConsistentOnCore st.scheduler c ∧
  runQueueUniqueOnCore st.scheduler c ∧
  currentThreadValidOnCore st c ∧
  timeSlicePositiveOnCore st c ∧
  currentTimeSlicePositiveOnCore st c ∧
  edfCurrentHasEarliestDeadlineOnCore st c ∧
  contextMatchesCurrentOnCore st c ∧
  runnableThreadsAreTCBsOnCore st c ∧
  schedulerPriorityMatchOnCore st c ∧
  domainTimeRemainingPositiveOnCore st c ∧
  -- audit-pass-9 (PR #801, reviewer comment 2): include the per-core
  -- RunQueue.wellFormed structural invariant.  Pre-pass-9 the aggregate
  -- excluded this conjunct, meaning `schedulerInvariant_smp` could hold
  -- for a core whose RunQueue had inconsistent membership/priority
  -- indices.  Per implement-the-improvement, the conjunct is now first-
  -- class so SM5 consumers receive the structural guarantee directly.
  -- Appended at the END (not adjacent to `runQueueUniqueOnCore`) to
  -- minimise index shifts in the per-conjunct projection family — only
  -- `domainTimeRemainingPositiveOnCore`'s index shifts (h.2.2.2.2.2.2.2.2.2
  -- → h.2.2.2.2.2.2.2.2.2.1).
  runQueueOnCoreWellFormed st.scheduler c

/-- WS-SM SM4.C.29: the system-wide SMP scheduler invariant — the per-core
invariant holding on *every* core.  This is the form cross-subsystem
composition surfaces consume once the kernel is genuinely multi-core
(SM5+); at SM4.C only the boot core is non-idle, so the non-boot
conjuncts hold by the default-state lemmas below. -/
def schedulerInvariant_smp (st : SystemState) : Prop :=
  ∀ c : CoreId, schedulerInvariant_perCore st c

/-- WS-SM SM4.C.29 (plan §5.6): the per-core slices aggregate exactly to the
system-wide SMP invariant.  Holds by definition (`schedulerInvariant_smp`
*is* the `∀ c` form); stated as a named bridge so consumers can rewrite
between the slice-collecting form and the aggregate. -/
theorem schedulerInvariant_perCore_aggregateForall (st : SystemState) :
    (∀ c : CoreId, schedulerInvariant_perCore st c) ↔ schedulerInvariant_smp st := Iff.rfl

/-- Project a single core's slice out of the system-wide aggregate. -/
theorem schedulerInvariant_smp_at (st : SystemState) (c : CoreId)
    (h : schedulerInvariant_smp st) : schedulerInvariant_perCore st c := h c

-- Per-conjunct projections from the per-core aggregate (mirrors the
-- `schedulerInvariantBundleFull_to_*` projection family).

theorem schedulerInvariant_perCore_to_queueCurrentConsistent {st : SystemState} {c : CoreId}
    (h : schedulerInvariant_perCore st c) : queueCurrentConsistentOnCore st.scheduler c := h.1

theorem schedulerInvariant_perCore_to_runQueueUnique {st : SystemState} {c : CoreId}
    (h : schedulerInvariant_perCore st c) : runQueueUniqueOnCore st.scheduler c := h.2.1

theorem schedulerInvariant_perCore_to_currentThreadValid {st : SystemState} {c : CoreId}
    (h : schedulerInvariant_perCore st c) : currentThreadValidOnCore st c := h.2.2.1

theorem schedulerInvariant_perCore_to_timeSlicePositive {st : SystemState} {c : CoreId}
    (h : schedulerInvariant_perCore st c) : timeSlicePositiveOnCore st c := h.2.2.2.1

theorem schedulerInvariant_perCore_to_currentTimeSlicePositive {st : SystemState} {c : CoreId}
    (h : schedulerInvariant_perCore st c) : currentTimeSlicePositiveOnCore st c := h.2.2.2.2.1

theorem schedulerInvariant_perCore_to_edfCurrentHasEarliestDeadline {st : SystemState} {c : CoreId}
    (h : schedulerInvariant_perCore st c) : edfCurrentHasEarliestDeadlineOnCore st c :=
  h.2.2.2.2.2.1

theorem schedulerInvariant_perCore_to_contextMatchesCurrent {st : SystemState} {c : CoreId}
    (h : schedulerInvariant_perCore st c) : contextMatchesCurrentOnCore st c := h.2.2.2.2.2.2.1

theorem schedulerInvariant_perCore_to_runnableThreadsAreTCBs {st : SystemState} {c : CoreId}
    (h : schedulerInvariant_perCore st c) : runnableThreadsAreTCBsOnCore st c :=
  h.2.2.2.2.2.2.2.1

theorem schedulerInvariant_perCore_to_schedulerPriorityMatch {st : SystemState} {c : CoreId}
    (h : schedulerInvariant_perCore st c) : schedulerPriorityMatchOnCore st c :=
  h.2.2.2.2.2.2.2.2.1

theorem schedulerInvariant_perCore_to_domainTimeRemainingPositive {st : SystemState} {c : CoreId}
    (h : schedulerInvariant_perCore st c) : domainTimeRemainingPositiveOnCore st c :=
  h.2.2.2.2.2.2.2.2.2.1

/-- audit-pass-9 (PR #801, reviewer comment 2): per-core run-queue
well-formedness projection.  Extracts the new 11th conjunct of the
aggregate (appended at the end of the conjunction). -/
theorem schedulerInvariant_perCore_to_runQueueOnCoreWellFormed
    {st : SystemState} {c : CoreId} (h : schedulerInvariant_perCore st c) :
    runQueueOnCoreWellFormed st.scheduler c :=
  h.2.2.2.2.2.2.2.2.2.2

-- ============================================================================
-- §3.4  Base per-core invariant (mirroring `schedulerInvariantBundle`)
-- ============================================================================
--
-- Audit-pass-9 (PR #801, reviewer comment 3): adds the **base** per-core
-- aggregate corresponding to the 3-conjunct cross-subsystem
-- `schedulerInvariantBundle` (`queueCurrentConsistent ∧ runQueueUnique ∧
-- currentThreadValid`).  The §3 aggregate `schedulerInvariant_perCore`
-- mirrors the *Full* bundle (10 conjuncts); some operations — notably
-- `chooseThread` — only preserve the base triad, not the full bundle,
-- so without this aggregate their per-core preservation has no typed
-- form to carry the evidence through.  Per the implement-the-improvement
-- rule, the missing base aggregate is now first-class.

/-- WS-SM SM4.C audit-pass-9: the **base** per-core scheduler invariant
at core `c` — mirrors the 3-conjunct cross-subsystem
`schedulerInvariantBundle` (`queueCurrentConsistent ∧ runQueueUnique ∧
currentThreadValid`).  This is the per-core slice consumed by
operations whose single-core preservation establishes only the base
triad (notably `chooseThread`); SM5's per-core scheduler reaches the
full aggregate transitively via `schedule`. -/
def schedulerInvariantBase_perCore (st : SystemState) (c : CoreId) : Prop :=
  queueCurrentConsistentOnCore st.scheduler c ∧
  runQueueUniqueOnCore st.scheduler c ∧
  currentThreadValidOnCore st c

/-- WS-SM SM4.C audit-pass-9: the system-wide SMP base scheduler
invariant — the base per-core invariant holding on *every* core. -/
def schedulerInvariantBase_smp (st : SystemState) : Prop :=
  ∀ c : CoreId, schedulerInvariantBase_perCore st c

/-- Per-core slices aggregate exactly to the system-wide base form
(holds by definition; stated as a named bridge for rewriting). -/
theorem schedulerInvariantBase_perCore_aggregateForall (st : SystemState) :
    (∀ c : CoreId, schedulerInvariantBase_perCore st c) ↔
      schedulerInvariantBase_smp st := Iff.rfl

/-- Project a single core's base slice out of the SMP aggregate. -/
theorem schedulerInvariantBase_smp_at (st : SystemState) (c : CoreId)
    (h : schedulerInvariantBase_smp st) : schedulerInvariantBase_perCore st c := h c

-- Per-conjunct projections.

theorem schedulerInvariantBase_perCore_to_queueCurrentConsistent
    {st : SystemState} {c : CoreId} (h : schedulerInvariantBase_perCore st c) :
    queueCurrentConsistentOnCore st.scheduler c := h.1

theorem schedulerInvariantBase_perCore_to_runQueueUnique
    {st : SystemState} {c : CoreId} (h : schedulerInvariantBase_perCore st c) :
    runQueueUniqueOnCore st.scheduler c := h.2.1

theorem schedulerInvariantBase_perCore_to_currentThreadValid
    {st : SystemState} {c : CoreId} (h : schedulerInvariantBase_perCore st c) :
    currentThreadValidOnCore st c := h.2.2

/-- WS-SM SM4.C audit-pass-9: the single-core `schedulerInvariantBundle`
implies the **base** per-core aggregate at the boot core.  Two of three
conjuncts are `Iff.rfl` (queueCurrentConsistent, runQueueUnique); the
third (currentThreadValid) is bridged via `currentThreadValidOnCore_bootCore_iff`. -/
theorem schedulerInvariantBundle_to_perCoreBase_bootCore {st : SystemState}
    (h : schedulerInvariantBundle st) : schedulerInvariantBase_perCore st bootCoreId := by
  obtain ⟨hQCC, hRQU, hCTV⟩ := h
  exact ⟨hQCC, hRQU, (currentThreadValidOnCore_bootCore_iff st).mpr hCTV⟩

/-- WS-SM SM4.C audit-pass-9: converse — the base per-core aggregate at
the boot core reassembles the single-core bundle. -/
theorem schedulerInvariantBase_perCore_bootCore_to_bundle {st : SystemState}
    (h : schedulerInvariantBase_perCore st bootCoreId) : schedulerInvariantBundle st := by
  obtain ⟨hQCC, hRQU, hCTV⟩ := h
  exact ⟨hQCC, hRQU, (currentThreadValidOnCore_bootCore_iff st).mp hCTV⟩

/-- WS-SM SM4.C audit-pass-9: project the base per-core aggregate from
the full per-core aggregate.  Useful for SM5 callers that only need the
base triad — extract from the full evidence in one step. -/
theorem schedulerInvariant_perCore_to_base {st : SystemState} {c : CoreId}
    (h : schedulerInvariant_perCore st c) : schedulerInvariantBase_perCore st c :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- WS-SM SM4.C audit-pass-9: project the base SMP aggregate from the
full SMP aggregate. -/
theorem schedulerInvariant_smp_to_base {st : SystemState}
    (h : schedulerInvariant_smp st) : schedulerInvariantBase_smp st :=
  fun c => schedulerInvariant_perCore_to_base (h c)

-- ============================================================================
-- §3.5  Extended per-core invariant (mirroring `schedulerInvariantBundleExtended`)
-- ============================================================================

/-- WS-SM SM4.C: the **extended** per-core scheduler invariant at core `c`,
mirroring `schedulerInvariantBundleExtended`'s per-core slice.

Composes the base `schedulerInvariant_perCore` (the ten conjuncts of
`schedulerInvariantBundleFull`'s per-core slice) with the four
per-core conjuncts that Z4 / AE3-A added: `currentBudgetPositiveOnCore`,
`budgetPositiveOnCore`, `replenishQueueValidOnCore`,
`effectiveParamsMatchRunQueueOnCore`.  The remaining three Z4 conjuncts
(`schedContextsWellFormed`, `schedContextBindingConsistent`,
`boundThreadDomainConsistent`) are core-independent (they quantify
universally over the object store) and need no per-core form; they
participate in the `…_to_bundleExtended_bootCore` bridge as
separate arguments.

This is the aggregate SM5+ per-core scheduler will preserve once the
full Z4 invariant surface is migrated. -/
def schedulerInvariant_perCore_extended (st : SystemState) (c : CoreId) : Prop :=
  schedulerInvariant_perCore st c ∧
  currentBudgetPositiveOnCore st c ∧
  budgetPositiveOnCore st c ∧
  replenishQueueValidOnCore st c ∧
  effectiveParamsMatchRunQueueOnCore st c

/-- WS-SM SM4.C: the system-wide SMP extended scheduler invariant. -/
def schedulerInvariant_smp_extended (st : SystemState) : Prop :=
  ∀ c : CoreId, schedulerInvariant_perCore_extended st c

/-- WS-SM SM4.C: the extended per-core slice collects to the extended SMP
aggregate by definition. -/
theorem schedulerInvariant_perCore_extended_aggregateForall (st : SystemState) :
    (∀ c : CoreId, schedulerInvariant_perCore_extended st c) ↔
    schedulerInvariant_smp_extended st := Iff.rfl

/-- Project a single core's extended slice. -/
theorem schedulerInvariant_smp_extended_at (st : SystemState) (c : CoreId)
    (h : schedulerInvariant_smp_extended st) : schedulerInvariant_perCore_extended st c := h c

/-- Project the base (10-conjunct) per-core slice out of the extended form. -/
theorem schedulerInvariant_perCore_extended_to_base {st : SystemState} {c : CoreId}
    (h : schedulerInvariant_perCore_extended st c) : schedulerInvariant_perCore st c := h.1

theorem schedulerInvariant_perCore_extended_to_currentBudgetPositive
    {st : SystemState} {c : CoreId} (h : schedulerInvariant_perCore_extended st c) :
    currentBudgetPositiveOnCore st c := h.2.1

theorem schedulerInvariant_perCore_extended_to_budgetPositive
    {st : SystemState} {c : CoreId} (h : schedulerInvariant_perCore_extended st c) :
    budgetPositiveOnCore st c := h.2.2.1

theorem schedulerInvariant_perCore_extended_to_replenishQueueValid
    {st : SystemState} {c : CoreId} (h : schedulerInvariant_perCore_extended st c) :
    replenishQueueValidOnCore st c := h.2.2.2.1

theorem schedulerInvariant_perCore_extended_to_effectiveParamsMatchRunQueue
    {st : SystemState} {c : CoreId} (h : schedulerInvariant_perCore_extended st c) :
    effectiveParamsMatchRunQueueOnCore st c := h.2.2.2.2

-- ============================================================================
-- §4  Bridges to the live cross-subsystem bundle surface
-- ============================================================================
--
-- These ground the per-core aggregate in the existing single-core bundles:
-- the per-core invariant at the boot core IS the full bundle's per-core
-- slice (up to the §2 boot-core bridges).  Every preservation theorem
-- that today establishes `schedulerInvariantBundleFull` (or `…Extended`)
-- therefore also establishes `schedulerInvariant_perCore st bootCoreId`,
-- so SM5 inherits the entire single-core proof effort at the boot core.

/-- WS-SM SM4.C: the full single-core bundle implies the per-core invariant
at the boot core.  Each per-core conjunct at `bootCoreId` is provably
equivalent to the full bundle's corresponding conjunct (see §2 bridges);
the bundle's system-wide `domainScheduleEntriesPositive` conjunct is
dropped (it is not per-core). -/
theorem schedulerInvariantBundleFull_to_perCore_bootCore {st : SystemState}
    (h : schedulerInvariantBundleFull st)
    -- audit-pass-9 (PR #801, reviewer comment 2): explicit per-core
    -- run-queue well-formedness hypothesis.  `schedulerInvariantBundleFull`
    -- does NOT carry `RunQueue.wellFormed` (it is preserved at the
    -- per-API-call level but not aggregated at the bundle level), so the
    -- bridge into the new 11-conjunct per-core aggregate must take it
    -- explicitly.  Every existing per-op preservation theorem in
    -- `Scheduler/Operations/Preservation.lean` already requires
    -- `hwf : RunQueue.wellFormed (s.runQueueOnCore bootCoreId)` as input,
    -- so the obligation is no net new burden on callers — it surfaces
    -- the existing implicit precondition through the SM4.C aggregate.
    (hWf : RunQueue.wellFormed (st.scheduler.runQueueOnCore bootCoreId)) :
    schedulerInvariant_perCore st bootCoreId := by
  obtain ⟨⟨hQCC, hRQU, hCTV⟩, hTSP, hCTSP, hEDF, hCMC, hRAT, hSPM, hDTR, _hDSE⟩ := h
  refine ⟨hQCC, hRQU, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hDTR, hWf⟩
  · exact (currentThreadValidOnCore_bootCore_iff st).mpr hCTV
  · exact (timeSlicePositiveOnCore_bootCore_iff st).mpr hTSP
  · exact (currentTimeSlicePositiveOnCore_bootCore_iff st).mpr hCTSP
  · exact (edfCurrentHasEarliestDeadlineOnCore_bootCore_iff st).mpr hEDF
  · exact (contextMatchesCurrentOnCore_bootCore_iff st).mpr hCMC
  · exact (runnableThreadsAreTCBsOnCore_bootCore_iff st).mpr hRAT
  · exact (schedulerPriorityMatchOnCore_bootCore_iff st).mpr hSPM

/-- WS-SM SM4.C: the converse — the per-core invariant at the boot core
plus the system-wide `domainScheduleEntriesPositive` rebuilds the full
single-core bundle.  Confirms the per-core slice loses no boot-core
content. -/
theorem schedulerInvariant_perCore_bootCore_to_bundleFull {st : SystemState}
    (h : schedulerInvariant_perCore st bootCoreId)
    (hDSE : domainScheduleEntriesPositive st) : schedulerInvariantBundleFull st := by
  -- audit-pass-9: aggregate now has 11 conjuncts; the new wellFormed conjunct
  -- (`_hWf`) is discarded because `schedulerInvariantBundleFull` does not
  -- carry it.
  obtain ⟨hQCC, hRQU, hCTV, hTSP, hCTSP, hEDF, hCMC, hRAT, hSPM, hDTR, _hWf⟩ := h
  refine ⟨⟨hQCC, hRQU, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, hDTR, hDSE⟩
  · exact (currentThreadValidOnCore_bootCore_iff st).mp hCTV
  · exact (timeSlicePositiveOnCore_bootCore_iff st).mp hTSP
  · exact (currentTimeSlicePositiveOnCore_bootCore_iff st).mp hCTSP
  · exact (edfCurrentHasEarliestDeadlineOnCore_bootCore_iff st).mp hEDF
  · exact (contextMatchesCurrentOnCore_bootCore_iff st).mp hCMC
  · exact (runnableThreadsAreTCBsOnCore_bootCore_iff st).mp hRAT
  · exact (schedulerPriorityMatchOnCore_bootCore_iff st).mp hSPM

/-- WS-SM SM4.C: the extended single-core bundle (a superset of the full
bundle) likewise implies the **base** per-core invariant at the boot
core (projects through `.1` to the `Full` subset, which the previous
bridge handles). -/
theorem schedulerInvariantBundleExtended_to_perCore_bootCore {st : SystemState}
    (h : schedulerInvariantBundleExtended st)
    -- audit-pass-9: forwarded `hWf` for the audit-pass-9 11-conjunct aggregate
    (hWf : RunQueue.wellFormed (st.scheduler.runQueueOnCore bootCoreId)) :
    schedulerInvariant_perCore st bootCoreId :=
  schedulerInvariantBundleFull_to_perCore_bootCore h.1 hWf

/-- WS-SM SM4.C: the extended single-core bundle implies the **extended**
per-core invariant at the boot core.  This is the tight bridge: each of
`schedulerInvariantBundleExtended`'s seven extra Z4 conjuncts maps to its
per-core form via the §2 boot-core bridges (for the four genuinely
per-core conjuncts) or is dropped (for the three system-wide ones:
`schedContextsWellFormed`, `schedContextBindingConsistent`,
`boundThreadDomainConsistent`).  The dropped conjuncts are restored in
the converse bridge below. -/
theorem schedulerInvariantBundleExtended_to_perCore_extended_bootCore {st : SystemState}
    (h : schedulerInvariantBundleExtended st)
    -- audit-pass-9: forwarded `hWf` for the audit-pass-9 11-conjunct base
    -- aggregate that the extended aggregate composes via `.1`.
    (hWf : RunQueue.wellFormed (st.scheduler.runQueueOnCore bootCoreId)) :
    schedulerInvariant_perCore_extended st bootCoreId := by
  refine ⟨schedulerInvariantBundleFull_to_perCore_bootCore h.1 hWf, ?_, ?_, ?_, ?_⟩
  · exact (currentBudgetPositiveOnCore_bootCore_iff st).mpr
      (schedulerInvariantBundleExtended_to_currentBudgetPositive h)
  · exact (budgetPositiveOnCore_bootCore_iff st).mpr
      (schedulerInvariantBundleExtended_to_budgetPositive h)
  · exact (replenishQueueValidOnCore_bootCore_iff st).mpr
      (schedulerInvariantBundleExtended_to_replenishQueueValid h)
  · exact (effectiveParamsMatchRunQueueOnCore_bootCore_iff st).mpr
      (schedulerInvariantBundleExtended_to_effectiveParamsMatchRunQueue h)

/-- WS-SM SM4.C: the converse — the extended per-core invariant at the boot
core plus the three system-wide Z4 conjuncts (`schedContextsWellFormed`,
`schedContextBindingConsistent`, `boundThreadDomainConsistent`) plus
`domainScheduleEntriesPositive` rebuilds the full
`schedulerInvariantBundleExtended`.  Confirms the extended per-core slice
loses no boot-core content. -/
theorem schedulerInvariant_perCore_extended_bootCore_to_bundleExtended
    {st : SystemState}
    (h : schedulerInvariant_perCore_extended st bootCoreId)
    (hDSE : domainScheduleEntriesPositive st)
    (hSCWF : schedContextsWellFormed st)
    (hSCBC : schedContextBindingConsistent st)
    (hBTDC : boundThreadDomainConsistent st) :
    schedulerInvariantBundleExtended st := by
  obtain ⟨hBase, hCBP, hBP, hRQV, hEPM⟩ := h
  refine ⟨?_, ?_, ?_, hSCWF, ?_, hSCBC, ?_, hBTDC⟩
  · exact schedulerInvariant_perCore_bootCore_to_bundleFull hBase hDSE
  · exact (budgetPositiveOnCore_bootCore_iff st).mp hBP
  · exact (currentBudgetPositiveOnCore_bootCore_iff st).mp hCBP
  · exact (replenishQueueValidOnCore_bootCore_iff st).mp hRQV
  · exact (effectiveParamsMatchRunQueueOnCore_bootCore_iff st).mp hEPM

-- ============================================================================
-- §5  Default-state: every core satisfies the per-core invariant at boot
-- ============================================================================

/-- WS-SM SM4.C: the freshly-booted (empty) system satisfies the per-core
scheduler invariant on **every** core.  Each core's `current` is `none` and
each core's run queue is empty (`default_state_perCoreInitialized`), so every
conjunct holds vacuously except `domainTimeRemainingPositive`, which holds
because each core's `domainTimeRemaining` defaults to `5`.  This is the
per-core analog (over all of `allCores`) of the single-core
`default`-bundle lemmas, and the SM5 base case. -/
theorem default_schedulerInvariant_perCore (c : CoreId) :
    schedulerInvariant_perCore (default : SystemState) c := by
  have hCur : (default : SystemState).scheduler.currentOnCore c = none :=
    (default_state_perCoreInitialized c).1
  have hRQ : (default : SystemState).scheduler.runQueueOnCore c = RunQueue.empty :=
    (default_state_perCoreInitialized c).2.1
  have hDTR : (default : SystemState).scheduler.domainTimeRemainingOnCore c = 5 :=
    (default_state_perCoreInitialized c).2.2.2.2.1
  have hNotMemList : ∀ tid : SeLe4n.ThreadId,
      tid ∉ ((default : SystemState).scheduler.runQueueOnCore c).toList := by
    intro tid; rw [hRQ, RunQueue.toList_empty]; exact List.not_mem_nil
  have hNotMem : ∀ tid : SeLe4n.ThreadId,
      tid ∉ ((default : SystemState).scheduler.runQueueOnCore c) := by
    intro tid hMem
    exact hNotMemList tid ((RunQueue.mem_toList_iff_mem _ tid).2 hMem)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [queueCurrentConsistentOnCore, hCur]
  · simp only [runQueueUniqueOnCore, hRQ, RunQueue.toList_empty]; exact List.nodup_nil
  · simp only [currentThreadValidOnCore, hCur]
  · intro tid hMem; exact absurd hMem (hNotMemList tid)
  · simp only [currentTimeSlicePositiveOnCore, hCur]
  · simp only [edfCurrentHasEarliestDeadlineOnCore, hCur]
  · simp only [contextMatchesCurrentOnCore, hCur]
  · intro tid hMem; exact absurd hMem (hNotMemList tid)
  · intro tid hMem; exact absurd hMem (hNotMem tid)
  · simp only [domainTimeRemainingPositiveOnCore, hDTR]; decide
  · show RunQueue.wellFormed _
    rw [hRQ]; exact RunQueue.empty_wellFormed

/-- WS-SM SM4.C: the freshly-booted system satisfies the system-wide SMP
scheduler invariant — the per-core invariant on every core. -/
theorem default_schedulerInvariant_smp :
    schedulerInvariant_smp (default : SystemState) :=
  fun c => default_schedulerInvariant_perCore c

/-- WS-SM SM4.C audit-pass-9: the freshly-booted system satisfies the
**base** per-core scheduler invariant on every core (a 3-conjunct subset
of the full default). -/
theorem default_schedulerInvariantBase_perCore (c : CoreId) :
    schedulerInvariantBase_perCore (default : SystemState) c :=
  schedulerInvariant_perCore_to_base (default_schedulerInvariant_perCore c)

/-- WS-SM SM4.C audit-pass-9: the freshly-booted system satisfies the
system-wide SMP base scheduler invariant. -/
theorem default_schedulerInvariantBase_smp :
    schedulerInvariantBase_smp (default : SystemState) :=
  fun c => default_schedulerInvariantBase_perCore c

/-- WS-SM SM4.C: the freshly-booted system satisfies the **extended** per-core
scheduler invariant on every core.  Each Z4 conjunct holds vacuously on the
empty default state:
  * `currentBudgetPositiveOnCore` — vacuous via `currentOnCore c = none`;
  * `budgetPositiveOnCore` — vacuous via empty run queue;
  * `replenishQueueValidOnCore` — empty queue is sorted + size-consistent;
  * `effectiveParamsMatchRunQueueOnCore` — vacuous via empty run queue. -/
theorem default_schedulerInvariant_perCore_extended (c : CoreId) :
    schedulerInvariant_perCore_extended (default : SystemState) c := by
  have hCur : (default : SystemState).scheduler.currentOnCore c = none :=
    (default_state_perCoreInitialized c).1
  have hRQ : (default : SystemState).scheduler.runQueueOnCore c = RunQueue.empty :=
    (default_state_perCoreInitialized c).2.1
  have hRepl : (default : SystemState).scheduler.replenishQueueOnCore c =
        SeLe4n.Kernel.ReplenishQueue.empty :=
    (default_state_perCoreInitialized c).2.2.1
  have hNotMemList : ∀ tid : SeLe4n.ThreadId,
      tid ∉ ((default : SystemState).scheduler.runQueueOnCore c).toList := by
    intro tid; rw [hRQ, RunQueue.toList_empty]; exact List.not_mem_nil
  have hNotMem : ∀ tid : SeLe4n.ThreadId,
      tid ∉ ((default : SystemState).scheduler.runQueueOnCore c) := by
    intro tid hMem
    exact hNotMemList tid ((RunQueue.mem_toList_iff_mem _ tid).2 hMem)
  refine ⟨default_schedulerInvariant_perCore c, ?_, ?_, ?_, ?_⟩
  · simp only [currentBudgetPositiveOnCore, hCur]
  · intro tid hMem; exact absurd hMem (hNotMemList tid)
  · refine ⟨?_, ?_⟩
    · rw [hRepl]; exact empty_sorted
    · rw [hRepl]; exact empty_sizeConsistent
  · intro tid hMem; exact absurd hMem (hNotMem tid)

/-- WS-SM SM4.C: the freshly-booted system satisfies the system-wide
SMP extended invariant on every core. -/
theorem default_schedulerInvariant_smp_extended :
    schedulerInvariant_smp_extended (default : SystemState) :=
  fun c => default_schedulerInvariant_perCore_extended c

-- ============================================================================
-- §5.5  Per-conjunct frame lemmas (fine-grained SM5 reasoning)
-- ============================================================================
--
-- One frame lemma per per-core predicate, surfacing the minimal set of
-- reads each conjunct depends on.  These are the SM5-fine-grained
-- foundations on top of which the aggregate `_frame` in §6 is built.
-- Each closes via `unfold` + targeted rewrites under the hypotheses,
-- with `getTcb?_congr_objects` / `getSchedContext?_congr_objects`
-- bridging the typed-accessor reads through the `objects` hypothesis.

/-- Local helper: SchedContext congruence under object equality, mirroring
`getTcb?_congr_objects`.  Used by the SC-dependent per-conjunct frame
lemmas below. -/
private theorem getSchedContext?_congr_objects
    {st st' : SystemState} (h : st'.objects = st.objects)
    (scId : SeLe4n.SchedContextId) :
    st'.getSchedContext? scId = st.getSchedContext? scId := by
  unfold SystemState.getSchedContext?; rw [h]

theorem queueCurrentConsistentOnCore_frame {s s' : SchedulerState} {c : CoreId}
    (hCur : s'.currentOnCore c = s.currentOnCore c)
    (hRQ : s'.runQueueOnCore c = s.runQueueOnCore c) :
    queueCurrentConsistentOnCore s' c ↔ queueCurrentConsistentOnCore s c := by
  unfold queueCurrentConsistentOnCore; rw [hCur, hRQ]

theorem runQueueUniqueOnCore_frame {s s' : SchedulerState} {c : CoreId}
    (hRQ : s'.runQueueOnCore c = s.runQueueOnCore c) :
    runQueueUniqueOnCore s' c ↔ runQueueUniqueOnCore s c := by
  unfold runQueueUniqueOnCore; rw [hRQ]

theorem runQueueOnCoreWellFormed_frame {s s' : SchedulerState} {c : CoreId}
    (hRQ : s'.runQueueOnCore c = s.runQueueOnCore c) :
    runQueueOnCoreWellFormed s' c ↔ runQueueOnCoreWellFormed s c := by
  unfold runQueueOnCoreWellFormed; rw [hRQ]

theorem currentThreadValidOnCore_frame {st st' : SystemState} {c : CoreId}
    (hCur : st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c)
    (hObj : st'.objects = st.objects) :
    currentThreadValidOnCore st' c ↔ currentThreadValidOnCore st c := by
  have hTcb : ∀ tid, st'.getTcb? tid = st.getTcb? tid := getTcb?_congr_objects hObj
  unfold currentThreadValidOnCore; simp only [hCur, hTcb]

theorem currentThreadInActiveDomainOnCore_frame {st st' : SystemState} {c : CoreId}
    (hCur : st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c)
    (hAD : st'.scheduler.activeDomainOnCore c = st.scheduler.activeDomainOnCore c)
    (hObj : st'.objects = st.objects) :
    currentThreadInActiveDomainOnCore st' c ↔ currentThreadInActiveDomainOnCore st c := by
  have hTcb : ∀ tid, st'.getTcb? tid = st.getTcb? tid := getTcb?_congr_objects hObj
  unfold currentThreadInActiveDomainOnCore; simp only [hCur, hAD, hTcb]

theorem timeSlicePositiveOnCore_frame {st st' : SystemState} {c : CoreId}
    (hRQ : st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c)
    (hObj : st'.objects = st.objects) :
    timeSlicePositiveOnCore st' c ↔ timeSlicePositiveOnCore st c := by
  have hTcb : ∀ tid, st'.getTcb? tid = st.getTcb? tid := getTcb?_congr_objects hObj
  unfold timeSlicePositiveOnCore; simp only [hRQ, hTcb]

theorem currentTimeSlicePositiveOnCore_frame {st st' : SystemState} {c : CoreId}
    (hCur : st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c)
    (hObj : st'.objects = st.objects) :
    currentTimeSlicePositiveOnCore st' c ↔ currentTimeSlicePositiveOnCore st c := by
  have hTcb : ∀ tid, st'.getTcb? tid = st.getTcb? tid := getTcb?_congr_objects hObj
  unfold currentTimeSlicePositiveOnCore; simp only [hCur, hTcb]

theorem edfCurrentHasEarliestDeadlineOnCore_frame {st st' : SystemState} {c : CoreId}
    (hCur : st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c)
    (hRQ : st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c)
    (hObj : st'.objects = st.objects) :
    edfCurrentHasEarliestDeadlineOnCore st' c ↔ edfCurrentHasEarliestDeadlineOnCore st c := by
  have hTcb : ∀ tid, st'.getTcb? tid = st.getTcb? tid := getTcb?_congr_objects hObj
  unfold edfCurrentHasEarliestDeadlineOnCore; simp only [hCur, hRQ, hTcb]

theorem contextMatchesCurrentOnCore_frame {st st' : SystemState} {c : CoreId}
    (hCur : st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c)
    (hRegs : st'.machine.regs = st.machine.regs)
    (hObj : st'.objects = st.objects) :
    contextMatchesCurrentOnCore st' c ↔ contextMatchesCurrentOnCore st c := by
  have hTcb : ∀ tid, st'.getTcb? tid = st.getTcb? tid := getTcb?_congr_objects hObj
  unfold contextMatchesCurrentOnCore; simp only [hCur, hRegs, hTcb]

theorem runnableThreadsAreTCBsOnCore_frame {st st' : SystemState} {c : CoreId}
    (hRQ : st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c)
    (hObj : st'.objects = st.objects) :
    runnableThreadsAreTCBsOnCore st' c ↔ runnableThreadsAreTCBsOnCore st c := by
  have hTcb : ∀ tid, st'.getTcb? tid = st.getTcb? tid := getTcb?_congr_objects hObj
  unfold runnableThreadsAreTCBsOnCore; simp only [hRQ, hTcb]

theorem schedulerPriorityMatchOnCore_frame {st st' : SystemState} {c : CoreId}
    (hRQ : st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c)
    (hObj : st'.objects = st.objects) :
    schedulerPriorityMatchOnCore st' c ↔ schedulerPriorityMatchOnCore st c := by
  have hTcb : ∀ tid, st'.getTcb? tid = st.getTcb? tid := getTcb?_congr_objects hObj
  unfold schedulerPriorityMatchOnCore; simp only [hRQ, hTcb]

theorem domainTimeRemainingPositiveOnCore_frame {st st' : SystemState} {c : CoreId}
    (hDTR : st'.scheduler.domainTimeRemainingOnCore c = st.scheduler.domainTimeRemainingOnCore c) :
    domainTimeRemainingPositiveOnCore st' c ↔ domainTimeRemainingPositiveOnCore st c := by
  unfold domainTimeRemainingPositiveOnCore; rw [hDTR]

theorem currentBudgetPositiveOnCore_frame {st st' : SystemState} {c : CoreId}
    (hCur : st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c)
    (hObj : st'.objects = st.objects) :
    currentBudgetPositiveOnCore st' c ↔ currentBudgetPositiveOnCore st c := by
  have hTcb : ∀ tid, st'.getTcb? tid = st.getTcb? tid := getTcb?_congr_objects hObj
  have hSc : ∀ scId, st'.getSchedContext? scId = st.getSchedContext? scId :=
    getSchedContext?_congr_objects hObj
  unfold currentBudgetPositiveOnCore; simp only [hCur, hTcb, hSc]

theorem budgetPositiveOnCore_frame {st st' : SystemState} {c : CoreId}
    (hRQ : st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c)
    (hObj : st'.objects = st.objects) :
    budgetPositiveOnCore st' c ↔ budgetPositiveOnCore st c := by
  have hTcb : ∀ tid, st'.getTcb? tid = st.getTcb? tid := getTcb?_congr_objects hObj
  have hSc : ∀ scId, st'.getSchedContext? scId = st.getSchedContext? scId :=
    getSchedContext?_congr_objects hObj
  unfold budgetPositiveOnCore; simp only [hRQ, hTcb, hSc]

theorem replenishmentPipelineOrderOnCore_frame {st st' : SystemState} {c : CoreId}
    (hRepl : st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c)
    (hTimer : st'.machine.timer = st.machine.timer) :
    replenishmentPipelineOrderOnCore st' c ↔ replenishmentPipelineOrderOnCore st c := by
  unfold replenishmentPipelineOrderOnCore; rw [hRepl, hTimer]

theorem replenishQueueValidOnCore_frame {st st' : SystemState} {c : CoreId}
    (hRepl : st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c) :
    replenishQueueValidOnCore st' c ↔ replenishQueueValidOnCore st c := by
  unfold replenishQueueValidOnCore; rw [hRepl]

theorem effectiveParamsMatchRunQueueOnCore_frame {st st' : SystemState} {c : CoreId}
    (hRQ : st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c)
    (hObj : st'.objects = st.objects) :
    effectiveParamsMatchRunQueueOnCore st' c ↔ effectiveParamsMatchRunQueueOnCore st c := by
  have hTcb : ∀ tid, st'.getTcb? tid = st.getTcb? tid := getTcb?_congr_objects hObj
  have hSc : ∀ scId, st'.getSchedContext? scId = st.getSchedContext? scId :=
    getSchedContext?_congr_objects hObj
  unfold effectiveParamsMatchRunQueueOnCore; simp only [hRQ, hTcb, hSc]

-- ============================================================================
-- §6  Per-core frame lemma + cross-core independence (SM4.C.30)
-- ============================================================================

/-- WS-SM SM4.C: the per-core scheduler invariant at core `c` reads only
core `c`'s scheduler slots (`current` / `runQueue` / `domainTimeRemaining`),
the object store (via the typed `getTcb?` / `getSchedContext?`
accessors), and the machine register file.  Hence any modification that
frames those four reads preserves the invariant at core `c`.

This is the substantive cross-core-independence foundation: it is the lemma
that justifies why a per-core operation on core `c'` cannot disturb core
`c`'s invariant (the `…_pairwise` corollaries below instantiate it), and
why SM5 will need to re-prove a per-core operation's preservation only at
the core it actually writes. -/
theorem schedulerInvariant_perCore_frame {st st' : SystemState} {c : CoreId}
    (hCur  : st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c)
    (hRQ   : st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c)
    (hDTR  : st'.scheduler.domainTimeRemainingOnCore c = st.scheduler.domainTimeRemainingOnCore c)
    (hRegs : st'.machine.regs = st.machine.regs)
    (hObj  : st'.objects = st.objects) :
    schedulerInvariant_perCore st' c ↔ schedulerInvariant_perCore st c := by
  -- The aggregate predicates of §3 read only through `getTcb?` (not
  -- `getSchedContext?` — none of the 11 conjuncts in the aggregate look
  -- up SchedContext objects); `hTcb` is the only object-store congruence
  -- needed.  `hObj` flows in through `getTcb?_congr_objects`.  audit-pass-9:
  -- added `runQueueOnCoreWellFormed` to the simp set for the new conjunct.
  have hTcb : ∀ tid, st'.getTcb? tid = st.getTcb? tid := getTcb?_congr_objects hObj
  simp only [schedulerInvariant_perCore, queueCurrentConsistentOnCore, runQueueUniqueOnCore,
    currentThreadValidOnCore, timeSlicePositiveOnCore, currentTimeSlicePositiveOnCore,
    edfCurrentHasEarliestDeadlineOnCore, contextMatchesCurrentOnCore,
    runnableThreadsAreTCBsOnCore, schedulerPriorityMatchOnCore,
    domainTimeRemainingPositiveOnCore, runQueueOnCoreWellFormed,
    hCur, hRQ, hDTR, hRegs, hTcb]

/-- WS-SM SM4.C.30: writing a *different* core's current-thread slot leaves
this core's per-core invariant unchanged.  Instantiates the frame lemma via
the SM4.B store/load algebra (the cross-field frame + the `…_ne`
per-core-independence lemmas). -/
theorem schedulerInvariant_perCore_independent_of_setCurrentOnCore
    {st : SystemState} {c c' : CoreId} (hne : c ≠ c') (v : Option SeLe4n.ThreadId) :
    schedulerInvariant_perCore { st with scheduler := st.scheduler.setCurrentOnCore c' v } c ↔
    schedulerInvariant_perCore st c := by
  apply schedulerInvariant_perCore_frame <;> simp [Ne.symm hne]

/-- WS-SM SM4.C.30: writing a different core's run-queue slot leaves this
core's per-core invariant unchanged. -/
theorem schedulerInvariant_perCore_independent_of_setRunQueueOnCore
    {st : SystemState} {c c' : CoreId} (hne : c ≠ c') (v : RunQueue) :
    schedulerInvariant_perCore { st with scheduler := st.scheduler.setRunQueueOnCore c' v } c ↔
    schedulerInvariant_perCore st c := by
  apply schedulerInvariant_perCore_frame <;> simp [Ne.symm hne]

/-- WS-SM SM4.C.30: writing a different core's domain-time-remaining slot
leaves this core's per-core invariant unchanged. -/
theorem schedulerInvariant_perCore_independent_of_setDomainTimeRemainingOnCore
    {st : SystemState} {c c' : CoreId} (hne : c ≠ c') (v : Nat) :
    schedulerInvariant_perCore
      { st with scheduler := st.scheduler.setDomainTimeRemainingOnCore c' v } c ↔
    schedulerInvariant_perCore st c := by
  apply schedulerInvariant_perCore_frame <;> simp [Ne.symm hne]

/-- WS-SM SM4.C.30: writing any other core's replenish-queue slot leaves this
core's per-core invariant unchanged.  `schedulerInvariant_perCore` (mirroring
`schedulerInvariantBundleFull`) does not read `replenishQueueOnCore`, so the
independence holds for *any* target core (the `hne` hypothesis is retained for
API uniformity with the other independence corollaries). -/
theorem schedulerInvariant_perCore_independent_of_setReplenishQueueOnCore
    {st : SystemState} {c c' : CoreId} (_hne : c ≠ c') (v : ReplenishQueue) :
    schedulerInvariant_perCore
      { st with scheduler := st.scheduler.setReplenishQueueOnCore c' v } c ↔
    schedulerInvariant_perCore st c := by
  apply schedulerInvariant_perCore_frame <;> simp

/-- WS-SM SM4.C.30: writing any other core's active-domain slot leaves this
core's per-core invariant unchanged.  The aggregate does not read
`activeDomainOnCore` (only `currentThreadInActiveDomainOnCore` does, and that
is not in the `…Full`-mirroring aggregate), so the corollary holds for any
target core (`hne` retained for API uniformity). -/
theorem schedulerInvariant_perCore_independent_of_setActiveDomainOnCore
    {st : SystemState} {c c' : CoreId} (_hne : c ≠ c') (v : SeLe4n.DomainId) :
    schedulerInvariant_perCore
      { st with scheduler := st.scheduler.setActiveDomainOnCore c' v } c ↔
    schedulerInvariant_perCore st c := by
  apply schedulerInvariant_perCore_frame <;> simp

/-- WS-SM SM4.C.30: writing any other core's domain-schedule-index slot leaves
this core's per-core invariant unchanged.  The aggregate does not read
`domainScheduleIndexOnCore`, so the corollary holds for any target core. -/
theorem schedulerInvariant_perCore_independent_of_setDomainScheduleIndexOnCore
    {st : SystemState} {c c' : CoreId} (_hne : c ≠ c') (v : Nat) :
    schedulerInvariant_perCore
      { st with scheduler := st.scheduler.setDomainScheduleIndexOnCore c' v } c ↔
    schedulerInvariant_perCore st c := by
  apply schedulerInvariant_perCore_frame <;> simp

/-- WS-SM SM4.C.30: writing any other core's last-timeout-errors slot leaves
this core's per-core invariant unchanged.  The aggregate does not read
`lastTimeoutErrorsOnCore` (only used diagnostically), so the corollary holds
for any target core. -/
theorem schedulerInvariant_perCore_independent_of_setLastTimeoutErrorsOnCore
    {st : SystemState} {c c' : CoreId} (_hne : c ≠ c')
    (v : List (SeLe4n.ThreadId × KernelError)) :
    schedulerInvariant_perCore
      { st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c' v } c ↔
    schedulerInvariant_perCore st c := by
  apply schedulerInvariant_perCore_frame <;> simp

/-- WS-SM SM4.C.30 (plan §5.6): **per-core pairwise independence**.  For two
distinct cores `c₁ ≠ c₂`, simultaneously overwriting *all three* of core
`c₂`'s slots that the per-core invariant reads (`current`, `runQueue`,
`domainTimeRemaining`) leaves core `c₁`'s per-core invariant unchanged.

This is the substantive realisation of the plan's documentation-only
`P s c₁ ↔ P s c₁` sketch: core `c₂`'s scheduler state genuinely does not
appear in core `c₁`'s invariant.  The `Vector` per-core indexing (SM4.B) is
exactly what delivers this independence, and it is the property SM5 relies
on to reason about each core's scheduler in isolation. -/
theorem schedulerInvariant_perCore_pairwise
    {st : SystemState} {c₁ c₂ : CoreId} (hne : c₁ ≠ c₂)
    (vc : Option SeLe4n.ThreadId) (vrq : RunQueue) (vdtr : Nat) :
    schedulerInvariant_perCore
      { st with scheduler :=
        ((st.scheduler.setCurrentOnCore c₂ vc).setRunQueueOnCore c₂ vrq).setDomainTimeRemainingOnCore c₂ vdtr }
      c₁ ↔
    schedulerInvariant_perCore st c₁ := by
  apply schedulerInvariant_perCore_frame <;> simp [Ne.symm hne]

-- ============================================================================
-- §7  Idle-core frame + SMP-preservation skeleton (the SM5 bridge)
-- ============================================================================

/-- WS-SM SM4.C: a frame variant for an **idle** core — one whose current
thread is `none` on both states.  Because all five current-dependent
conjuncts are then vacuously `True`, this frame needs **no** agreement on
the machine register file (`contextMatchesCurrent` never reads it when the
core is idle).  It depends only on the core's run queue, domain-time, and
the object store.

This is the SM5-critical case: a boot-core operation that *changes the
register file* (e.g. `schedule`'s inline context restore) still preserves
every idle core's per-core invariant, since an idle core's register
context is irrelevant to its (vacuous) invariant. -/
theorem schedulerInvariant_perCore_frame_idle {st st' : SystemState} {c : CoreId}
    (hCurNone' : st'.scheduler.currentOnCore c = none)
    (hCurNone  : st.scheduler.currentOnCore c = none)
    (hRQ  : st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c)
    (hDTR : st'.scheduler.domainTimeRemainingOnCore c = st.scheduler.domainTimeRemainingOnCore c)
    (hObj : st'.objects = st.objects) :
    schedulerInvariant_perCore st' c ↔ schedulerInvariant_perCore st c := by
  -- audit-pass-9: added `runQueueOnCoreWellFormed` to the simp set
  -- (the new 11th conjunct of the aggregate; covered by the `hRQ` frame).
  have hTcb : ∀ tid, st'.getTcb? tid = st.getTcb? tid := getTcb?_congr_objects hObj
  simp only [schedulerInvariant_perCore, queueCurrentConsistentOnCore, runQueueUniqueOnCore,
    currentThreadValidOnCore, timeSlicePositiveOnCore, currentTimeSlicePositiveOnCore,
    edfCurrentHasEarliestDeadlineOnCore, contextMatchesCurrentOnCore,
    runnableThreadsAreTCBsOnCore, schedulerPriorityMatchOnCore,
    domainTimeRemainingPositiveOnCore, runQueueOnCoreWellFormed,
    hCurNone', hCurNone, hRQ, hDTR, hTcb]

/-- WS-SM SM4.C: the **single-core-preservation-lifts-to-SMP** skeleton.

Given that the per-core invariant held on every core pre-transition
(`hPre`), a transition `st → st'` preserves the *system-wide* SMP invariant
provided:
  * the boot core's per-core invariant is re-established (`hBoot` — exactly
    what every existing single-core preservation theorem proves, via the
    `schedulerInvariantBundleFull_to_perCore_bootCore` bridge), and
  * every non-boot core stays idle and has its run queue / domain-time /
    the object store framed (true of a single-core operation, which only
    writes the boot core's slots and, for `schedule`, only the boot core's
    register context).

This is the migration's payoff: SM5 re-proves a per-core operation's
preservation **only at the core it writes**; every other core is discharged
by `schedulerInvariant_perCore_frame_idle`. -/
theorem schedulerInvariant_smp_of_bootCore_and_idle_frame {st st' : SystemState}
    (hPre : schedulerInvariant_smp st)
    (hBoot : schedulerInvariant_perCore st' bootCoreId)
    (hIdle' : ∀ c, c ≠ bootCoreId → st'.scheduler.currentOnCore c = none)
    (hIdle  : ∀ c, c ≠ bootCoreId → st.scheduler.currentOnCore c = none)
    (hFrameRQ  : ∀ c, c ≠ bootCoreId →
      st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c)
    (hFrameDTR : ∀ c, c ≠ bootCoreId →
      st'.scheduler.domainTimeRemainingOnCore c = st.scheduler.domainTimeRemainingOnCore c)
    (hFrameObj : st'.objects = st.objects) :
    schedulerInvariant_smp st' := by
  intro c
  by_cases hc : c = bootCoreId
  · subst hc; exact hBoot
  · exact (schedulerInvariant_perCore_frame_idle (hIdle' c hc) (hIdle c hc)
      (hFrameRQ c hc) (hFrameDTR c hc) hFrameObj).mpr (hPre c)

-- ============================================================================
-- §8  Extended-aggregate frame, independence, and SMP-preservation skeleton
-- ============================================================================

/-- WS-SM SM4.C: aggregate frame lemma for `schedulerInvariant_perCore_extended`.
The extended aggregate reads everything the base does (current, runQueue,
domainTimeRemaining, objects, machine.regs) plus core `c`'s replenish queue. -/
theorem schedulerInvariant_perCore_extended_frame {st st' : SystemState} {c : CoreId}
    (hCur  : st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c)
    (hRQ   : st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c)
    (hDTR  : st'.scheduler.domainTimeRemainingOnCore c = st.scheduler.domainTimeRemainingOnCore c)
    (hRepl : st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c)
    (hRegs : st'.machine.regs = st.machine.regs)
    (hObj  : st'.objects = st.objects) :
    schedulerInvariant_perCore_extended st' c ↔ schedulerInvariant_perCore_extended st c := by
  unfold schedulerInvariant_perCore_extended
  rw [schedulerInvariant_perCore_frame hCur hRQ hDTR hRegs hObj]
  rw [currentBudgetPositiveOnCore_frame hCur hObj]
  rw [budgetPositiveOnCore_frame hRQ hObj]
  rw [replenishQueueValidOnCore_frame hRepl]
  rw [effectiveParamsMatchRunQueueOnCore_frame hRQ hObj]

/-- WS-SM SM4.C: idle-core variant of the extended frame.  When core `c` is
idle on both states, the five current-dependent base conjuncts are vacuous
(so register-file agreement is unnecessary) AND `currentBudgetPositive` is
likewise vacuous; we still need the run-queue/domain-time/replenish-queue/
object-store agreement for the runnable-quantified conjuncts. -/
theorem schedulerInvariant_perCore_extended_frame_idle {st st' : SystemState} {c : CoreId}
    (hCurNone' : st'.scheduler.currentOnCore c = none)
    (hCurNone  : st.scheduler.currentOnCore c = none)
    (hRQ   : st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c)
    (hDTR  : st'.scheduler.domainTimeRemainingOnCore c = st.scheduler.domainTimeRemainingOnCore c)
    (hRepl : st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c)
    (hObj  : st'.objects = st.objects) :
    schedulerInvariant_perCore_extended st' c ↔ schedulerInvariant_perCore_extended st c := by
  unfold schedulerInvariant_perCore_extended
  rw [schedulerInvariant_perCore_frame_idle hCurNone' hCurNone hRQ hDTR hObj]
  rw [currentBudgetPositiveOnCore_frame (hCurNone'.trans hCurNone.symm) hObj]
  rw [budgetPositiveOnCore_frame hRQ hObj]
  rw [replenishQueueValidOnCore_frame hRepl]
  rw [effectiveParamsMatchRunQueueOnCore_frame hRQ hObj]

/-- WS-SM SM4.C.30: extended-aggregate independence — writing core c'`s
slots leaves core c's extended per-core invariant unchanged (c ≠ c').
The composed-write form: all four fields that distinguish extended from
base are c-indexed, so writing any of c'`s setters is invariant-preserving
at c. -/
theorem schedulerInvariant_perCore_extended_pairwise
    {st : SystemState} {c₁ c₂ : CoreId} (hne : c₁ ≠ c₂)
    (vc : Option SeLe4n.ThreadId) (vrq : RunQueue) (vdtr : Nat)
    (vrepl : ReplenishQueue) :
    schedulerInvariant_perCore_extended
      { st with scheduler :=
        (((st.scheduler.setCurrentOnCore c₂ vc).setRunQueueOnCore c₂ vrq).setDomainTimeRemainingOnCore
          c₂ vdtr).setReplenishQueueOnCore c₂ vrepl }
      c₁ ↔
    schedulerInvariant_perCore_extended st c₁ := by
  apply schedulerInvariant_perCore_extended_frame <;> simp [Ne.symm hne]

/-- WS-SM SM4.C: SMP-preservation skeleton for the extended invariant — the
single-core-extended-preservation-lifts-to-extended-SMP composition.
Mirror of `schedulerInvariant_smp_of_bootCore_and_idle_frame` for the
extended aggregate, adding a `hFrameRepl` hypothesis. -/
theorem schedulerInvariant_smp_extended_of_bootCore_and_idle_frame {st st' : SystemState}
    (hPre : schedulerInvariant_smp_extended st)
    (hBoot : schedulerInvariant_perCore_extended st' bootCoreId)
    (hIdle' : ∀ c, c ≠ bootCoreId → st'.scheduler.currentOnCore c = none)
    (hIdle  : ∀ c, c ≠ bootCoreId → st.scheduler.currentOnCore c = none)
    (hFrameRQ  : ∀ c, c ≠ bootCoreId →
      st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c)
    (hFrameDTR : ∀ c, c ≠ bootCoreId →
      st'.scheduler.domainTimeRemainingOnCore c = st.scheduler.domainTimeRemainingOnCore c)
    (hFrameRepl : ∀ c, c ≠ bootCoreId →
      st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c)
    (hFrameObj : st'.objects = st.objects) :
    schedulerInvariant_smp_extended st' := by
  intro c
  by_cases hc : c = bootCoreId
  · subst hc; exact hBoot
  · exact (schedulerInvariant_perCore_extended_frame_idle (hIdle' c hc) (hIdle c hc)
      (hFrameRQ c hc) (hFrameDTR c hc) (hFrameRepl c hc) hFrameObj).mpr (hPre c)

-- ============================================================================
-- §9  Cross-subsystem per-core predicates (plan §5.6)
-- ============================================================================
--
-- Per plan §5.6, the per-core scheduler invariant aggregate ALSO names
-- three cross-subsystem predicates: `schedContextRunQueueConsistent_perCore`
-- (the per-core analog of `CrossSubsystem.schedContextRunQueueConsistent`),
-- `priorityInheritance_perCore` (the per-core analog of
-- `PriorityInheritance.blockingAcyclic`), and a new
-- `activeDomainOnCore_isInDomainSchedule` (no single-core counterpart).
-- These cross the SM4.C / SM4.D boundary slightly (since
-- `schedContextRunQueueConsistent` lives in `CrossSubsystem.lean`), but
-- including them here matches the plan literally and gives SM5 a single
-- composed per-core invariant to preserve.

/-- SM4.C (plan §5.6): per-core form of
`CrossSubsystem.schedContextRunQueueConsistent`.  For every thread in
core `c`'s run queue, if the thread is bound to a SchedContext, the SC
exists in the object store with positive `budgetRemaining`. -/
def schedContextRunQueueConsistent_perCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ (tid : SeLe4n.ThreadId),
    tid ∈ (st.scheduler.runQueueOnCore c).toList →
    ∀ (tcb : TCB),
      st.getTcb? tid = some tcb →
      ∀ scId, tcb.schedContextBinding.scId? = some scId →
        ∃ sc, st.getSchedContext? scId = some sc ∧
          sc.budgetRemaining.val > 0

/-- SM4.C (plan §5.6): per-core form of
`PriorityInheritance.blockingAcyclic`.  The blocking graph is built from
the entire object store (cross-core IPC means any thread can block on
any endpoint), so this predicate is **genuinely system-wide**: the per-
core form is the same global blocking-acyclic property, exposed under a
`(c : CoreId)`-parameterised signature for compositional convenience.

This is honest about the predicate's *zero* core dependence (the body
deliberately ignores `_c`); when SM5+ introduces genuinely per-core
blocking sub-graphs, this signature is the migration seam. -/
def priorityInheritance_perCore (st : SystemState) (_c : CoreId) : Prop :=
  PriorityInheritance.blockingAcyclic st

/-- SM4.C (plan §5.6): the active domain on core `c` is one of the domains
listed in the (system-wide) domain schedule.  Plan-named new predicate;
no single-core counterpart in `Scheduler/Invariant.lean`.

When `domainSchedule = []`, the kernel runs in single-domain mode and
any active domain value is admissible (the left disjunct).  Otherwise,
the active domain must appear as the `.domain` field of some schedule
entry. -/
def activeDomainOnCore_isInDomainSchedule (st : SystemState) (c : CoreId) : Prop :=
  st.scheduler.domainSchedule = [] ∨
  ∃ e ∈ st.scheduler.domainSchedule, e.domain = st.scheduler.activeDomainOnCore c

-- ============================================================================
-- §9.1  Boot-core bridges for the cross-subsystem per-core predicates
-- ============================================================================

/-- WS-SM SM4.C: at the boot core, `schedContextRunQueueConsistent_perCore` is
provably equivalent to the existing single-core
`CrossSubsystem.schedContextRunQueueConsistent`.  Closes via `simp only`
with the typed-accessor `_eq_some_iff` lemmas, which rewrite each
`getTcb? = some` / `getSchedContext? = some` into the raw-`objects[…]?`
form that the single-core predicate uses. -/
theorem schedContextRunQueueConsistent_perCore_bootCore_iff (st : SystemState) :
    schedContextRunQueueConsistent_perCore st bootCoreId ↔
    schedContextRunQueueConsistent st := by
  unfold schedContextRunQueueConsistent_perCore schedContextRunQueueConsistent
  simp only [SystemState.getTcb?_eq_some_iff, SystemState.getSchedContext?_eq_some_iff]

/-- WS-SM SM4.C: at any core, `priorityInheritance_perCore` is the global
`PriorityInheritance.blockingAcyclic`.  This holds by definition (the
per-core form ignores its `c` parameter), surfaced as a named bridge for
consumers reasoning at the global vs per-core abstraction. -/
theorem priorityInheritance_perCore_iff (st : SystemState) (c : CoreId) :
    priorityInheritance_perCore st c ↔ PriorityInheritance.blockingAcyclic st := Iff.rfl

-- ============================================================================
-- §9.2  Default-state for the cross-subsystem per-core predicates
-- ============================================================================

/-- The freshly-booted system satisfies `schedContextRunQueueConsistent_perCore`
on every core (vacuous via empty run queue). -/
theorem default_schedContextRunQueueConsistent_perCore (c : CoreId) :
    schedContextRunQueueConsistent_perCore (default : SystemState) c := by
  intro tid hMem
  have hRQ : (default : SystemState).scheduler.runQueueOnCore c = RunQueue.empty :=
    (default_state_perCoreInitialized c).2.1
  rw [hRQ, RunQueue.toList_empty] at hMem
  exact absurd hMem List.not_mem_nil

/-- The freshly-booted system satisfies `priorityInheritance_perCore` on every
core (the empty object store has no blocking edges, so `blockingAcyclic`
holds vacuously — same proof as `CrossSubsystem.default_blockingAcyclic`
which is established by `default_crossSubsystemInvariant`). -/
theorem default_priorityInheritance_perCore (c : CoreId) :
    priorityInheritance_perCore (default : SystemState) c :=
  (crossSubsystemInvariant_to_blockingAcyclic _ default_crossSubsystemInvariant)

/-- The freshly-booted system satisfies `activeDomainOnCore_isInDomainSchedule`
on every core: the default state's `domainSchedule = []` discharges the
left disjunct. -/
theorem default_activeDomainOnCore_isInDomainSchedule (c : CoreId) :
    activeDomainOnCore_isInDomainSchedule (default : SystemState) c := by
  left
  -- `(default : SystemState).scheduler.domainSchedule` reduces to `[]` by
  -- the SchedulerState default-field discipline.
  rfl

-- ============================================================================
-- §9.3  Per-conjunct frame lemmas for the cross-subsystem per-core predicates
-- ============================================================================

/-- Frame lemma for `schedContextRunQueueConsistent_perCore`: depends on core
`c`'s run queue plus the object store. -/
theorem schedContextRunQueueConsistent_perCore_frame {st st' : SystemState} {c : CoreId}
    (hRQ : st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c)
    (hObj : st'.objects = st.objects) :
    schedContextRunQueueConsistent_perCore st' c ↔
    schedContextRunQueueConsistent_perCore st c := by
  have hTcb : ∀ tid, st'.getTcb? tid = st.getTcb? tid := getTcb?_congr_objects hObj
  have hSc : ∀ scId, st'.getSchedContext? scId = st.getSchedContext? scId :=
    getSchedContext?_congr_objects hObj
  unfold schedContextRunQueueConsistent_perCore
  simp only [hRQ, hTcb, hSc]

/-- Private helper: `blockingChain` is congruent under `objects` equality
for any fuel.  Proved by induction on fuel — the recursion only reads
`st.objects[…]?`, so `objects` equality propagates structurally through
the chain walk.  Used by `priorityInheritance_perCore_frame`. -/
private theorem blockingChain_objects_congr
    {st st' : SystemState} (hObj : st'.objects = st.objects)
    (tid : SeLe4n.ThreadId) (fuel : Nat) :
    PriorityInheritance.blockingChain st' tid fuel =
    PriorityInheritance.blockingChain st tid fuel := by
  induction fuel generalizing tid with
  | zero => rfl
  | succ fuel' ih =>
    unfold PriorityInheritance.blockingChain
    have hLookup : st'.objects[tid.toObjId]? = st.objects[tid.toObjId]? := by rw [hObj]
    cases h : (st.objects[tid.toObjId]? : Option KernelObject) with
    | none => simp [hLookup, h]
    | some obj =>
      cases obj with
      | tcb tcb =>
        cases hIpc : tcb.ipcState with
        | ready => simp [hLookup, h, hIpc]
        | blockedOnSend _ => simp [hLookup, h, hIpc]
        | blockedOnReceive _ => simp [hLookup, h, hIpc]
        | blockedOnNotification _ => simp [hLookup, h, hIpc]
        | blockedOnReply _ srv =>
          cases srv with
          | none => simp [hLookup, h, hIpc]
          | some server =>
            simp only [hLookup, h, hIpc]
            exact congrArg (server :: ·) (ih server)
        | blockedOnCall _ => simp [hLookup, h, hIpc]
      | endpoint _ => simp [hLookup, h]
      | notification _ => simp [hLookup, h]
      | cnode _ => simp [hLookup, h]
      | vspaceRoot _ => simp [hLookup, h]
      | untyped _ => simp [hLookup, h]
      | schedContext _ => simp [hLookup, h]

/-- Frame lemma for `priorityInheritance_perCore`: depends on the entire
object store *and* `objectIndex` (the latter feeds `blockingChain`'s
default fuel).  Proved substantively via `blockingChain_objects_congr`
(structural induction on fuel — the chain walk only reads
`st.objects[…]?`) plus the `objectIndex.length` equality derived from
`hIdx`.  Both hypotheses are genuinely required: the chain walk
recurses on `st.objects` (handled by `hObj`) AND its default fuel
`st.objectIndex.length` comes from `st.objectIndex` (handled by
`hIdx`).  SM5 operations that preserve both — which includes every
scheduler operation that doesn't insert/remove objects — discharge
both directly. -/
theorem priorityInheritance_perCore_frame {st st' : SystemState} {c : CoreId}
    (hObj : st'.objects = st.objects)
    (hIdx : st'.objectIndex = st.objectIndex) :
    priorityInheritance_perCore st' c ↔ priorityInheritance_perCore st c := by
  unfold priorityInheritance_perCore PriorityInheritance.blockingAcyclic
  have h_len : st'.objectIndex.length = st.objectIndex.length := by rw [hIdx]
  have hChain : ∀ tid : SeLe4n.ThreadId,
      PriorityInheritance.blockingChain st' tid st'.objectIndex.length =
      PriorityInheritance.blockingChain st tid st.objectIndex.length := by
    intro tid
    rw [blockingChain_objects_congr hObj tid st'.objectIndex.length, h_len]
  constructor
  · intro hAcy tid hMem
    exact hAcy tid (hChain tid ▸ hMem)
  · intro hAcy tid hMem
    exact hAcy tid ((hChain tid).symm ▸ hMem)

/-- Frame lemma for `activeDomainOnCore_isInDomainSchedule`: depends on core
`c`'s active-domain slot and the system-wide `domainSchedule`. -/
theorem activeDomainOnCore_isInDomainSchedule_frame {st st' : SystemState} {c : CoreId}
    (hAD : st'.scheduler.activeDomainOnCore c = st.scheduler.activeDomainOnCore c)
    (hDS : st'.scheduler.domainSchedule = st.scheduler.domainSchedule) :
    activeDomainOnCore_isInDomainSchedule st' c ↔
    activeDomainOnCore_isInDomainSchedule st c := by
  unfold activeDomainOnCore_isInDomainSchedule; rw [hAD, hDS]

-- ============================================================================
-- §10  Cross-subsystem per-core aggregate + bridges
-- ============================================================================

/-- WS-SM SM4.C (plan §5.6, comprehensive): the **cross-subsystem** per-core
scheduler invariant.  Composes the extended per-core aggregate (§3.5) with
the three plan §5.6 cross-subsystem conjuncts.  This is the most complete
per-core scheduler invariant in SM4.C; SM5 will preserve this in its
per-core scheduler operations. -/
def schedulerInvariant_perCore_crossSubsystem (st : SystemState) (c : CoreId) : Prop :=
  schedulerInvariant_perCore_extended st c ∧
  schedContextRunQueueConsistent_perCore st c ∧
  priorityInheritance_perCore st c ∧
  activeDomainOnCore_isInDomainSchedule st c

/-- System-wide SMP form of the cross-subsystem per-core invariant. -/
def schedulerInvariant_smp_crossSubsystem (st : SystemState) : Prop :=
  ∀ c : CoreId, schedulerInvariant_perCore_crossSubsystem st c

/-- The cross-subsystem per-core slices aggregate to the system-wide form. -/
theorem schedulerInvariant_perCore_crossSubsystem_aggregateForall (st : SystemState) :
    (∀ c : CoreId, schedulerInvariant_perCore_crossSubsystem st c) ↔
    schedulerInvariant_smp_crossSubsystem st := Iff.rfl

theorem schedulerInvariant_smp_crossSubsystem_at (st : SystemState) (c : CoreId)
    (h : schedulerInvariant_smp_crossSubsystem st) :
    schedulerInvariant_perCore_crossSubsystem st c := h c

-- Per-conjunct projections from the cross-subsystem aggregate.

theorem schedulerInvariant_perCore_crossSubsystem_to_extended {st : SystemState} {c : CoreId}
    (h : schedulerInvariant_perCore_crossSubsystem st c) :
    schedulerInvariant_perCore_extended st c := h.1

theorem schedulerInvariant_perCore_crossSubsystem_to_schedContextRunQueueConsistent
    {st : SystemState} {c : CoreId} (h : schedulerInvariant_perCore_crossSubsystem st c) :
    schedContextRunQueueConsistent_perCore st c := h.2.1

theorem schedulerInvariant_perCore_crossSubsystem_to_priorityInheritance
    {st : SystemState} {c : CoreId} (h : schedulerInvariant_perCore_crossSubsystem st c) :
    priorityInheritance_perCore st c := h.2.2.1

theorem schedulerInvariant_perCore_crossSubsystem_to_activeDomainOnCore_isInDomainSchedule
    {st : SystemState} {c : CoreId} (h : schedulerInvariant_perCore_crossSubsystem st c) :
    activeDomainOnCore_isInDomainSchedule st c := h.2.2.2

/-- WS-SM SM4.C: the cross-subsystem per-core invariant at the boot core
follows from `schedulerInvariantBundleExtended` + `crossSubsystemInvariant`
+ the new `activeDomainOnCore_isInDomainSchedule` (which has no single-core
counterpart; it is fresh content per plan §5.6 and must be supplied
separately). -/
theorem crossSubsystemInvariant_to_perCore_crossSubsystem_bootCore {st : SystemState}
    (hExt : schedulerInvariantBundleExtended st)
    (hCSI : crossSubsystemInvariant st)
    (hADS : activeDomainOnCore_isInDomainSchedule st bootCoreId)
    -- audit-pass-9: forwarded `hWf` for the audit-pass-9 wellFormed
    -- conjunct in the base aggregate the extended one composes.
    (hWf : RunQueue.wellFormed (st.scheduler.runQueueOnCore bootCoreId)) :
    schedulerInvariant_perCore_crossSubsystem st bootCoreId := by
  refine ⟨schedulerInvariantBundleExtended_to_perCore_extended_bootCore hExt hWf, ?_, ?_, hADS⟩
  · exact (schedContextRunQueueConsistent_perCore_bootCore_iff st).mpr
      (crossSubsystemInvariant_to_schedContextRunQueueConsistent _ hCSI)
  · exact (priorityInheritance_perCore_iff st bootCoreId).mpr
      (crossSubsystemInvariant_to_blockingAcyclic _ hCSI)

/-- The freshly-booted system satisfies the cross-subsystem per-core invariant
on every core (composes the extended and the 3 cross-subsystem defaults). -/
theorem default_schedulerInvariant_perCore_crossSubsystem (c : CoreId) :
    schedulerInvariant_perCore_crossSubsystem (default : SystemState) c :=
  ⟨default_schedulerInvariant_perCore_extended c,
   default_schedContextRunQueueConsistent_perCore c,
   default_priorityInheritance_perCore c,
   default_activeDomainOnCore_isInDomainSchedule c⟩

/-- The freshly-booted system satisfies the system-wide SMP cross-subsystem
invariant. -/
theorem default_schedulerInvariant_smp_crossSubsystem :
    schedulerInvariant_smp_crossSubsystem (default : SystemState) :=
  fun c => default_schedulerInvariant_perCore_crossSubsystem c

-- ============================================================================
-- §11  "Sufficient idle" theorem + per-operation SMP-preservation composition
-- ============================================================================

/-- WS-SM SM4.C: when core `c` is **idle** on `st` (no current thread, empty
run queue, positive domain-time), `schedulerInvariant_perCore st c` holds
unconditionally.  Every current-dependent conjunct is vacuous (matches on
`none`); every runnable-quantified conjunct is vacuous (universally
quantifies over `[]`); the only non-vacuous conjunct,
`domainTimeRemainingPositive`, is supplied as a hypothesis.

This is the **structural** sufficient condition that justifies why, on the
current single-core kernel, non-boot cores trivially satisfy the per-core
invariant: they are perma-idle (default state) until SM5 activates them. -/
theorem schedulerInvariant_perCore_holds_if_idle (st : SystemState) (c : CoreId)
    (hCurNone : st.scheduler.currentOnCore c = none)
    (hRQEmpty : (st.scheduler.runQueueOnCore c).toList = [])
    (hDTRPos : st.scheduler.domainTimeRemainingOnCore c > 0)
    -- audit-pass-9: `toList = []` doesn't entail wellFormed structurally;
    -- the caller supplies it.  SM5 discharges via `RunQueue.empty_wellFormed`.
    (hWf : (st.scheduler.runQueueOnCore c).wellFormed) :
    schedulerInvariant_perCore st c := by
  have hNotMemList : ∀ tid : SeLe4n.ThreadId,
      tid ∉ (st.scheduler.runQueueOnCore c).toList := by
    intro tid; rw [hRQEmpty]; exact List.not_mem_nil
  have hNotMem : ∀ tid : SeLe4n.ThreadId,
      tid ∉ (st.scheduler.runQueueOnCore c) := by
    intro tid hMem
    exact hNotMemList tid ((RunQueue.mem_toList_iff_mem _ tid).2 hMem)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [queueCurrentConsistentOnCore, hCurNone]
  · simp only [runQueueUniqueOnCore, hRQEmpty]; exact List.nodup_nil
  · simp only [currentThreadValidOnCore, hCurNone]
  · intro tid hMem; exact absurd hMem (hNotMemList tid)
  · simp only [currentTimeSlicePositiveOnCore, hCurNone]
  · simp only [edfCurrentHasEarliestDeadlineOnCore, hCurNone]
  · simp only [contextMatchesCurrentOnCore, hCurNone]
  · intro tid hMem; exact absurd hMem (hNotMemList tid)
  · intro tid hMem; exact absurd hMem (hNotMem tid)
  · exact hDTRPos
  · -- `toList = []` does not entail `wellFormed`: a RunQueue can have
    -- empty `flat` while `byPriority` carries inconsistent buckets.  SM5
    -- discharges `hWf` from "this core's RunQueue = `RunQueue.empty`"
    -- via `RunQueue.empty_wellFormed`.
    exact hWf

/-- Strong-idle variant of §6's `schedulerInvariant_perCore_frame_idle`:
when core `c`'s scheduler slots are *all* in the idle shape (no current,
empty run queue, positive DTR) on the post-state, the per-core invariant
holds at `c` regardless of any state change.  This bypasses the
`objects` / `regs` frame hypotheses entirely — for an idle core,
neither matters. -/
theorem schedulerInvariant_perCore_idle_on_post_state {st' : SystemState} {c : CoreId}
    (hCurNone : st'.scheduler.currentOnCore c = none)
    (hRQEmpty : (st'.scheduler.runQueueOnCore c).toList = [])
    (hDTRPos : st'.scheduler.domainTimeRemainingOnCore c > 0)
    -- audit-pass-9: forwarded wellFormed hypothesis from `_holds_if_idle`.
    (hWf : (st'.scheduler.runQueueOnCore c).wellFormed) :
    schedulerInvariant_perCore st' c :=
  schedulerInvariant_perCore_holds_if_idle st' c hCurNone hRQEmpty hDTRPos hWf

/-- audit-pass-11 (post-audit improvement): convenience form of
`schedulerInvariant_perCore_holds_if_idle` taking the *stronger structural*
hypothesis `runQueueOnCore c = RunQueue.empty` instead of the pair
`(toList = []) ∧ wellFormed`.

The trade-off this resolves: pre-audit-11, the SM5-bridge skeleton's
`hNonBootIdle` had to carry 4 conjuncts including `wellFormed`,
because `toList = []` alone cannot derive `wellFormed` (the
`RunQueue.byPriority` index is structurally independent of `flat`).
Under the SM5 contract, non-boot cores ARE the default-replicate
`RunQueue.empty` — a strictly stronger fact that DOES entail
`wellFormed` (via `RunQueue.empty_wellFormed`) and `toList = []`
(via `RunQueue.toList_empty`).  This wrapper exposes that path so
SM5 callers with `rq = empty` skip the manual conversion.

The underlying `_holds_if_idle` is retained as the *minimal* form
(takes only the necessary facts; no over-constraint), and remains
the public API for callers that only have the weaker facts. -/
theorem schedulerInvariant_perCore_holds_if_idle_default
    (st : SystemState) (c : CoreId)
    (hCurNone : st.scheduler.currentOnCore c = none)
    (hRQEqEmpty : st.scheduler.runQueueOnCore c = RunQueue.empty)
    (hDTRPos : st.scheduler.domainTimeRemainingOnCore c > 0) :
    schedulerInvariant_perCore st c :=
  schedulerInvariant_perCore_holds_if_idle st c hCurNone
    (hRQEqEmpty ▸ RunQueue.toList_empty)
    hDTRPos
    (hRQEqEmpty ▸ RunQueue.empty_wellFormed)

/-- WS-SM SM4.C: **the per-operation SMP-preservation composition** — the
SM5 migration bridge for any boot-core scheduler operation.

Given:
  * `hBoot'` : the boot core's per-core invariant has been re-established
    post-operation (typically from
    `schedulerInvariantBundleFull_to_perCore_bootCore` applied to the
    existing single-core preservation theorem), AND
  * `hNonBootIdle` : every non-boot core is idle in the
    `schedulerInvariant_perCore_holds_if_idle` sense on the post-state
    (holds by construction for any boot-core-only operation under the
    SM4.B setter discipline, since non-boot cores' slots are unchanged
    from their default idle initial values).

This composition cleanly avoids the frame-equality hypotheses
(`hFrameRQ`, `hFrameDTR`, `hFrameObj`) of `_smp_of_bootCore_and_idle_frame`,
making it applicable to operations that *do* change `objects` or
`machine.regs` (e.g., `schedule`'s context restore) — for non-boot idle
cores, those changes are simply invisible. -/
theorem schedulerInvariant_smp_of_bootCore_preservation
    {st' : SystemState}
    (hBoot' : schedulerInvariant_perCore st' bootCoreId)
    -- audit-pass-9 (PR #801, reviewer comment 2): the non-boot idle
    -- witness now bundles four facts (no current, empty run queue,
    -- positive DTR, **wellFormed run queue**) — the fourth needed by
    -- the audit-pass-9 conjunct in the per-core aggregate.  Discharged
    -- in SM5 from "the non-boot core's runQueueOnCore is the default
    -- replicate slot, which is `RunQueue.empty`, whose wellFormed
    -- holds by the empty-RHTable lookup pattern (see
    -- `default_schedulerInvariant_perCore`'s discharge for the new
    -- conjunct)".
    (hNonBootIdle : ∀ c, c ≠ bootCoreId →
      st'.scheduler.currentOnCore c = none ∧
      (st'.scheduler.runQueueOnCore c).toList = [] ∧
      st'.scheduler.domainTimeRemainingOnCore c > 0 ∧
      (st'.scheduler.runQueueOnCore c).wellFormed) :
    schedulerInvariant_smp st' := by
  intro c
  by_cases hc : c = bootCoreId
  · subst hc; exact hBoot'
  · obtain ⟨hCN, hRQE, hDTR, hWf⟩ := hNonBootIdle c hc
    exact schedulerInvariant_perCore_holds_if_idle st' c hCN hRQE hDTR hWf

/-- The extended analog of `schedulerInvariant_smp_of_bootCore_preservation`.
For non-boot cores, the extended invariant holds when the core is fully
idle in the *base* sense (no current, empty run queue, positive DTR) AND
the *extended* sense (empty replenish queue).  The caller supplies a
per-core "fully idle on post-state" witness `hNonBootIdle'` that proves
the extended per-core invariant at each non-boot core directly. -/
theorem schedulerInvariant_smp_extended_of_bootCore_preservation
    {st' : SystemState}
    (hBoot' : schedulerInvariant_perCore_extended st' bootCoreId)
    (hNonBootIdle' : ∀ c, c ≠ bootCoreId →
      schedulerInvariant_perCore_extended st' c) :
    schedulerInvariant_smp_extended st' := by
  intro c
  by_cases hc : c = bootCoreId
  · subst hc; exact hBoot'
  · exact hNonBootIdle' c hc

end SeLe4n.Kernel
