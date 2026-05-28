-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Invariant

-- The boot-core bridge proofs in §2 use `cases h : X` substitution to
-- substantively case-analyse on `objects[…]?` lookups; the `simp [hObj]`
-- calls at the leaves are defensive (some cases close without consuming
-- the equation, depending on the variant) and the linter flags them as
-- unused arguments per arm.  The proofs are correct as written; suppress
-- the noise file-locally.
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

**AK7 typed-accessor discipline**: thirteen of the sixteen per-core
predicate bodies route their object-store lookups through the typed
`getTcb?` accessor (only one-level lookup); their boot-core bridges go
through `getTcb?_eq_some_iff` plus a per-variant case analysis on
`st.objects[…]?`.  Three predicates that need a two-level lookup
(TCB-then-SchedContext: `currentBudgetPositiveOnCore`,
`budgetPositiveOnCore`, `effectiveParamsMatchRunQueueOnCore`) keep the
existing raw `match`-on-`objects[…]?` body verbatim so their boot-core
bridges close as defeq `Iff.rfl`; a future workstream that migrates the
corresponding single-core predicates to typed accessors will move these
mirrors with them.

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
`currentBudgetPositive`.

This predicate uses raw `match`-on-`objects[…]?` rather than the typed
`getTcb?` / `getSchedContext?` accessors.  Reason: the predicate has two
nested object-store lookups (TCB-then-SchedContext), and matching the
existing single-core predicate's raw-`match` body verbatim keeps the
boot-core bridge as a defeq `Iff.rfl` (rather than requiring a multi-
level case-analysis proof through `getTcb?_eq_some_iff` /
`getSchedContext?_eq_some_iff`).  The typed-accessor migration of this
predicate's underlying single-core form is tracked as an AK7-cascade
candidate; when it lands, this per-core mirror moves with it. -/
def currentBudgetPositiveOnCore (st : SystemState) (c : CoreId) : Prop :=
  match st.scheduler.currentOnCore c with
  | none => True
  | some tid =>
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
      match tcb.schedContextBinding with
      | .unbound => True
      | .bound scId | .donated scId _ =>
        match st.objects[scId.toObjId]? with
        | some (.schedContext sc) => sc.budgetRemaining.val > 0
        | _ => True
    | _ => True

/-- SM4.C: per-core budget positivity for runnable threads.  Per-core form
of `budgetPositive`.  (See `currentBudgetPositiveOnCore`'s note on the
raw-`match` choice for two-level object lookups.) -/
def budgetPositiveOnCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ tid, tid ∈ (st.scheduler.runQueueOnCore c).toList →
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
      match tcb.schedContextBinding with
      | .unbound => True
      | .bound scId | .donated scId _ =>
        match st.objects[scId.toObjId]? with
        | some (.schedContext sc) => sc.budgetRemaining.val > 0
        | _ => True
    | _ => True

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
`effectiveParamsMatchRunQueue`.  (See `currentBudgetPositiveOnCore`'s note
on the raw-`match` choice for two-level object lookups.) -/
def effectiveParamsMatchRunQueueOnCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ tid, tid ∈ (st.scheduler.runQueueOnCore c) →
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
      match tcb.schedContextBinding with
      | .unbound =>
        (st.scheduler.runQueueOnCore c).threadPriority[tid]? = some tcb.priority
      | .bound scId | .donated scId _ =>
        match st.objects[scId.toObjId]? with
        | some (.schedContext sc) =>
          (st.scheduler.runQueueOnCore c).threadPriority[tid]? = some sc.priority
        | _ => True
    | _ => True

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

theorem currentBudgetPositiveOnCore_bootCore_iff (st : SystemState) :
    currentBudgetPositiveOnCore st bootCoreId ↔ currentBudgetPositive st := Iff.rfl

theorem budgetPositiveOnCore_bootCore_iff (st : SystemState) :
    budgetPositiveOnCore st bootCoreId ↔ budgetPositive st := Iff.rfl

theorem replenishmentPipelineOrderOnCore_bootCore_iff (st : SystemState) :
    replenishmentPipelineOrderOnCore st bootCoreId ↔ replenishmentPipelineOrder st := Iff.rfl

theorem replenishQueueValidOnCore_bootCore_iff (st : SystemState) :
    replenishQueueValidOnCore st bootCoreId ↔ replenishQueueValid st := Iff.rfl

theorem effectiveParamsMatchRunQueueOnCore_bootCore_iff (st : SystemState) :
    effectiveParamsMatchRunQueueOnCore st bootCoreId ↔ effectiveParamsMatchRunQueue st := Iff.rfl

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
  domainTimeRemainingPositiveOnCore st c

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
  h.2.2.2.2.2.2.2.2.2

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
    (h : schedulerInvariantBundleFull st) : schedulerInvariant_perCore st bootCoreId := by
  obtain ⟨⟨hQCC, hRQU, hCTV⟩, hTSP, hCTSP, hEDF, hCMC, hRAT, hSPM, hDTR, _hDSE⟩ := h
  refine ⟨hQCC, hRQU, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hDTR⟩
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
  obtain ⟨hQCC, hRQU, hCTV, hTSP, hCTSP, hEDF, hCMC, hRAT, hSPM, hDTR⟩ := h
  refine ⟨⟨hQCC, hRQU, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, hDTR, hDSE⟩
  · exact (currentThreadValidOnCore_bootCore_iff st).mp hCTV
  · exact (timeSlicePositiveOnCore_bootCore_iff st).mp hTSP
  · exact (currentTimeSlicePositiveOnCore_bootCore_iff st).mp hCTSP
  · exact (edfCurrentHasEarliestDeadlineOnCore_bootCore_iff st).mp hEDF
  · exact (contextMatchesCurrentOnCore_bootCore_iff st).mp hCMC
  · exact (runnableThreadsAreTCBsOnCore_bootCore_iff st).mp hRAT
  · exact (schedulerPriorityMatchOnCore_bootCore_iff st).mp hSPM

/-- WS-SM SM4.C: the extended single-core bundle (a superset of the full
bundle) likewise implies the per-core invariant at the boot core. -/
theorem schedulerInvariantBundleExtended_to_perCore_bootCore {st : SystemState}
    (h : schedulerInvariantBundleExtended st) : schedulerInvariant_perCore st bootCoreId :=
  schedulerInvariantBundleFull_to_perCore_bootCore h.1

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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

/-- WS-SM SM4.C: the freshly-booted system satisfies the system-wide SMP
scheduler invariant — the per-core invariant on every core. -/
theorem default_schedulerInvariant_smp :
    schedulerInvariant_smp (default : SystemState) :=
  fun c => default_schedulerInvariant_perCore c

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
  -- `getSchedContext?` — none of the 10 conjuncts in the aggregate look
  -- up SchedContext objects); `hTcb` is the only object-store congruence
  -- needed.  `hObj` flows in through `getTcb?_congr_objects`.
  have hTcb : ∀ tid, st'.getTcb? tid = st.getTcb? tid := getTcb?_congr_objects hObj
  simp only [schedulerInvariant_perCore, queueCurrentConsistentOnCore, runQueueUniqueOnCore,
    currentThreadValidOnCore, timeSlicePositiveOnCore, currentTimeSlicePositiveOnCore,
    edfCurrentHasEarliestDeadlineOnCore, contextMatchesCurrentOnCore,
    runnableThreadsAreTCBsOnCore, schedulerPriorityMatchOnCore,
    domainTimeRemainingPositiveOnCore, hCur, hRQ, hDTR, hRegs, hTcb]

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
  have hTcb : ∀ tid, st'.getTcb? tid = st.getTcb? tid := getTcb?_congr_objects hObj
  simp only [schedulerInvariant_perCore, queueCurrentConsistentOnCore, runQueueUniqueOnCore,
    currentThreadValidOnCore, timeSlicePositiveOnCore, currentTimeSlicePositiveOnCore,
    edfCurrentHasEarliestDeadlineOnCore, contextMatchesCurrentOnCore,
    runnableThreadsAreTCBsOnCore, schedulerPriorityMatchOnCore,
    domainTimeRemainingPositiveOnCore, hCurNone', hCurNone, hRQ, hDTR, hTcb]

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

end SeLe4n.Kernel
