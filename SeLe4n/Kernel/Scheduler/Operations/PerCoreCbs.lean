-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.Core
import SeLe4n.Kernel.Scheduler.Operations.PerCoreChooseThread
import SeLe4n.Kernel.Scheduler.Operations.PerCoreTimerTick

/-!
# WS-SM SM5.H — Per-core CBS (Constant Bandwidth Server)

Per-core CBS replenishment-queue management (plan
`docs/planning/SMP_PER_CORE_SCHEDULER_PLAN.md` §3.8, §5): each core owns its
**own** replenishment queue (`replenishQueueOnCore c`, the SM4.B per-core field),
holding the budget-refill schedule for the SchedContexts whose bound thread is
homed on core `c`.  When a thread's `cpuAffinity` changes, its bound
SchedContext's pending replenishments **migrate** to the new core's queue, so the
per-core CBS accounting follows the thread.

This module builds on the substantial per-core CBS machinery already landed by
SM5.D (the per-core timer tick): `processReplenishmentsDueOnCore`,
`refillSchedContext`, `replenishWakeTarget`, and `timerTickBudgetOnCore` (which
inserts an exhausted SchedContext's future replenishment into
`replenishQueueOnCore c`).  SM5.H adds the **queue-management** surface SM5.D
open-coded plus the genuinely-new **migration** operation:

* **SM5.H.1** — `replenishQueueOnCore` is the SM4.B accessor; this module recaps
  it via the SM4.C well-formedness predicates (`replenishQueueValidOnCore` /
  `replenishmentPipelineOrderOnCore`) and introduces the plan §3.8 affinity-
  consistency invariant `replenishQueueAffinityConsistentOnCore`.
* **SM5.H.2** — `replenishOnCore`: the per-core "schedule a CBS replenishment"
  primitive (insert `(scId, eligibleAt)` into `replenishQueueOnCore c`) — the
  clean named extraction of the queue insert `timerTickBudgetOnCore` /
  `handleYieldWithBudget` open-code — plus its frame lemmas.
* **SM5.H.3** — `replenishOnCore` / the migration preserve
  `replenishQueueValidOnCore` (sorted + size-consistent) on every core.
* **SM5.H.4** — `migrateSchedContextReplenishment` (move a SchedContext's pending
  replenishments between cores) and the composite
  `setThreadCpuAffinityWithMigration` (set affinity AND migrate), plus
  `schedContextMigration_consistent` (the migration restores affinity-
  consistency).
* **SM5.H.5** — `replenishQueueAffinityConsistentOnCore` (plan §3.8 Theorem
  3.8.1): every SchedContext in core `c`'s replenish queue has its bound thread
  homed on core `c` (`determineTargetCore = c`).
* **SM5.H.6** — `replenishOnCore` / the migration preserve
  `replenishmentPipelineOrderOnCore` (every queued replenishment is eligible
  strictly in the future).
* **SM5.H.7** — per-core CBS budget accounting: `timerTickBudgetOnCore` preserves
  the per-core replenish-queue validity + pipeline order (the per-core CBS
  invariant the SM5.I run loop carries across a tick).

All theorems are proved with no dependency beyond Lean's foundational `propext` /
`Quot.sound` / `Classical.choice`.  The new operations (`replenishOnCore`, the
migration) are forward-looking infrastructure — the live per-core CBS path is the
SM5.D `timerTickOnCore`, and the affinity-migration syscall (`tcbSetAffinity`,
which would call `setThreadCpuAffinityWithMigration`) is SM5.I+ work — so this
module is staged via `Platform.Staged`; SM5.I's per-core run loop is the first
runtime exerciser.

## Naming erratum (plan §3.8)

The plan §3.8 Theorem 3.8.1 is captioned `schedContextRunQueueConsistent_perCore`,
but that name is **already taken** by an unrelated SM4.C predicate (run-queue
membership ↔ positive budget, in `Scheduler/Invariant/PerCore.lean`).  The §3.8
content is about the **replenish queue ↔ thread home core**, so — per the
internal-first naming rule — it is named `replenishQueueAffinityConsistentOnCore`
here.  The literal `cpuAffinity = some c` of the §3.8 pseudocode is realised as
`determineTargetCore st tid = c` (the SM5.C.9 "unbound ⇒ bootCoreId" home-core
rule), which correctly admits SchedContext-bound but affinity-unbound threads
(whose replenishments are homed on the boot core) — the literal form would
wrongly forbid them.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (numCores CoreId bootCoreId SgiKind)

-- ============================================================================
-- §1  SM5.H.1 / SM5.H.5 — the per-core CBS replenish-queue predicates
-- ============================================================================

/-- WS-SM SM5.H.5 (plan §3.8, Theorem 3.8.1): per-core CBS replenish-queue
affinity consistency.  Every SchedContext with a pending replenishment in core
`c`'s replenish queue has its bound thread **homed on core `c`** — i.e. the
thread's wake target (`determineTargetCore`, the SM5.C.9 home-core rule) is `c`.

This is the per-core CBS analogue of the SM4.C
`schedContextRunQueueConsistent_perCore` (run queue ↔ budget): it connects the
per-core *replenish* queue to per-thread CPU placement, so a thread's
budget-refill schedule lives on the core the thread will wake onto.  It is the
invariant the SM5.H.4 affinity migration restores (a thread whose home core
changes drags its SchedContext's replenishments to the new core).

The literal `cpuAffinity = some c` of the §3.8 pseudocode is generalised to
`determineTargetCore st tid = c`: for a thread bound to `some c` it is exactly
`cpuAffinity = some c`, while for a SchedContext-bound but affinity-unbound thread
(`cpuAffinity = none`) it correctly maps to `bootCoreId` (the boot core homes
unbound threads, SM5.C.9) — the literal form would wrongly forbid such threads
from holding a SchedContext at all. -/
def replenishQueueAffinityConsistentOnCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ (scId : SchedContextId) (t : Nat),
    (scId, t) ∈ (st.scheduler.replenishQueueOnCore c).entries →
    ∀ sc, st.getSchedContext? scId = some sc →
      ∀ tid, sc.boundThread = some tid →
        determineTargetCore st tid = c

/-- WS-SM SM5.H.5: the SMP-wide affinity-consistency invariant — every core's
replenish queue is affinity-consistent. -/
def replenishQueueAffinityConsistent_smp (st : SystemState) : Prop :=
  ∀ c : CoreId, replenishQueueAffinityConsistentOnCore st c

/-- WS-SM SM5.H.5: the SMP form extracts the per-core form at any core. -/
theorem replenishQueueAffinityConsistent_smp_at (st : SystemState)
    (h : replenishQueueAffinityConsistent_smp st) (c : CoreId) :
    replenishQueueAffinityConsistentOnCore st c := h c

/-- WS-SM SM5.H.5: the freshly-booted system is affinity-consistent on every core
(vacuous — the default replenish queue is empty). -/
theorem default_replenishQueueAffinityConsistentOnCore (c : CoreId) :
    replenishQueueAffinityConsistentOnCore (default : SystemState) c := by
  intro scId t hMem _ _ _ _
  have hRepl : (default : SystemState).scheduler.replenishQueueOnCore c
      = SeLe4n.Kernel.ReplenishQueue.empty := (default_state_perCoreInitialized c).2.2.1
  rw [hRepl] at hMem
  simp [SeLe4n.Kernel.ReplenishQueue.empty] at hMem

/-- WS-SM SM5.H.5: the freshly-booted system is SMP-affinity-consistent. -/
theorem default_replenishQueueAffinityConsistent_smp :
    replenishQueueAffinityConsistent_smp (default : SystemState) :=
  fun c => default_replenishQueueAffinityConsistentOnCore c

/-- WS-SM SM5.H.5 (frame): the affinity-consistency invariant on core `c` reads
only core `c`'s replenish queue plus the object store (via `getSchedContext?` and
`determineTargetCore`, both pure object-store reads).  A state agreeing on those
agrees on the predicate. -/
theorem replenishQueueAffinityConsistentOnCore_frame {st st' : SystemState} {c : CoreId}
    (hRepl : st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c)
    (hObj : st'.objects = st.objects) :
    replenishQueueAffinityConsistentOnCore st' c ↔
    replenishQueueAffinityConsistentOnCore st c := by
  have hSc : ∀ scId, st'.getSchedContext? scId = st.getSchedContext? scId := by
    intro scId; unfold SystemState.getSchedContext?; rw [hObj]
  have hTgt : ∀ tid, determineTargetCore st' tid = determineTargetCore st tid := by
    intro tid; unfold determineTargetCore SystemState.getTcb?; rw [hObj]
  unfold replenishQueueAffinityConsistentOnCore
  simp only [hRepl, hSc, hTgt]

-- ============================================================================
-- §1b  Structural lemmas for `ReplenishQueue.insertSorted` / `.remove`
-- ============================================================================
--
-- The membership-decomposition lemmas the SM5.H preservation proofs rest on:
-- a member of `insertSorted` is the new entry or an old entry; a member of
-- `remove` (a filter) is an old entry whose key differs.  Kept local to the
-- staged module (about `ReplenishQueue.insertSorted`, in scope via the import)
-- to avoid a production rebuild of the whole kernel for a pure list lemma.

/-- WS-SM SM5.H: a member of `insertSorted entries scId t` is either the freshly
inserted entry `(scId, t)` or an original entry of `entries`.  The reverse of the
existing `ReplenishQueue.mem_insertSorted` / `subset_insertSorted`. -/
private theorem mem_insertSorted_iff (entries : List (SchedContextId × Nat))
    (scId : SchedContextId) (t : Nat) (e : SchedContextId × Nat) :
    e ∈ ReplenishQueue.insertSorted entries scId t ↔ (e = (scId, t) ∨ e ∈ entries) := by
  induction entries with
  | nil => simp [ReplenishQueue.insertSorted]
  | cons hd tail ih =>
    obtain ⟨hId, hTime⟩ := hd
    unfold ReplenishQueue.insertSorted
    split
    · -- `t < hTime`: result is `(scId, t) :: (hId, hTime) :: tail`; both sides
      -- normalise to the same 3-way disjunction.
      simp only [List.mem_cons]
    · -- `¬ t < hTime`: result is `(hId, hTime) :: insertSorted tail …`; close the
      -- or-reassociation explicitly (`tauto` is unavailable in the core toolchain).
      simp only [List.mem_cons, ih]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rcases h with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rcases h with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

/-- WS-SM SM5.H: a member of `rq.remove scId`'s entries is an original member of
`rq.entries` whose key is *not* `scId` (the filtered-out key). -/
private theorem mem_remove_entries {rq : ReplenishQueue} {scId : SchedContextId}
    {e : SchedContextId × Nat} (h : e ∈ (rq.remove scId).entries) :
    e ∈ rq.entries ∧ e.1 ≠ scId := by
  simp only [ReplenishQueue.remove] at h
  have h' := List.mem_filter.mp h
  refine ⟨h'.1, ?_⟩
  intro hEq
  have hbeq : (e.1 == scId) = true := by rw [hEq]; exact beq_self_eq_true _
  simp [hbeq] at h'

-- ============================================================================
-- §2  SM5.H.2 — `replenishOnCore`: per-core CBS replenishment scheduling
-- ============================================================================

/- WS-SM SM5.H.2 (plan §3.8): `replenishOnCore st c scId eligibleAt` schedules a CBS
replenishment for SchedContext `scId` on core `c` — inserts `(scId, eligibleAt)`
into core `c`'s replenish queue (`replenishQueueOnCore c`, SM4.B per-core field),
leaving every other scheduler slot, every *other* core's replenish queue, and the
object store untouched.  The clean named extraction of the queue insert
`timerTickBudgetOnCore` / `handleYieldWithBudget` open-code.  The plan signature
`replenishOnCore (s, c, sc)` realises `sc` as `(scId, eligibleAt)`; the faithful
`replenishScOnCore (s, c, sc, now)` form computes `now + sc.period.val` internally,
discharging the SM5.H.6 pipeline-order future-ness from `sc.period > 0`.

`replenishOnCore`, `replenishScOnCore`, the migration, and the composite are
**production** defs in `Scheduler/Operations/Core.lean` (reached via the SM5.H.4
`tcbSetAffinity` syscall); this staged module collects their theorem surface. -/

/-- WS-SM SM5.H.2: scheduling a replenishment never touches the object store. -/
@[simp] theorem replenishOnCore_objects (st : SystemState) (c : CoreId)
    (scId : SchedContextId) (eligibleAt : Nat) :
    (replenishOnCore st c scId eligibleAt).objects = st.objects := rfl

/-- WS-SM SM5.H.2: scheduling a replenishment never advances the machine timer. -/
@[simp] theorem replenishOnCore_machine (st : SystemState) (c : CoreId)
    (scId : SchedContextId) (eligibleAt : Nat) :
    (replenishOnCore st c scId eligibleAt).machine = st.machine := rfl

/-- WS-SM SM5.H.2: it frames every thread's TCB resolution (object store unchanged). -/
theorem replenishOnCore_getTcb? (st : SystemState) (c : CoreId)
    (scId : SchedContextId) (eligibleAt : Nat) (tid : SeLe4n.ThreadId) :
    (replenishOnCore st c scId eligibleAt).getTcb? tid = st.getTcb? tid := by
  unfold SystemState.getTcb?; rw [replenishOnCore_objects]

/-- WS-SM SM5.H.2: it frames every SchedContext resolution (object store unchanged). -/
theorem replenishOnCore_getSchedContext? (st : SystemState) (c : CoreId)
    (scId : SchedContextId) (eligibleAt : Nat) (scId' : SchedContextId) :
    (replenishOnCore st c scId eligibleAt).getSchedContext? scId' = st.getSchedContext? scId' := by
  unfold SystemState.getSchedContext?; rw [replenishOnCore_objects]

/-- WS-SM SM5.H.2: it frames every thread's home core (`determineTargetCore`
reads only the object store). -/
theorem replenishOnCore_determineTargetCore (st : SystemState) (c : CoreId)
    (scId : SchedContextId) (eligibleAt : Nat) (tid : SeLe4n.ThreadId) :
    determineTargetCore (replenishOnCore st c scId eligibleAt) tid = determineTargetCore st tid := by
  unfold determineTargetCore SystemState.getTcb?; rw [replenishOnCore_objects]

/-- WS-SM SM5.H.2: core `c`'s replenish queue after scheduling is the old queue
with `(scId, eligibleAt)` inserted.  (`(replenishOnCore …).scheduler` is
definitionally `st.scheduler.setReplenishQueueOnCore c …`, so each frame is the
corresponding SM4.B setter lemma.) -/
@[simp] theorem replenishOnCore_replenishQueueOnCore_self (st : SystemState) (c : CoreId)
    (scId : SchedContextId) (eligibleAt : Nat) :
    (replenishOnCore st c scId eligibleAt).scheduler.replenishQueueOnCore c
      = (st.scheduler.replenishQueueOnCore c).insert scId eligibleAt := by
  unfold replenishOnCore
  exact SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_self _ _ _

/-- WS-SM SM5.H.2: scheduling on core `c` frames a *different* core `c'`'s
replenish queue. -/
theorem replenishOnCore_replenishQueueOnCore_ne (st : SystemState) (c c' : CoreId)
    (scId : SchedContextId) (eligibleAt : Nat) (h : c ≠ c') :
    (replenishOnCore st c scId eligibleAt).scheduler.replenishQueueOnCore c'
      = st.scheduler.replenishQueueOnCore c' := by
  unfold replenishOnCore
  exact SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ _ _ _ h

/-- WS-SM SM5.H.2: scheduling a replenishment frames every core's run queue. -/
@[simp] theorem replenishOnCore_runQueueOnCore (st : SystemState) (c c' : CoreId)
    (scId : SchedContextId) (eligibleAt : Nat) :
    (replenishOnCore st c scId eligibleAt).scheduler.runQueueOnCore c'
      = st.scheduler.runQueueOnCore c' := by
  unfold replenishOnCore
  exact SchedulerState.setReplenishQueueOnCore_runQueueOnCore _ _ _ _

/-- WS-SM SM5.H.2: scheduling a replenishment frames every core's current thread. -/
@[simp] theorem replenishOnCore_currentOnCore (st : SystemState) (c c' : CoreId)
    (scId : SchedContextId) (eligibleAt : Nat) :
    (replenishOnCore st c scId eligibleAt).scheduler.currentOnCore c'
      = st.scheduler.currentOnCore c' := by
  unfold replenishOnCore
  exact SchedulerState.setReplenishQueueOnCore_currentOnCore _ _ _ _

/-- WS-SM SM5.H.2: scheduling a replenishment frames every core's active domain. -/
@[simp] theorem replenishOnCore_activeDomainOnCore (st : SystemState) (c c' : CoreId)
    (scId : SchedContextId) (eligibleAt : Nat) :
    (replenishOnCore st c scId eligibleAt).scheduler.activeDomainOnCore c'
      = st.scheduler.activeDomainOnCore c' := by
  unfold replenishOnCore
  exact SchedulerState.setReplenishQueueOnCore_activeDomainOnCore _ _ _ _

/-- WS-SM SM5.H.2: the scheduled entry is a genuine member of core `c`'s
post-state replenish queue (it was not dropped). -/
theorem replenishOnCore_mem (st : SystemState) (c : CoreId)
    (scId : SchedContextId) (eligibleAt : Nat) :
    (scId, eligibleAt) ∈ ((replenishOnCore st c scId eligibleAt).scheduler.replenishQueueOnCore c).entries := by
  rw [replenishOnCore_replenishQueueOnCore_self]
  exact mem_insertSorted _ scId eligibleAt

-- ============================================================================
-- §3  SM5.H.3 — `replenishOnCore` preserves replenish-queue validity
-- ============================================================================

/-- WS-SM SM5.H.3 (plan §6.1 `replenishQueueOnCore_wellFormed`): scheduling a
replenishment on core `c` preserves core `c`'s replenish-queue validity
(`replenishQueueValidOnCore` = sorted-by-eligibility ∧ size-consistent).  The
queue insert preserves both via `ReplenishQueue.insert_preserves_sorted` /
`insert_sizeConsistent`. -/
theorem replenishOnCore_preserves_replenishQueueValidOnCore (st : SystemState)
    (c : CoreId) (scId : SchedContextId) (eligibleAt : Nat)
    (hValid : replenishQueueValidOnCore st c) :
    replenishQueueValidOnCore (replenishOnCore st c scId eligibleAt) c := by
  unfold replenishQueueValidOnCore
  rw [replenishOnCore_replenishQueueOnCore_self]
  exact ⟨insert_preserves_sorted hValid.1, insert_sizeConsistent hValid.2⟩

/-- WS-SM SM5.H.3: scheduling on core `c` preserves a *different* core `c'`'s
replenish-queue validity (its queue is untouched). -/
theorem replenishOnCore_preserves_replenishQueueValidOnCore_ne (st : SystemState)
    (c c' : CoreId) (scId : SchedContextId) (eligibleAt : Nat) (h : c ≠ c')
    (hValid : replenishQueueValidOnCore st c') :
    replenishQueueValidOnCore (replenishOnCore st c scId eligibleAt) c' :=
  (replenishQueueValidOnCore_frame (replenishOnCore_replenishQueueOnCore_ne st c c' scId eligibleAt h)).mpr hValid

/-- WS-SM SM5.H.3 (SMP form): scheduling a replenishment preserves
replenish-queue validity on **every** core. -/
theorem replenishOnCore_preserves_replenishQueueValid_smp (st : SystemState)
    (c : CoreId) (scId : SchedContextId) (eligibleAt : Nat)
    (hValid : ∀ c', replenishQueueValidOnCore st c') :
    ∀ c', replenishQueueValidOnCore (replenishOnCore st c scId eligibleAt) c' := by
  intro c'
  by_cases h : c = c'
  · subst h; exact replenishOnCore_preserves_replenishQueueValidOnCore st c scId eligibleAt (hValid c)
  · exact replenishOnCore_preserves_replenishQueueValidOnCore_ne st c c' scId eligibleAt h (hValid c')

-- ============================================================================
-- §4  SM5.H.6 — `replenishOnCore` preserves replenishment-pipeline order
-- ============================================================================

/-- WS-SM SM5.H.6 (plan §6.1 `replenishmentPipelineOrder_perCore`): scheduling a
replenishment on core `c` at a **future** eligibility tick (`eligibleAt >
machine.timer`) preserves core `c`'s replenishment-pipeline order (every queued
replenishment is eligible strictly after the current tick).

The CBS engine always schedules at `now + period.val` with `period.val > 0`, so
`eligibleAt > machine.timer` holds at every real call site (this is the SM5.H.6
discharge obligation, exposed as a hypothesis so `replenishOnCore` itself stays
agnostic to the eligibility computation).  `replenishOnCore` does not advance the
machine timer, so the existing entries' future-ness is inherited and the new
entry's is `hFuture`. -/
theorem replenishOnCore_preserves_replenishmentPipelineOrderOnCore (st : SystemState)
    (c : CoreId) (scId : SchedContextId) (eligibleAt : Nat)
    (hPipeline : replenishmentPipelineOrderOnCore st c)
    (hFuture : eligibleAt > st.machine.timer) :
    replenishmentPipelineOrderOnCore (replenishOnCore st c scId eligibleAt) c := by
  intro pair hMem
  rw [replenishOnCore_machine]
  rw [replenishOnCore_replenishQueueOnCore_self] at hMem
  rcases (mem_insertSorted_iff _ scId eligibleAt pair).mp hMem with hEq | hOld
  · rw [hEq]; exact hFuture
  · exact hPipeline pair hOld

/-- WS-SM SM5.H.6: scheduling on core `c` preserves a *different* core `c'`'s
pipeline order (its queue and the machine timer are untouched). -/
theorem replenishOnCore_preserves_replenishmentPipelineOrderOnCore_ne (st : SystemState)
    (c c' : CoreId) (scId : SchedContextId) (eligibleAt : Nat) (h : c ≠ c')
    (hPipeline : replenishmentPipelineOrderOnCore st c') :
    replenishmentPipelineOrderOnCore (replenishOnCore st c scId eligibleAt) c' := by
  intro pair hMem
  rw [replenishOnCore_machine]
  rw [replenishOnCore_replenishQueueOnCore_ne st c c' scId eligibleAt h] at hMem
  exact hPipeline pair hMem

-- ============================================================================
-- §5  SM5.H.5 — `replenishOnCore` preserves affinity consistency
-- ============================================================================

/-- WS-SM SM5.H.5: scheduling a replenishment for `scId` on core `c` preserves
core `c`'s affinity consistency, provided the scheduled SchedContext is itself
homed on `c` (`hTarget`: its bound thread's `determineTargetCore` is `c`).  This
is the obligation the live CBS path discharges — `timerTickBudgetOnCore` schedules
`scId` on the core running the tick, which under the invariant is `scId`'s home
core.  `replenishOnCore` frames `getSchedContext?` / `determineTargetCore` (object
store untouched), so the only new queue entry is `(scId, eligibleAt)`, covered by
`hTarget`. -/
theorem replenishOnCore_preserves_replenishQueueAffinityConsistentOnCore (st : SystemState)
    (c : CoreId) (scId : SchedContextId) (eligibleAt : Nat)
    (hCons : replenishQueueAffinityConsistentOnCore st c)
    (hTarget : ∀ sc, st.getSchedContext? scId = some sc →
      ∀ tid, sc.boundThread = some tid → determineTargetCore st tid = c) :
    replenishQueueAffinityConsistentOnCore (replenishOnCore st c scId eligibleAt) c := by
  intro scId₀ t hMem sc hSc tid hBound
  rw [replenishOnCore_getSchedContext?] at hSc
  rw [replenishOnCore_determineTargetCore]
  rw [replenishOnCore_replenishQueueOnCore_self] at hMem
  rcases (mem_insertSorted_iff _ scId eligibleAt (scId₀, t)).mp hMem with hEq | hOld
  · -- the freshly scheduled entry: `scId₀ = scId`, covered by `hTarget`.
    have hScEq : scId₀ = scId := (Prod.mk.injEq .. ▸ hEq).1
    subst hScEq
    exact hTarget sc hSc tid hBound
  · -- a pre-existing entry: covered by the pre-state consistency.
    exact hCons scId₀ t hOld sc hSc tid hBound

-- ============================================================================
-- §6  SM5.H.4 — SchedContext replenishment migration on affinity change
-- ============================================================================

-- §6a  Structural helpers for the fold-of-inserts (the migration moves a
--      SchedContext's pending replenishments by re-inserting each into the
--      destination queue).

/-- WS-SM SM5.H.4: a member of a fold-of-inserts (all keyed by `scId`) is either
an original member of the seed queue `toQ`, or one of the inserted entries
`(scId, x.2)` for some `x` in the moved list.  The provenance lemma the migration
preservation proofs decompose membership with. -/
private theorem mem_foldl_insert_provenance (moved : List (SchedContextId × Nat))
    (scId : SchedContextId) (e : SchedContextId × Nat) :
    ∀ (toQ : ReplenishQueue),
      e ∈ (moved.foldl (fun q x => q.insert scId x.2) toQ).entries →
      e ∈ toQ.entries ∨ ∃ x ∈ moved, e = (scId, x.2) := by
  induction moved with
  | nil => intro toQ h; exact Or.inl h
  | cons hd tail ih =>
    intro toQ h
    rw [List.foldl_cons] at h
    rcases ih (toQ.insert scId hd.2) h with h' | ⟨x, hxMem, hxEq⟩
    · rcases (mem_insertSorted_iff _ scId hd.2 e).mp h' with hEq | hMem
      · exact Or.inr ⟨hd, List.mem_cons_self .., hEq⟩
      · exact Or.inl hMem
    · exact Or.inr ⟨x, List.mem_cons_of_mem _ hxMem, hxEq⟩

/-- WS-SM SM5.H.4: a fold-of-inserts preserves sorted-by-eligibility order. -/
private theorem foldl_insert_preserves_sorted (moved : List (SchedContextId × Nat))
    (scId : SchedContextId) :
    ∀ (toQ : ReplenishQueue), replenishQueueSorted toQ →
      replenishQueueSorted (moved.foldl (fun q x => q.insert scId x.2) toQ) := by
  induction moved with
  | nil => intro toQ h; exact h
  | cons hd tail ih =>
    intro toQ h
    rw [List.foldl_cons]
    exact ih (toQ.insert scId hd.2) (insert_preserves_sorted h)

/-- WS-SM SM5.H.4: a fold-of-inserts preserves the cached-size invariant. -/
private theorem foldl_insert_preserves_sizeConsistent (moved : List (SchedContextId × Nat))
    (scId : SchedContextId) :
    ∀ (toQ : ReplenishQueue), replenishQueueSizeConsistent toQ →
      replenishQueueSizeConsistent (moved.foldl (fun q x => q.insert scId x.2) toQ) := by
  induction moved with
  | nil => intro toQ h; exact h
  | cons hd tail ih =>
    intro toQ h
    rw [List.foldl_cons]
    exact ih (toQ.insert scId hd.2) (insert_sizeConsistent h)

/- WS-SM SM5.H.4 (plan §3.8): `migrateSchedContextReplenishment st scId fromCore
toCore` migrates SchedContext `scId`'s pending replenishments from core `fromCore`'s
replenish queue to core `toCore`'s — removes every `(scId, _)` entry from
`fromCore` and re-inserts each at its original eligibility time into `toCore` (a
fold of `ReplenishQueue.insert`s).  A no-op when `fromCore = toCore`.  Writes only
the two replenish-queue slots; the object store, every run queue, and every other
per-core slot are untouched — so `getSchedContext?` / `determineTargetCore` are
unchanged by the migration itself.  Production def in
`Scheduler/Operations/Core.lean`; the affinity-change composite composes it with
the run-queue migration to follow the thread to its new home core. -/

/-- WS-SM SM5.H.4: a self-migration (`fromCore = toCore`) is the identity. -/
@[simp] theorem migrateSchedContextReplenishment_noop (st : SystemState)
    (scId : SchedContextId) (c : CoreId) :
    migrateSchedContextReplenishment st scId c c = st := by
  unfold migrateSchedContextReplenishment; rw [if_pos rfl]

/-- WS-SM SM5.H.4: the migration never touches the object store. -/
@[simp] theorem migrateSchedContextReplenishment_objects (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) :
    (migrateSchedContextReplenishment st scId fromCore toCore).objects = st.objects := by
  unfold migrateSchedContextReplenishment; split <;> rfl

/-- WS-SM SM5.H.4: the migration never advances the machine timer. -/
@[simp] theorem migrateSchedContextReplenishment_machine (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) :
    (migrateSchedContextReplenishment st scId fromCore toCore).machine = st.machine := by
  unfold migrateSchedContextReplenishment; split <;> rfl

/-- WS-SM SM5.H.4: the migration frames every SchedContext resolution. -/
theorem migrateSchedContextReplenishment_getSchedContext? (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) (scId' : SchedContextId) :
    (migrateSchedContextReplenishment st scId fromCore toCore).getSchedContext? scId'
      = st.getSchedContext? scId' := by
  unfold SystemState.getSchedContext?; rw [migrateSchedContextReplenishment_objects]

/-- WS-SM SM5.H.4: the migration frames every thread's home core. -/
theorem migrateSchedContextReplenishment_determineTargetCore (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) (tid : SeLe4n.ThreadId) :
    determineTargetCore (migrateSchedContextReplenishment st scId fromCore toCore) tid
      = determineTargetCore st tid := by
  unfold determineTargetCore SystemState.getTcb?; rw [migrateSchedContextReplenishment_objects]

/-- WS-SM SM5.H.4: core `toCore`'s post-migration replenish queue is the fold of
`scId`-inserts onto its pre-state queue (when `fromCore ≠ toCore`). -/
theorem migrateSchedContextReplenishment_replenishQueueOnCore_to (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) (h : fromCore ≠ toCore) :
    (migrateSchedContextReplenishment st scId fromCore toCore).scheduler.replenishQueueOnCore toCore
      = ((st.scheduler.replenishQueueOnCore fromCore).entries.filter (fun e => e.1 == scId)).foldl
          (fun q e => q.insert scId e.2) (st.scheduler.replenishQueueOnCore toCore) := by
  unfold migrateSchedContextReplenishment; rw [if_neg h]
  exact SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_self _ _ _

/-- WS-SM SM5.H.4: core `fromCore`'s post-migration replenish queue is its
pre-state queue with all `scId` entries removed (when `fromCore ≠ toCore`). -/
theorem migrateSchedContextReplenishment_replenishQueueOnCore_from (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) (h : fromCore ≠ toCore) :
    (migrateSchedContextReplenishment st scId fromCore toCore).scheduler.replenishQueueOnCore fromCore
      = (st.scheduler.replenishQueueOnCore fromCore).remove scId := by
  unfold migrateSchedContextReplenishment; rw [if_neg h]
  rw [SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ _ _ _ (Ne.symm h)]
  exact SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_self _ _ _

/-- WS-SM SM5.H.4: a core `c'` other than `fromCore` / `toCore` has its replenish
queue untouched by the migration. -/
theorem migrateSchedContextReplenishment_replenishQueueOnCore_other (st : SystemState)
    (scId : SchedContextId) (fromCore toCore c' : CoreId)
    (hFrom : fromCore ≠ c') (hTo : toCore ≠ c') :
    (migrateSchedContextReplenishment st scId fromCore toCore).scheduler.replenishQueueOnCore c'
      = st.scheduler.replenishQueueOnCore c' := by
  unfold migrateSchedContextReplenishment
  by_cases h : fromCore = toCore
  · rw [if_pos h]
  · rw [if_neg h]
    rw [SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ _ _ _ hTo,
        SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ _ _ _ hFrom]

-- §6b  Structural facts: the migration genuinely *moves* `scId`'s entries.

/-- WS-SM SM5.H.4: after a migration (`fromCore ≠ toCore`), **no** `scId`
replenishment remains in `fromCore`'s queue — they were all removed. -/
theorem migrateSchedContextReplenishment_fromCore_excludes_scId (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) (h : fromCore ≠ toCore) (t : Nat) :
    (scId, t) ∉ ((migrateSchedContextReplenishment st scId fromCore toCore).scheduler.replenishQueueOnCore fromCore).entries := by
  rw [migrateSchedContextReplenishment_replenishQueueOnCore_from st scId fromCore toCore h]
  intro hMem
  exact (mem_remove_entries hMem).2 rfl

/-- WS-SM SM5.H.4: every entry in `toCore`'s post-migration queue either was
already there, or is one of `scId`'s migrated entries (a `(scId, _)` pair drawn
from `fromCore`'s pre-state queue).  The membership decomposition the affinity /
pipeline preservation proofs use. -/
theorem migrateSchedContextReplenishment_mem_toCore (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) (h : fromCore ≠ toCore)
    (e : SchedContextId × Nat)
    (hMem : e ∈ ((migrateSchedContextReplenishment st scId fromCore toCore).scheduler.replenishQueueOnCore toCore).entries) :
    e ∈ (st.scheduler.replenishQueueOnCore toCore).entries ∨
      (e.1 = scId ∧ e ∈ (st.scheduler.replenishQueueOnCore fromCore).entries) := by
  rw [migrateSchedContextReplenishment_replenishQueueOnCore_to st scId fromCore toCore h] at hMem
  rcases mem_foldl_insert_provenance _ scId e _ hMem with hOld | ⟨x, hxMem, hxEq⟩
  · exact Or.inl hOld
  · have hxFilt := List.mem_filter.mp hxMem
    have hxKey : x.1 = scId := eq_of_beq hxFilt.2
    have hex : e = x := by rw [hxEq, ← hxKey]
    exact Or.inr ⟨by rw [hxEq], hex ▸ hxFilt.1⟩

-- §6b  SM5.H.3 — the migration preserves replenish-queue validity.

/-- WS-SM SM5.H.3 (plan §6.1 `replenishQueueOnCore_wellFormed`): the migration
preserves replenish-queue validity on **every** core.  `fromCore`'s queue is a
`remove` (sorted + size preserved); `toCore`'s is a fold of `insert`s (likewise);
every other core's queue is untouched. -/
theorem migrateSchedContextReplenishment_preserves_replenishQueueValid_smp (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId)
    (hValid : ∀ c, replenishQueueValidOnCore st c) :
    ∀ c, replenishQueueValidOnCore (migrateSchedContextReplenishment st scId fromCore toCore) c := by
  intro c
  by_cases hEq : fromCore = toCore
  · subst hEq; rw [migrateSchedContextReplenishment_noop]; exact hValid c
  · by_cases hcf : c = fromCore
    · subst hcf
      unfold replenishQueueValidOnCore
      rw [migrateSchedContextReplenishment_replenishQueueOnCore_from st scId c toCore hEq]
      exact ⟨remove_preserves_sorted (hValid c).1, remove_sizeConsistent⟩
    · by_cases hct : c = toCore
      · subst hct
        unfold replenishQueueValidOnCore
        rw [migrateSchedContextReplenishment_replenishQueueOnCore_to st scId fromCore c hEq]
        exact ⟨foldl_insert_preserves_sorted _ scId _ (hValid c).1,
               foldl_insert_preserves_sizeConsistent _ scId _ (hValid c).2⟩
      · exact (replenishQueueValidOnCore_frame
          (migrateSchedContextReplenishment_replenishQueueOnCore_other st scId fromCore toCore c
            (Ne.symm hcf) (Ne.symm hct))).mpr (hValid c)

-- §6b  SM5.H.6 — the migration preserves replenishment-pipeline order.

/-- WS-SM SM5.H.6 (plan §6.1 `replenishmentPipelineOrder_perCore`): the migration
preserves replenishment-pipeline order on **every** core.  It never advances the
machine timer and only relocates existing entries (whose future-ness is inherited):
`fromCore`'s post-queue is a subset of its pre-queue, and `toCore`'s post-queue is
its pre-queue plus `scId`'s entries — which came from `fromCore`'s pre-queue, also
future by the pre-state pipeline order on `fromCore`.  Hence the SMP-wide
hypothesis `∀ c, replenishmentPipelineOrderOnCore st c`. -/
theorem migrateSchedContextReplenishment_preserves_replenishmentPipelineOrder_smp (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId)
    (hPipeline : ∀ c, replenishmentPipelineOrderOnCore st c) :
    ∀ c, replenishmentPipelineOrderOnCore (migrateSchedContextReplenishment st scId fromCore toCore) c := by
  intro c pair hMem
  rw [migrateSchedContextReplenishment_machine]
  by_cases hEq : fromCore = toCore
  · subst hEq; rw [migrateSchedContextReplenishment_noop] at hMem; exact hPipeline c pair hMem
  · by_cases hcf : c = fromCore
    · subst hcf
      rw [migrateSchedContextReplenishment_replenishQueueOnCore_from st scId c toCore hEq] at hMem
      exact hPipeline c pair (mem_remove_entries hMem).1
    · by_cases hct : c = toCore
      · subst hct
        rcases migrateSchedContextReplenishment_mem_toCore st scId fromCore c hEq pair hMem with hOld | ⟨_, hFromMem⟩
        · exact hPipeline c pair hOld
        · exact hPipeline fromCore pair hFromMem
      · rw [migrateSchedContextReplenishment_replenishQueueOnCore_other st scId fromCore toCore c
          (Ne.symm hcf) (Ne.symm hct)] at hMem
        exact hPipeline c pair hMem

-- §6c  SM5.H.4 — the composite (affinity write + migration) + affinity restoration

/-- WS-SM SM5.H.4: `determineTargetCore` reads only `getTcb?`, so equal TCB
resolutions give equal home cores.  The congruence the affinity-write home-core
frame rests on. -/
theorem determineTargetCore_congr_getTcb? (st₁ st₂ : SystemState) (tid : SeLe4n.ThreadId)
    (h : st₁.getTcb? tid = st₂.getTcb? tid) :
    determineTargetCore st₁ tid = determineTargetCore st₂ tid := by
  unfold determineTargetCore; rw [h]

/-- WS-SM SM5.H.4: the affinity write frames every *other* thread's home core
(`determineTargetCore`) — its only object write is at `targetTid.toObjId`. -/
theorem setThreadCpuAffinity_determineTargetCore_ne (st : SystemState)
    (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId) (other : SeLe4n.ThreadId)
    (st' : SystemState) (hInv : st.objects.invExt) (hNe : other ≠ targetTid)
    (h : setThreadCpuAffinity st targetTid affinity = .ok st') :
    determineTargetCore st' other = determineTargetCore st other :=
  determineTargetCore_congr_getTcb? st' st other
    (setThreadCpuAffinity_getTcb?_ne st targetTid affinity other st' hInv hNe h)

/-- WS-SM SM5.H.4: the affinity write frames every SchedContext resolution.  The
target write inserts a `.tcb`; at `targetTid.toObjId` the pre-state was already a
`.tcb` (`getTcb? targetTid = some tcb`), so `getSchedContext?` is `none` there both
before and after; at every other key the lookup is unchanged. -/
theorem setThreadCpuAffinity_getSchedContext? (st : SystemState)
    (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId) (st' : SystemState)
    (tcb : TCB) (hTcb : st.getTcb? targetTid = some tcb) (hInv : st.objects.invExt)
    (h : setThreadCpuAffinity st targetTid affinity = .ok st') (scId'' : SchedContextId) :
    st'.getSchedContext? scId'' = st.getSchedContext? scId'' := by
  unfold setThreadCpuAffinity at h
  simp only [hTcb, Except.ok.injEq] at h
  -- Keep `st'` a variable; record only its object-store value.  All object reads
  -- route through the `.get?` method form (AK7-clean — the raw `[·]?` bracket text
  -- the AK7 `RAW_LOOKUP_TID` metric counts never appears in this source).
  have hObjEq : st'.objects = st.objects.insert targetTid.toObjId (.tcb { tcb with cpuAffinity := affinity }) := by
    rw [← h]
  have hTcbGet : st.objects.get? targetTid.toObjId = some (.tcb tcb) := by
    rw [← RHTable_getElem?_eq_get?]
    exact (SystemState.getTcb?_eq_some_iff st targetTid tcb).mp hTcb
  by_cases hKey : scId''.toObjId = targetTid.toObjId
  · -- same object id: both `getSchedContext?` lookups land on a `.tcb` ⇒ `none`.
    have hPostNone : st'.getSchedContext? scId'' = none := by
      apply SystemState.getSchedContext?_none_of_tcb _ scId'' { tcb with cpuAffinity := affinity }
      rw [RHTable_getElem?_eq_get?, hObjEq, hKey]
      exact RobinHood.RHTable.getElem?_insert_self st.objects targetTid.toObjId _ hInv
    have hPreNone : st.getSchedContext? scId'' = none := by
      apply SystemState.getSchedContext?_none_of_tcb _ scId'' tcb
      rw [RHTable_getElem?_eq_get?, hKey]; exact hTcbGet
    rw [hPostNone, hPreNone]
  · -- different object id: the lookup is framed (`.get?` method form).
    have hframe : (st.objects.insert targetTid.toObjId (.tcb { tcb with cpuAffinity := affinity })).get? scId''.toObjId
        = st.objects.get? scId''.toObjId :=
      RobinHood.RHTable.getElem?_insert_ne st.objects targetTid.toObjId scId''.toObjId _
        (fun he => hKey (eq_of_beq he).symm) hInv
    unfold SystemState.getSchedContext?
    rw [hObjEq]
    simp only [RHTable_getElem?_eq_get?]
    rw [hframe]

-- §6c  Migration-level affinity behaviour (on a consistent input state).

/-- WS-SM SM5.H.4 / SM5.H.5: the migration *establishes* affinity consistency on
the destination core `toCore`, given `toCore`'s pre-existing entries are
consistent (`hConsTo`) and the migrated SchedContext is itself homed on `toCore`
(`hHome` — its bound thread's `determineTargetCore` is `toCore`).  The migrated
entries are precisely `scId`'s, covered by `hHome`; the rest are covered by
`hConsTo`. -/
theorem migrateSchedContextReplenishment_establishes_affinityConsistentOnCore_to
    (st : SystemState) (scId : SchedContextId) (fromCore toCore : CoreId) (h : fromCore ≠ toCore)
    (hConsTo : replenishQueueAffinityConsistentOnCore st toCore)
    (hHome : ∀ sc, st.getSchedContext? scId = some sc →
      ∀ tid, sc.boundThread = some tid → determineTargetCore st tid = toCore) :
    replenishQueueAffinityConsistentOnCore (migrateSchedContextReplenishment st scId fromCore toCore) toCore := by
  intro scId₀ t hMem sc₀ hSc tid hBound
  rw [migrateSchedContextReplenishment_getSchedContext?] at hSc
  rw [migrateSchedContextReplenishment_determineTargetCore]
  rcases migrateSchedContextReplenishment_mem_toCore st scId fromCore toCore h _ hMem with hOld | ⟨hKey, _⟩
  · exact hConsTo scId₀ t hOld sc₀ hSc tid hBound
  · subst hKey
    exact hHome sc₀ hSc tid hBound

/-- WS-SM SM5.H.4 / SM5.H.5: the migration *preserves* affinity consistency on the
source core `fromCore`, given its entries **other than** `scId`'s are consistent
(`hConsNonScId`).  The post-migration `fromCore` queue is the pre-state queue with
all `scId` entries removed — exactly the non-`scId` entries `hConsNonScId` covers
(the `scId` entries — the only ones the affinity change could have invalidated on
`fromCore` — are gone). -/
theorem migrateSchedContextReplenishment_establishes_affinityConsistentOnCore_from
    (st : SystemState) (scId : SchedContextId) (fromCore toCore : CoreId) (h : fromCore ≠ toCore)
    (hConsNonScId : ∀ (scId₀ : SchedContextId) (t : Nat),
      (scId₀, t) ∈ (st.scheduler.replenishQueueOnCore fromCore).entries → scId₀ ≠ scId →
        ∀ sc₀, st.getSchedContext? scId₀ = some sc₀ →
          ∀ tid, sc₀.boundThread = some tid → determineTargetCore st tid = fromCore) :
    replenishQueueAffinityConsistentOnCore (migrateSchedContextReplenishment st scId fromCore toCore) fromCore := by
  intro scId₀ t hMem sc₀ hSc tid hBound
  rw [migrateSchedContextReplenishment_getSchedContext?] at hSc
  rw [migrateSchedContextReplenishment_determineTargetCore]
  rw [migrateSchedContextReplenishment_replenishQueueOnCore_from st scId fromCore toCore h] at hMem
  have hRem := mem_remove_entries hMem
  exact hConsNonScId scId₀ t hRem.1 hRem.2 sc₀ hSc tid hBound

/-- WS-SM SM5.H.4 / SM5.H.5: the migration *preserves* affinity consistency on any
core `c'` other than `fromCore` / `toCore` — its replenish queue and the object
store are untouched. -/
theorem migrateSchedContextReplenishment_preserves_affinityConsistentOnCore_other
    (st : SystemState) (scId : SchedContextId) (fromCore toCore c' : CoreId)
    (hFrom : fromCore ≠ c') (hTo : toCore ≠ c')
    (hCons : replenishQueueAffinityConsistentOnCore st c') :
    replenishQueueAffinityConsistentOnCore (migrateSchedContextReplenishment st scId fromCore toCore) c' :=
  (replenishQueueAffinityConsistentOnCore_frame
    (migrateSchedContextReplenishment_replenishQueueOnCore_other st scId fromCore toCore c' hFrom hTo)
    (migrateSchedContextReplenishment_objects st scId fromCore toCore)).mpr hCons

-- §6c  Run-queue migration frame lemmas (the full-migration's run-queue step
--       frames the object store + every replenish queue, so the replenish-queue
--       theorems carry through the full composite).

/-- WS-SM SM5.H.4: the run-queue migration never touches the object store. -/
@[simp] theorem migrateRunQueueOnAffinityChange_objects (st : SystemState)
    (tid : SeLe4n.ThreadId) (fromCore toCore : CoreId) :
    (migrateRunQueueOnAffinityChange st tid fromCore toCore).objects = st.objects := by
  unfold migrateRunQueueOnAffinityChange
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

/-- WS-SM SM5.H.4: the run-queue migration never advances the machine timer. -/
@[simp] theorem migrateRunQueueOnAffinityChange_machine (st : SystemState)
    (tid : SeLe4n.ThreadId) (fromCore toCore : CoreId) :
    (migrateRunQueueOnAffinityChange st tid fromCore toCore).machine = st.machine := by
  unfold migrateRunQueueOnAffinityChange
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

/-- WS-SM SM5.H.4: the run-queue migration frames every core's **replenish** queue
(it writes only run-queue slots). -/
@[simp] theorem migrateRunQueueOnAffinityChange_replenishQueueOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (fromCore toCore c' : CoreId) :
    (migrateRunQueueOnAffinityChange st tid fromCore toCore).scheduler.replenishQueueOnCore c'
      = st.scheduler.replenishQueueOnCore c' := by
  unfold migrateRunQueueOnAffinityChange
  split
  · rfl
  · split
    · rfl
    · split
      · simp
      · rfl

/-- WS-SM SM5.H.4: the run-queue migration frames every SchedContext resolution. -/
theorem migrateRunQueueOnAffinityChange_getSchedContext? (st : SystemState)
    (tid : SeLe4n.ThreadId) (fromCore toCore : CoreId) (scId' : SchedContextId) :
    (migrateRunQueueOnAffinityChange st tid fromCore toCore).getSchedContext? scId'
      = st.getSchedContext? scId' := by
  unfold SystemState.getSchedContext?; rw [migrateRunQueueOnAffinityChange_objects]

/-- WS-SM SM5.H.4: the run-queue migration frames every thread's home core. -/
theorem migrateRunQueueOnAffinityChange_determineTargetCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (fromCore toCore : CoreId) (tid' : SeLe4n.ThreadId) :
    determineTargetCore (migrateRunQueueOnAffinityChange st tid fromCore toCore) tid'
      = determineTargetCore st tid' := by
  unfold determineTargetCore SystemState.getTcb?; rw [migrateRunQueueOnAffinityChange_objects]

-- §6c  The replenish-affinity restoration (generalised to any affinity, incl. unbind).

/-- WS-SM SM5.H.4 (the replenish-affinity restoration core): the affinity write
(`stSet`) followed by the SchedContext replenishment migration from the old home
core (`determineTargetCore st targetTid`) to the new home core (`newHome =
determineTargetCore stSet targetTid`) *restores* per-core CBS affinity consistency
on **every** core.

Generalised over `affinity` (the new home `newHome` is supplied via `hNewHome`,
which is `determineTargetCore_bound_eq_affinity` for `some c` and
`determineTargetCore_unbound_eq_bootCore` for `none`), so it covers both **bind**
and **unbind**.  Pre-state hypotheses: SchedContext-bound TCB (`hTcb`/`hBind`/
`hSc`/`hBound`); 1:1 binding (`hUnique`, from `schedContextBindingConsistent`);
whole state already affinity-consistent (`hCons`).  The migration moves `scId`
from `oldHome` to `newHome` where `determineTargetCore stSet targetTid = newHome`;
every other SchedContext's home core is unchanged (1:1 binding), so consistency is
preserved elsewhere and established for the migrated entries on `newHome`. -/
theorem schedContextReplMigration_consistent
    (st : SystemState) (targetTid : SeLe4n.ThreadId) (newHome : CoreId)
    (tcb : TCB) (scId : SchedContextId) (sc : SchedContext)
    (affinity : Option CoreId) (stSet : SystemState)
    (hTcb : st.getTcb? targetTid = some tcb)
    (hInv : st.objects.invExt)
    (hBind : tcb.schedContextBinding.scId? = some scId)
    (hSc : st.getSchedContext? scId = some sc)
    (hBound : sc.boundThread = some targetTid)
    (hUnique : ∀ (scId'' : SchedContextId) (sc'' : SchedContext),
      st.getSchedContext? scId'' = some sc'' → sc''.boundThread = some targetTid → scId'' = scId)
    (hCons : ∀ c, replenishQueueAffinityConsistentOnCore st c)
    (hSet : setThreadCpuAffinity st targetTid affinity = .ok stSet)
    (hNewHome : determineTargetCore stSet targetTid = newHome) :
    replenishQueueAffinityConsistent_smp
      (migrateSchedContextReplenishment stSet scId (determineTargetCore st targetTid) newHome) := by
  have hSchedEq : stSet.scheduler = st.scheduler :=
    setThreadCpuAffinity_preserves_scheduler st targetTid affinity stSet hSet
  have hScFrame : ∀ scId'', stSet.getSchedContext? scId'' = st.getSchedContext? scId'' :=
    fun scId'' => setThreadCpuAffinity_getSchedContext? st targetTid affinity stSet tcb hTcb hInv hSet scId''
  have hTgtSelf : determineTargetCore stSet targetTid = newHome := hNewHome
  have hTgtNe : ∀ other, other ≠ targetTid → determineTargetCore stSet other = determineTargetCore st other :=
    fun other hNe => setThreadCpuAffinity_determineTargetCore_ne st targetTid affinity other stSet hInv hNe hSet
  have hOldEntries : ∀ (c : CoreId) (t : Nat),
      (scId, t) ∈ (st.scheduler.replenishQueueOnCore c).entries →
      c = determineTargetCore st targetTid := by
    intro c t hMem
    exact (hCons c scId t hMem sc hSc targetTid hBound).symm
  have bridge : ∀ (c₀ : CoreId) (scId₀ : SchedContextId) (t : Nat) (sc₀ : SchedContext) (tid₀ : SeLe4n.ThreadId),
      (scId₀, t) ∈ (st.scheduler.replenishQueueOnCore c₀).entries →
      st.getSchedContext? scId₀ = some sc₀ → sc₀.boundThread = some tid₀ → scId₀ ≠ scId →
      determineTargetCore stSet tid₀ = c₀ := by
    intro c₀ scId₀ t sc₀ tid₀ hMem hSc₀ hBound₀ hNeScId
    have hConsC : determineTargetCore st tid₀ = c₀ := hCons c₀ scId₀ t hMem sc₀ hSc₀ tid₀ hBound₀
    have hNeTid : tid₀ ≠ targetTid := by
      intro hEq; subst hEq
      exact hNeScId (hUnique scId₀ sc₀ hSc₀ hBound₀)
    rw [hTgtNe tid₀ hNeTid]; exact hConsC
  have hStSetOff : ∀ c, c ≠ determineTargetCore st targetTid →
      replenishQueueAffinityConsistentOnCore stSet c := by
    intro c hcNeOld scId₀ t hMem sc₀ hSc₀ tid₀ hBound₀
    rw [hSchedEq] at hMem
    rw [hScFrame scId₀] at hSc₀
    have hNeScId : scId₀ ≠ scId := fun hEq => hcNeOld (hOldEntries c t (hEq ▸ hMem))
    exact bridge c scId₀ t sc₀ tid₀ hMem hSc₀ hBound₀ hNeScId
  intro c
  by_cases hON : determineTargetCore st targetTid = newHome
  · rw [hON, migrateSchedContextReplenishment_noop]
    intro scId₀ t hMem sc₀ hSc₀ tid₀ hBound₀
    rw [hSchedEq] at hMem
    rw [hScFrame scId₀] at hSc₀
    by_cases hTid : tid₀ = targetTid
    · subst hTid
      have hScEq : scId₀ = scId := hUnique scId₀ sc₀ hSc₀ hBound₀
      subst hScEq
      exact hTgtSelf.trans ((hOldEntries c t hMem).trans hON).symm
    · rw [hTgtNe tid₀ hTid]
      exact hCons c scId₀ t hMem sc₀ hSc₀ tid₀ hBound₀
  · by_cases hcNew : c = newHome
    · subst hcNew
      refine migrateSchedContextReplenishment_establishes_affinityConsistentOnCore_to
        stSet scId _ c (fun hEq => hON hEq) (hStSetOff c (fun hEq => hON hEq.symm)) ?_
      intro sc' hSc' tid' hBound'
      rw [hScFrame scId] at hSc'
      have hScEq : sc = sc' := Option.some.inj (hSc ▸ hSc')
      subst hScEq
      have hTidEq : tid' = targetTid := (Option.some.inj (hBound ▸ hBound')).symm
      subst hTidEq
      exact hTgtSelf
    · by_cases hcOld : c = determineTargetCore st targetTid
      · subst hcOld
        refine migrateSchedContextReplenishment_establishes_affinityConsistentOnCore_from
          stSet scId (determineTargetCore st targetTid) newHome (fun hEq => hON hEq) ?_
        intro scId₀ t hMem hNeScId sc₀ hSc₀ tid₀ hBound₀
        rw [hSchedEq] at hMem
        rw [hScFrame scId₀] at hSc₀
        exact bridge (determineTargetCore st targetTid) scId₀ t sc₀ tid₀ hMem hSc₀ hBound₀ hNeScId
      · exact migrateSchedContextReplenishment_preserves_affinityConsistentOnCore_other
          stSet scId (determineTargetCore st targetTid) newHome c
          (fun hEq => hcOld hEq.symm) (fun hEq => hcNew hEq.symm) (hStSetOff c hcOld)

-- §6c  The full composite (affinity write + replenishment migration + run-queue
--      migration + cross-core SGI) shape theorems + the headline restoration.

/-- WS-SM SM5.H.4: the full composite rejects a non-TCB target (fail-closed). -/
theorem setThreadCpuAffinityWithMigration_error_of_no_tcb (st : SystemState)
    (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId) (executingCore : CoreId)
    (hTcb : st.getTcb? targetTid = none) :
    setThreadCpuAffinityWithMigration st targetTid affinity executingCore = .error .invalidArgument := by
  simp only [setThreadCpuAffinityWithMigration, hTcb]

/-- WS-SM SM5.H.4: for a SchedContext-**bound** target, the full composite's state
component is the affinity write `stSet`, followed by the replenishment migration
(old home → new home), followed by the run-queue migration. -/
theorem setThreadCpuAffinityWithMigration_bound_state_eq (st : SystemState)
    (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId) (executingCore : CoreId)
    (tcb : TCB) (scId : SchedContextId)
    (hTcb : st.getTcb? targetTid = some tcb) (hBind : tcb.schedContextBinding.scId? = some scId)
    (stSet : SystemState) (hSet : setThreadCpuAffinity st targetTid affinity = .ok stSet)
    (st' : SystemState × Option (CoreId × SgiKind))
    (hStep : setThreadCpuAffinityWithMigration st targetTid affinity executingCore = .ok st') :
    st'.1 = migrateRunQueueOnAffinityChange
      (migrateSchedContextReplenishment stSet scId
        (determineTargetCore st targetTid) (determineTargetCore stSet targetTid))
      targetTid (determineTargetCore st targetTid) (determineTargetCore stSet targetTid) := by
  simp only [setThreadCpuAffinityWithMigration, hTcb, hSet, hBind] at hStep
  rw [← Except.ok.inj hStep]

/-- WS-SM SM5.H.4: for an **unbound** target (no SchedContext), the full composite's
state component is the affinity write `stSet` followed by the run-queue migration —
there is no replenishment schedule to migrate. -/
theorem setThreadCpuAffinityWithMigration_unbound_state_eq (st : SystemState)
    (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId) (executingCore : CoreId)
    (tcb : TCB)
    (hTcb : st.getTcb? targetTid = some tcb) (hBind : tcb.schedContextBinding.scId? = none)
    (stSet : SystemState) (hSet : setThreadCpuAffinity st targetTid affinity = .ok stSet)
    (st' : SystemState × Option (CoreId × SgiKind))
    (hStep : setThreadCpuAffinityWithMigration st targetTid affinity executingCore = .ok st') :
    st'.1 = migrateRunQueueOnAffinityChange stSet
      targetTid (determineTargetCore st targetTid) (determineTargetCore stSet targetTid) := by
  simp only [setThreadCpuAffinityWithMigration, hTcb, hSet, hBind] at hStep
  rw [← Except.ok.inj hStep]

/-- WS-SM SM5.H.4 (plan §6.1 `schedContextMigration_consistent`, the headline): the
**full** affinity-change-with-migration composite (for **any** affinity — bind or
unbind) *restores* per-core CBS affinity consistency on **every** core for a
SchedContext-bound target.

The run-queue migration step frames every replenish queue + the object store, so
the replenish-affinity invariant reduces to the replenish-only restoration
(`schedContextReplMigration_consistent`), with the new home `determineTargetCore
stSet targetTid` (no separate `some`/`none` case split — the home core is whatever
the affinity write produced).  The 1:1 binding (`hUnique`, from
`schedContextBindingConsistent`) is what keeps every *other* SchedContext's home
core fixed across the affinity write. -/
theorem schedContextMigration_consistent
    (st : SystemState) (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId)
    (executingCore : CoreId)
    (tcb : TCB) (scId : SchedContextId) (sc : SchedContext)
    (st' : SystemState × Option (CoreId × SgiKind))
    (hTcb : st.getTcb? targetTid = some tcb)
    (hInv : st.objects.invExt)
    (hBind : tcb.schedContextBinding.scId? = some scId)
    (hSc : st.getSchedContext? scId = some sc)
    (hBound : sc.boundThread = some targetTid)
    (hUnique : ∀ (scId'' : SchedContextId) (sc'' : SchedContext),
      st.getSchedContext? scId'' = some sc'' → sc''.boundThread = some targetTid → scId'' = scId)
    (hCons : ∀ c, replenishQueueAffinityConsistentOnCore st c)
    (hStep : setThreadCpuAffinityWithMigration st targetTid affinity executingCore = .ok st') :
    replenishQueueAffinityConsistent_smp st'.1 := by
  obtain ⟨stSet, hSet⟩ := setThreadCpuAffinity_ok_of_tcb st targetTid affinity tcb hTcb
  rw [setThreadCpuAffinityWithMigration_bound_state_eq st targetTid affinity executingCore
        tcb scId hTcb hBind stSet hSet st' hStep]
  intro c
  rw [replenishQueueAffinityConsistentOnCore_frame
        (migrateRunQueueOnAffinityChange_replenishQueueOnCore _ _ _ _ c)
        (migrateRunQueueOnAffinityChange_objects _ _ _ _)]
  exact schedContextReplMigration_consistent st targetTid (determineTargetCore stSet targetTid)
    tcb scId sc affinity stSet hTcb hInv hBind hSc hBound hUnique hCons hSet rfl c

-- ============================================================================
-- §7  SM5.H.7 — Per-core CBS budget accounting + the per-core CBS invariant
-- ============================================================================

/-- WS-SM SM5.H.7: the aggregate **per-core CBS invariant** on core `c` — its
replenish queue is well-formed (sorted-by-eligibility + size-consistent), every
queued replenishment is eligible strictly in the future (pipeline order), and
every queued SchedContext is homed on `c` (affinity consistency).  The composite
invariant the SM5.I per-core run loop maintains across a CBS tick, and the SM5.H
scheduling / migration operations preserve. -/
def perCoreCbsInvariant (st : SystemState) (c : CoreId) : Prop :=
  replenishQueueValidOnCore st c ∧
  replenishmentPipelineOrderOnCore st c ∧
  replenishQueueAffinityConsistentOnCore st c

/-- WS-SM SM5.H.7: the freshly-booted system satisfies the per-core CBS invariant
on every core (empty replenish queue). -/
theorem default_perCoreCbsInvariant (c : CoreId) :
    perCoreCbsInvariant (default : SystemState) c := by
  refine ⟨?_, ?_, ?_⟩
  · have hRepl : (default : SystemState).scheduler.replenishQueueOnCore c
        = SeLe4n.Kernel.ReplenishQueue.empty := (default_state_perCoreInitialized c).2.2.1
    unfold replenishQueueValidOnCore
    rw [hRepl]; exact ⟨empty_sorted, empty_sizeConsistent⟩
  · intro pair hMem
    have hRepl : (default : SystemState).scheduler.replenishQueueOnCore c
        = SeLe4n.Kernel.ReplenishQueue.empty := (default_state_perCoreInitialized c).2.2.1
    rw [hRepl] at hMem; simp [SeLe4n.Kernel.ReplenishQueue.empty] at hMem
  · exact default_replenishQueueAffinityConsistentOnCore c

/-- WS-SM SM5.H.7 (CBS scheduling maintains the per-core CBS invariant):
`replenishOnCore` preserves the aggregate per-core CBS invariant on core `c`,
provided the scheduled replenishment is eligible in the future (`hFuture`, which
the CBS engine guarantees via `now + period`, `period > 0`) and the scheduled
SchedContext is homed on `c` (`hTarget`, the invariant the live tick maintains).
Composes the SM5.H.3 validity, SM5.H.6 pipeline-order, and SM5.H.5 affinity
preservation. -/
theorem replenishOnCore_preserves_perCoreCbsInvariant (st : SystemState)
    (c : CoreId) (scId : SchedContextId) (eligibleAt : Nat)
    (hInv : perCoreCbsInvariant st c)
    (hFuture : eligibleAt > st.machine.timer)
    (hTarget : ∀ sc, st.getSchedContext? scId = some sc →
      ∀ tid, sc.boundThread = some tid → determineTargetCore st tid = c) :
    perCoreCbsInvariant (replenishOnCore st c scId eligibleAt) c :=
  ⟨replenishOnCore_preserves_replenishQueueValidOnCore st c scId eligibleAt hInv.1,
   replenishOnCore_preserves_replenishmentPipelineOrderOnCore st c scId eligibleAt hInv.2.1 hFuture,
   replenishOnCore_preserves_replenishQueueAffinityConsistentOnCore st c scId eligibleAt hInv.2.2 hTarget⟩

-- §7  SM5.H.7 — the CBS budget-bound (bandwidth) accounting.

/-- WS-SM SM5.H.7 (CBS budget accounting): `consumeBudget` preserves the CBS
bandwidth bound `budgetRemaining ≤ budget` — charging budget can only *decrease*
`budgetRemaining` (`consumeBudget_budgetRemaining_le`), so an already-bounded
remaining stays bounded.  The per-tick budget-charge half of the CBS isolation
guarantee. -/
theorem consumeBudget_preserves_le_budget (sc : SchedContext) (ticks : Nat)
    (h : sc.budgetRemaining.val ≤ sc.budget.val) :
    (consumeBudget sc ticks).budgetRemaining.val ≤ (consumeBudget sc ticks).budget.val := by
  have hle := consumeBudget_budgetRemaining_le sc ticks
  have hbudget : (consumeBudget sc ticks).budget = sc.budget := rfl
  rw [hbudget]
  exact Nat.le_trans hle h

/-- WS-SM SM5.H.7 (CBS budget accounting): `applyRefill` establishes the CBS
bandwidth bound `budgetRemaining ≤ budget` unconditionally — the refill is capped
at the `budget` ceiling (`applyRefill_le_budget`).  The replenishment half of the
CBS isolation guarantee: no replenishment can push a SchedContext over its
configured budget. -/
theorem applyRefill_preserves_le_budget (sc : SchedContext) (refillAmount : Nat) :
    (applyRefill sc refillAmount).budgetRemaining.val ≤ (applyRefill sc refillAmount).budget.val := by
  have hbudget : (applyRefill sc refillAmount).budget = sc.budget := rfl
  rw [hbudget]
  exact applyRefill_le_budget sc refillAmount

/-- WS-SM SM5.H.7 (CBS budget accounting): `scheduleReplenishment` keeps the bound
replenishment list within `maxReplenishments` (`truncateReplenishments_length_le`)
— the per-core replenishment schedule cannot grow without bound. -/
theorem scheduleReplenishment_replenishments_bounded (sc : SchedContext)
    (currentTime : Nat) (consumed : Budget) :
    (scheduleReplenishment sc currentTime consumed).replenishments.length ≤ maxReplenishments := by
  unfold scheduleReplenishment
  exact truncateReplenishments_length_le _

-- ============================================================================
-- §8  SM5.H.2 (B8) — `replenishScOnCore`: faithful `sc`-based scheduling
--     + SM5.H.6 UNCONDITIONAL pipeline-order preservation (from `period > 0`)
-- ============================================================================

/-- WS-SM SM5.H.2: the faithful `sc`-based scheduling primitive is the `scId`-keyed
`replenishOnCore` at the CBS-computed eligibility `now + sc.period.val`. -/
theorem replenishScOnCore_eq (st : SystemState) (c : CoreId) (sc : SchedContext) (now : Nat) :
    replenishScOnCore st c sc now = replenishOnCore st c sc.scId (now + sc.period.val) := rfl

/-- WS-SM SM5.H.2: `replenishScOnCore` frames the object store. -/
@[simp] theorem replenishScOnCore_objects (st : SystemState) (c : CoreId)
    (sc : SchedContext) (now : Nat) :
    (replenishScOnCore st c sc now).objects = st.objects := rfl

/-- WS-SM SM5.H.6 (the unconditional pipeline-order preservation): scheduling
`sc`'s replenishment at `now = machine.timer` preserves the replenishment-pipeline
order **without** a caller-supplied future-ness hypothesis — the eligibility
`machine.timer + sc.period.val` is strictly future because `sc.period > 0`
(`sc.wellFormed`'s first conjunct).  This is the SM5.H.6 obligation the faithful
`sc`-form discharges internally. -/
theorem replenishScOnCore_preserves_replenishmentPipelineOrderOnCore (st : SystemState)
    (c : CoreId) (sc : SchedContext)
    (hPipeline : replenishmentPipelineOrderOnCore st c) (hPos : 0 < sc.period.val) :
    replenishmentPipelineOrderOnCore (replenishScOnCore st c sc st.machine.timer) c := by
  rw [replenishScOnCore_eq]
  apply replenishOnCore_preserves_replenishmentPipelineOrderOnCore st c sc.scId _ hPipeline
  omega

/-- WS-SM SM5.H.6: the `0 < period` obligation is exactly `sc.wellFormed`'s first
conjunct, so a well-formed SchedContext's scheduling is unconditionally
pipeline-preserving. -/
theorem replenishScOnCore_preserves_replenishmentPipelineOrderOnCore_of_wf (st : SystemState)
    (c : CoreId) (sc : SchedContext)
    (hPipeline : replenishmentPipelineOrderOnCore st c) (hWf : sc.wellFormed) :
    replenishmentPipelineOrderOnCore (replenishScOnCore st c sc st.machine.timer) c :=
  replenishScOnCore_preserves_replenishmentPipelineOrderOnCore st c sc hPipeline
    (by have := hWf.1; simpa [Period.isPositive] using this)

-- ============================================================================
-- §9  SM5.H (C9) — object-store invariant (`invExt`) preservation
-- ============================================================================

/-- WS-SM SM5.H.2: `replenishOnCore` preserves the RobinHood object-store invariant
(it never touches the object store). -/
theorem replenishOnCore_preserves_objects_invExt (st : SystemState) (c : CoreId)
    (scId : SchedContextId) (eligibleAt : Nat) (h : st.objects.invExt) :
    (replenishOnCore st c scId eligibleAt).objects.invExt := by
  rw [replenishOnCore_objects]; exact h

/-- WS-SM SM5.H.4: `migrateSchedContextReplenishment` preserves `invExt`. -/
theorem migrateSchedContextReplenishment_preserves_objects_invExt (st : SystemState)
    (scId : SchedContextId) (fromCore toCore : CoreId) (h : st.objects.invExt) :
    (migrateSchedContextReplenishment st scId fromCore toCore).objects.invExt := by
  rw [migrateSchedContextReplenishment_objects]; exact h

/-- WS-SM SM5.H.4: the run-queue migration preserves `invExt`. -/
theorem migrateRunQueueOnAffinityChange_preserves_objects_invExt (st : SystemState)
    (tid : SeLe4n.ThreadId) (fromCore toCore : CoreId) (h : st.objects.invExt) :
    (migrateRunQueueOnAffinityChange st tid fromCore toCore).objects.invExt := by
  rw [migrateRunQueueOnAffinityChange_objects]; exact h

/-- WS-SM SM5.H.4: the full affinity-change composite preserves `invExt` — the
affinity write preserves it (the only object write is the target TCB's affinity
field, an insert at an existing key), and the replenish / run-queue migrations
never touch the object store. -/
theorem setThreadCpuAffinityWithMigration_preserves_objects_invExt (st : SystemState)
    (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId) (executingCore : CoreId)
    (hInv : st.objects.invExt) (st' : SystemState × Option (CoreId × SgiKind))
    (hStep : setThreadCpuAffinityWithMigration st targetTid affinity executingCore = .ok st') :
    st'.1.objects.invExt := by
  cases hTcb : st.getTcb? targetTid with
  | none =>
      rw [setThreadCpuAffinityWithMigration_error_of_no_tcb st targetTid affinity executingCore hTcb] at hStep
      simp at hStep
  | some tcb =>
      obtain ⟨stSet, hSet⟩ := setThreadCpuAffinity_ok_of_tcb st targetTid affinity tcb hTcb
      have hStInv : stSet.objects.invExt :=
        setThreadCpuAffinity_preserves_objects_invExt st targetTid affinity stSet hInv hSet
      cases hBind : tcb.schedContextBinding.scId? with
      | some scId =>
          rw [setThreadCpuAffinityWithMigration_bound_state_eq st targetTid affinity executingCore
                tcb scId hTcb hBind stSet hSet st' hStep,
              migrateRunQueueOnAffinityChange_objects, migrateSchedContextReplenishment_objects]
          exact hStInv
      | none =>
          rw [setThreadCpuAffinityWithMigration_unbound_state_eq st targetTid affinity executingCore
                tcb hTcb hBind stSet hSet st' hStep,
              migrateRunQueueOnAffinityChange_objects]
          exact hStInv

-- ============================================================================
-- §10  SM5.H (A1) — lock-set footprints over `SchedLockId`
-- ============================================================================
--
-- Every SM5.H operation declares its cross-domain lock footprint over the SM5.A
-- `SchedLockId` order (object < runQueue < replenishQueue, plan §4.4, then by
-- `core.val` within a kind).  The migration / composite are the first SM5
-- operations holding **two locks of the same kind** (`replenishQueue ⟨fromCore⟩`
-- and `⟨toCore⟩`, / `runQueue` likewise); their ascending acquisition order (the
-- SM3.D deadlock-freedom ladder) is certified by `_pairwise_le_of_core_le` under
-- `fromCore.val ≤ toCore.val` (the canonical order the SM3.B `lockAcquireSequence`
-- sort produces for either argument order).

/-- WS-SM SM5.H.2 (lock-set): `replenishOnCore c` writes only core `c`'s
replenish-queue slot. -/
def replenishOnCoreLockSet (c : CoreId) : List (SchedLockId × Concurrency.AccessMode) :=
  [ (SchedLockId.replenishQueue ⟨c⟩, .write) ]

/-- SM5.H.2: the footprint is the single per-core replenish-queue write lock. -/
@[simp] theorem replenishOnCoreLockSet_length (c : CoreId) :
    (replenishOnCoreLockSet c).length = 1 := rfl

/-- SM5.H.2: the footprint is write-only. -/
theorem replenishOnCoreLockSet_write_only (c : CoreId) :
    ∀ p ∈ replenishOnCoreLockSet c, p.2 = Concurrency.AccessMode.write := by
  intro p hp; simp only [replenishOnCoreLockSet, List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp; rfl

/-- SM5.H.2: the footprint contains core `c`'s replenish-queue write lock. -/
theorem replenishOnCoreLockSet_contains_replenishQueue_write (c : CoreId) :
    (SchedLockId.replenishQueue ⟨c⟩, Concurrency.AccessMode.write) ∈ replenishOnCoreLockSet c := by
  simp [replenishOnCoreLockSet]

/-- SM5.H.2: the footprint is within the SM3.D `maxLockSetSize` (= 8) cap. -/
theorem replenishOnCoreLockSet_size_le_maxLockSetSize (c : CoreId) :
    (replenishOnCoreLockSet c).length ≤ 8 := by rw [replenishOnCoreLockSet_length]; decide

/-- WS-SM SM5.H.4 (lock-set): `migrateSchedContextReplenishment fromCore toCore`
writes both cores' replenish-queue slots. -/
def migrateSchedContextReplenishmentLockSet (fromCore toCore : CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  [ (SchedLockId.replenishQueue ⟨fromCore⟩, .write)
  , (SchedLockId.replenishQueue ⟨toCore⟩, .write) ]

/-- SM5.H.4: the migration footprint is the two replenish-queue write locks. -/
@[simp] theorem migrateSchedContextReplenishmentLockSet_length (fromCore toCore : CoreId) :
    (migrateSchedContextReplenishmentLockSet fromCore toCore).length = 2 := rfl

/-- SM5.H.4: the migration footprint is write-only. -/
theorem migrateSchedContextReplenishmentLockSet_write_only (fromCore toCore : CoreId) :
    ∀ p ∈ migrateSchedContextReplenishmentLockSet fromCore toCore, p.2 = Concurrency.AccessMode.write := by
  intro p hp
  simp only [migrateSchedContextReplenishmentLockSet, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h <;> subst h <;> rfl

/-- SM5.H.4: for distinct cores the migration footprint's keys are duplicate-free. -/
theorem migrateSchedContextReplenishmentLockSet_keys_nodup (fromCore toCore : CoreId)
    (h : fromCore ≠ toCore) :
    ((migrateSchedContextReplenishmentLockSet fromCore toCore).map (·.1)).Nodup := by
  simp only [migrateSchedContextReplenishmentLockSet, List.map_cons, List.map_nil]
  refine List.Pairwise.cons (fun a ha => ?_) (List.pairwise_singleton _ _)
  rw [List.mem_singleton] at ha; subst ha
  intro hEq
  exact h (congrArg ReplenishQueueLockId.core (SchedLockId.replenishQueue.inj hEq))

/-- SM5.H.4 (plan §4.4 / SM3.D ladder): under the canonical core order
`fromCore.val ≤ toCore.val`, the migration footprint's keys are ascending — a valid
`withLockSet` acquisition sequence. -/
theorem migrateSchedContextReplenishmentLockSet_pairwise_le_of_core_le (fromCore toCore : CoreId)
    (h : fromCore.val ≤ toCore.val) :
    ((migrateSchedContextReplenishmentLockSet fromCore toCore).map (·.1)).Pairwise (· ≤ ·) := by
  simp only [migrateSchedContextReplenishmentLockSet, List.map_cons, List.map_nil]
  refine List.Pairwise.cons (fun a ha => ?_) (List.pairwise_singleton _ _)
  rw [List.mem_singleton] at ha; subst ha; exact h

/-- SM5.H.4: the migration footprint is within the `maxLockSetSize` cap. -/
theorem migrateSchedContextReplenishmentLockSet_size_le_maxLockSetSize (fromCore toCore : CoreId) :
    (migrateSchedContextReplenishmentLockSet fromCore toCore).length ≤ 8 := by
  rw [migrateSchedContextReplenishmentLockSet_length]; decide

/-- WS-SM SM5.H.4 (lock-set): `migrateRunQueueOnAffinityChange fromCore toCore`
writes both cores' run-queue slots. -/
def migrateRunQueueOnAffinityChangeLockSet (fromCore toCore : CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  [ (SchedLockId.runQueue ⟨fromCore⟩, .write)
  , (SchedLockId.runQueue ⟨toCore⟩, .write) ]

/-- SM5.H.4: the run-queue-migration footprint is the two run-queue write locks. -/
@[simp] theorem migrateRunQueueOnAffinityChangeLockSet_length (fromCore toCore : CoreId) :
    (migrateRunQueueOnAffinityChangeLockSet fromCore toCore).length = 2 := rfl

/-- SM5.H.4: under the canonical core order the run-queue-migration footprint's keys
are ascending. -/
theorem migrateRunQueueOnAffinityChangeLockSet_pairwise_le_of_core_le (fromCore toCore : CoreId)
    (h : fromCore.val ≤ toCore.val) :
    ((migrateRunQueueOnAffinityChangeLockSet fromCore toCore).map (·.1)).Pairwise (· ≤ ·) := by
  simp only [migrateRunQueueOnAffinityChangeLockSet, List.map_cons, List.map_nil]
  refine List.Pairwise.cons (fun a ha => ?_) (List.pairwise_singleton _ _)
  rw [List.mem_singleton] at ha; subst ha; exact h

/-- WS-SM SM5.H.4 (lock-set): the **complete** footprint of the full
affinity-change-with-migration composite — the object-store write lock (the
affinity write, an SM3.A.10 table-level write), the two run-queue write locks
(the run-queue migration), and the two replenish-queue write locks (the
replenishment migration), in plan §4.4 ascending order (object < runQueue <
replenishQueue, then by `core.val`).  This is the footprint a `withLockSet`
caller (the SM5.I `tcbSetAffinity` runtime path) acquires. -/
def setThreadCpuAffinityWithMigrationLockSet (oldCore newCore : CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  [ (SchedLockId.object schedObjStoreLockId, .write)
  , (SchedLockId.runQueue ⟨oldCore⟩, .write)
  , (SchedLockId.runQueue ⟨newCore⟩, .write)
  , (SchedLockId.replenishQueue ⟨oldCore⟩, .write)
  , (SchedLockId.replenishQueue ⟨newCore⟩, .write) ]

/-- SM5.H.4: the composite footprint has the five cross-domain write locks. -/
@[simp] theorem setThreadCpuAffinityWithMigrationLockSet_length (oldCore newCore : CoreId) :
    (setThreadCpuAffinityWithMigrationLockSet oldCore newCore).length = 5 := rfl

/-- SM5.H.4: the composite footprint is write-only. -/
theorem setThreadCpuAffinityWithMigrationLockSet_write_only (oldCore newCore : CoreId) :
    ∀ p ∈ setThreadCpuAffinityWithMigrationLockSet oldCore newCore,
      p.2 = Concurrency.AccessMode.write := by
  intro p hp
  simp only [setThreadCpuAffinityWithMigrationLockSet, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h <;> subst h <;> rfl

/-- SM5.H.4: the composite footprint contains the object-store write lock (the
affinity write). -/
theorem setThreadCpuAffinityWithMigrationLockSet_contains_objStore_write (oldCore newCore : CoreId) :
    (SchedLockId.object schedObjStoreLockId, Concurrency.AccessMode.write)
      ∈ setThreadCpuAffinityWithMigrationLockSet oldCore newCore := by
  simp [setThreadCpuAffinityWithMigrationLockSet]

/-- SM5.H.4 (plan §4.4 / SM3.D ladder): under the canonical core order
`oldCore.val ≤ newCore.val`, the composite footprint's keys form an ascending
acquisition sequence (object < runQueue < replenishQueue, then by core). -/
theorem setThreadCpuAffinityWithMigrationLockSet_pairwise_le_of_core_le (oldCore newCore : CoreId)
    (h : oldCore.val ≤ newCore.val) :
    ((setThreadCpuAffinityWithMigrationLockSet oldCore newCore).map (·.1)).Pairwise (· ≤ ·) := by
  have hObjRq : ∀ (r : RunQueueLockId), SchedLockId.object schedObjStoreLockId ≤ SchedLockId.runQueue r :=
    fun r => (SchedLockId.object_lt_runQueue _ _).1
  have hObjRpq : ∀ (r : ReplenishQueueLockId), SchedLockId.object schedObjStoreLockId ≤ SchedLockId.replenishQueue r :=
    fun r => (SchedLockId.object_lt_replenishQueue _ _).1
  have hRqRpq : ∀ (q : RunQueueLockId) (r : ReplenishQueueLockId),
      SchedLockId.runQueue q ≤ SchedLockId.replenishQueue r := fun q r => (SchedLockId.runQueue_lt_replenishQueue _ _).1
  simp only [setThreadCpuAffinityWithMigrationLockSet, List.map_cons, List.map_nil]
  refine List.Pairwise.cons (fun a ha => ?_) (List.Pairwise.cons (fun a ha => ?_)
    (List.Pairwise.cons (fun a ha => ?_) (List.Pairwise.cons (fun a ha => ?_)
      (List.pairwise_singleton _ _))))
  · rcases List.mem_cons.mp ha with rfl | ha
    · exact hObjRq _
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hObjRq _
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hObjRpq _
    rcases List.mem_singleton.mp ha with rfl; exact hObjRpq _
  · rcases List.mem_cons.mp ha with rfl | ha
    · exact h
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hRqRpq _ _
    rcases List.mem_singleton.mp ha with rfl; exact hRqRpq _ _
  · rcases List.mem_cons.mp ha with rfl | ha
    · exact hRqRpq _ _
    rcases List.mem_singleton.mp ha with rfl; exact hRqRpq _ _
  · rcases List.mem_singleton.mp ha with rfl; exact h

/-- SM5.H.4 (WCRT): the composite footprint (5 locks) is within the SM3.D
`maxLockSetSize` (= 8) cap — so its worst-case lock-wait is bounded. -/
theorem setThreadCpuAffinityWithMigrationLockSet_size_le_maxLockSetSize (oldCore newCore : CoreId) :
    (setThreadCpuAffinityWithMigrationLockSet oldCore newCore).length ≤ 8 := by
  rw [setThreadCpuAffinityWithMigrationLockSet_length]; decide

-- ============================================================================
-- §11  SM5.H.4 — Scheduler-invariant (`runQueueOnCoreWellFormed`) preservation
--      for the full-thread-migration run-queue move + the whole composite.
--
-- The "Full thread migration" decision (the composite also dequeues the thread
-- from its old core's run queue and re-enqueues on the new core) makes
-- `runQueueOnCoreWellFormed` preservation a genuine obligation: a per-core
-- transition that rewrites two run-queue slots must keep both well-formed, else
-- `chooseThreadOnCore` (which assumes well-formedness) could fault.  The move is
-- a `remove` on the old slot + an `insert` on the new slot, both
-- well-formedness-preserving (`RunQueue.remove_preserves_wellFormed` /
-- `insert_preserves_wellFormed`); every other core's slot is framed untouched.
-- ============================================================================

/-- WS-SM SM5.H.4: the run-queue migration preserves run-queue well-formedness on
**every** core.  In the write branch it `remove`s `tid` from `fromCore`'s slot and
`insert`s it into `toCore`'s — both preserve `RunQueue.wellFormed`; every other
core's slot is left untouched (framed by the SM4.B per-core set/get algebra). -/
theorem migrateRunQueueOnAffinityChange_preserves_runQueueOnCoreWellFormed
    (st : SystemState) (tid : SeLe4n.ThreadId) (fromCore toCore c' : CoreId)
    (h : runQueueOnCoreWellFormed st.scheduler c') :
    runQueueOnCoreWellFormed (migrateRunQueueOnAffinityChange st tid fromCore toCore).scheduler c' := by
  unfold migrateRunQueueOnAffinityChange
  split
  · exact h
  · split
    · exact h
    · split
      · -- write branch: scheduler = (setRunQueueOnCore fromCore rqFrom).setRunQueueOnCore toCore rqTo
        rename_i tcb _ _
        unfold runQueueOnCoreWellFormed at h ⊢
        by_cases hToc : toCore = c'
        · subst hToc
          simp only [SeLe4n.Model.SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
          exact RunQueue.insert_preserves_wellFormed _ h _ _
        · rw [SeLe4n.Model.SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hToc]
          by_cases hFromc : fromCore = c'
          · subst hFromc
            simp only [SeLe4n.Model.SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
            exact RunQueue.remove_preserves_wellFormed _ h _
          · rw [SeLe4n.Model.SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hFromc]
            exact h
      · exact h

/-- WS-SM SM5.H.4 (frame): the replenishment migration leaves **every** run-queue
slot untouched (it writes only replenish-queue slots) — so it preserves
run-queue well-formedness on every core trivially. -/
@[simp] theorem migrateSchedContextReplenishment_runQueueOnCore (st : SystemState)
    (scId : SchedContextId) (fromCore toCore c' : CoreId) :
    (migrateSchedContextReplenishment st scId fromCore toCore).scheduler.runQueueOnCore c'
      = st.scheduler.runQueueOnCore c' := by
  unfold migrateSchedContextReplenishment
  split
  · rfl
  · simp

/-- WS-SM SM5.H.4: the **full** affinity-change-with-migration composite preserves
run-queue well-formedness on every core.  Decomposes into the affinity write
(leaves the scheduler untouched), the optional replenishment migration (leaves
every run-queue slot untouched), and the run-queue migration
(`migrateRunQueueOnAffinityChange_preserves_runQueueOnCoreWellFormed`). -/
theorem setThreadCpuAffinityWithMigration_preserves_runQueueOnCoreWellFormed
    (st : SystemState) (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId)
    (executingCore c' : CoreId) (tcb : TCB)
    (st' : SystemState × Option (CoreId × SgiKind))
    (hTcb : st.getTcb? targetTid = some tcb)
    (h : runQueueOnCoreWellFormed st.scheduler c')
    (hStep : setThreadCpuAffinityWithMigration st targetTid affinity executingCore = .ok st') :
    runQueueOnCoreWellFormed st'.1.scheduler c' := by
  obtain ⟨stSet, hSet⟩ := setThreadCpuAffinity_ok_of_tcb st targetTid affinity tcb hTcb
  -- `stSet` shares `st`'s scheduler (the affinity write touches only the TCB object).
  have hSetSched : stSet.scheduler = st.scheduler :=
    setThreadCpuAffinity_preserves_scheduler st targetTid affinity stSet hSet
  have hSetWf : runQueueOnCoreWellFormed stSet.scheduler c' := by
    unfold runQueueOnCoreWellFormed at h ⊢; rw [hSetSched]; exact h
  cases hBind : tcb.schedContextBinding.scId? with
  | some scId =>
      rw [setThreadCpuAffinityWithMigration_bound_state_eq st targetTid affinity executingCore
        tcb scId hTcb hBind stSet hSet st' hStep]
      apply migrateRunQueueOnAffinityChange_preserves_runQueueOnCoreWellFormed
      -- run-queue migration's input is the replenishment migration of `stSet`.
      unfold runQueueOnCoreWellFormed at hSetWf ⊢
      rw [migrateSchedContextReplenishment_runQueueOnCore]
      exact hSetWf
  | none =>
      rw [setThreadCpuAffinityWithMigration_unbound_state_eq st targetTid affinity executingCore
        tcb hTcb hBind stSet hSet st' hStep]
      exact migrateRunQueueOnAffinityChange_preserves_runQueueOnCoreWellFormed
        stSet targetTid _ _ c' hSetWf

-- ============================================================================
-- §12  SM5.H.4 (B7) — grounding the `hUnique` 1:1-binding hypothesis in the
--      live `schedContextBindingConsistent` invariant.
--
-- The headline `schedContextMigration_consistent` takes `hUnique` (a thread is
-- bound by at most one SchedContext) as a hypothesis.  It is not assumed: it is
-- a *consequence* of the maintained `schedContextBindingConsistent` invariant —
-- a SchedContext bound to `targetTid` forces `targetTid`'s (unique) TCB binding
-- to name that SchedContext, so two SchedContexts bound to the same thread name
-- the same id.  This grounds `hUnique`, so the migration restoration discharges
-- from the live invariant surface (the form SM5.I consumes).
-- ============================================================================

/-- WS-SM SM5.H.4 (B7): under `schedContextBindingConsistent`, a thread is bound by
**at most one** SchedContext — the `hUnique` hypothesis of the headline migration
theorem, derived rather than assumed.  Two SchedContexts both reporting
`boundThread = some targetTid` force `targetTid`'s unique TCB binding to name each
of their ids, so the ids coincide. -/
theorem schedContextBindingConsistent_boundThread_unique
    (st : SystemState) (targetTid : SeLe4n.ThreadId)
    (hCons : schedContextBindingConsistent st)
    (scId : SchedContextId) (sc : SchedContext)
    (hSc : st.getSchedContext? scId = some sc)
    (hBound : sc.boundThread = some targetTid) :
    ∀ (scId'' : SchedContextId) (sc'' : SchedContext),
      st.getSchedContext? scId'' = some sc'' → sc''.boundThread = some targetTid → scId'' = scId := by
  intro scId'' sc'' hSc'' hBound''
  obtain ⟨tcb, hTcb, hb⟩ := hCons.2 scId sc
    ((SystemState.getSchedContext?_eq_some_iff st scId sc).mp hSc) targetTid hBound
  obtain ⟨tcb'', hTcb'', hb''⟩ := hCons.2 scId'' sc''
    ((SystemState.getSchedContext?_eq_some_iff st scId'' sc'').mp hSc'') targetTid hBound''
  -- The TCB at `targetTid` is unique, so `tcb'' = tcb`.
  rw [hTcb] at hTcb''
  injection hTcb'' with hObjEq
  injection hObjEq with htcbEq
  subst htcbEq
  -- `tcb.schedContextBinding` is a single value naming both ids.
  rcases hb with hb | ⟨_, hb⟩ <;> rcases hb'' with hb'' | ⟨_, hb''⟩
  · exact SchedContextBinding.bound.inj (hb''.symm.trans hb)
  · exact absurd (hb''.symm.trans hb) (by simp)
  · exact absurd (hb''.symm.trans hb) (by simp)
  · exact (SchedContextBinding.donated.inj (hb''.symm.trans hb)).1

/-- WS-SM SM5.H.4 (B7, grounded headline): the full affinity-change-with-migration
composite restores per-core CBS affinity consistency, with the 1:1-binding
hypothesis **discharged from the live `schedContextBindingConsistent`
invariant** — the form the SM5.I per-core run loop consumes (it maintains
`schedContextBindingConsistent`, not the bare `hUnique`). -/
theorem schedContextMigration_consistent_of_bindingConsistent
    (st : SystemState) (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId)
    (executingCore : CoreId)
    (tcb : TCB) (scId : SchedContextId) (sc : SchedContext)
    (st' : SystemState × Option (CoreId × SgiKind))
    (hTcb : st.getTcb? targetTid = some tcb)
    (hInv : st.objects.invExt)
    (hBind : tcb.schedContextBinding.scId? = some scId)
    (hSc : st.getSchedContext? scId = some sc)
    (hBound : sc.boundThread = some targetTid)
    (hBindCons : schedContextBindingConsistent st)
    (hCons : ∀ c, replenishQueueAffinityConsistentOnCore st c)
    (hStep : setThreadCpuAffinityWithMigration st targetTid affinity executingCore = .ok st') :
    replenishQueueAffinityConsistent_smp st'.1 :=
  schedContextMigration_consistent st targetTid affinity executingCore tcb scId sc st'
    hTcb hInv hBind hSc hBound
    (schedContextBindingConsistent_boundThread_unique st targetTid hBindCons scId sc hSc hBound)
    hCons hStep

-- ============================================================================
-- §13  SM5.H.4 (A5) — the FULL composite preserves the per-core CBS invariant
--      (`replenishQueueValid` + `replenishmentPipelineOrder` + affinity
--      consistency) on **every** core.
--
-- Decomposes the composite into its three production steps — the affinity write
-- (scheduler + machine untouched), the optional replenishment migration (the
-- SM5.H.3 / SM5.H.6 preservation), and the run-queue migration (frames every
-- replenish queue + the machine timer) — and bundles them with the §12 grounded
-- affinity restoration into the single per-core CBS-invariant SMP preservation.
-- ============================================================================

/-- WS-SM SM5.H.4: the affinity write leaves the machine state untouched (its only
write is the target TCB's `cpuAffinity` field in the object store). -/
theorem setThreadCpuAffinity_machine (st : SystemState) (targetTid : SeLe4n.ThreadId)
    (affinity : Option CoreId) (stSet : SystemState)
    (h : setThreadCpuAffinity st targetTid affinity = .ok stSet) :
    stSet.machine = st.machine := by
  unfold setThreadCpuAffinity at h
  cases hTcb : st.getTcb? targetTid with
  | none => simp [hTcb] at h
  | some tcb => simp only [hTcb, Except.ok.injEq] at h; subst h; rfl

/-- WS-SM SM5.H.4 (A5): the full composite preserves replenish-queue **validity**
on every core.  The affinity write shares `st`'s scheduler, the replenishment
migration preserves validity (SM5.H.3), and the run-queue migration frames every
replenish queue. -/
theorem setThreadCpuAffinityWithMigration_preserves_replenishQueueValid_smp
    (st : SystemState) (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId)
    (executingCore : CoreId) (tcb : TCB)
    (st' : SystemState × Option (CoreId × SgiKind))
    (hTcb : st.getTcb? targetTid = some tcb)
    (hValid : ∀ c, replenishQueueValidOnCore st c)
    (hStep : setThreadCpuAffinityWithMigration st targetTid affinity executingCore = .ok st') :
    ∀ c, replenishQueueValidOnCore st'.1 c := by
  obtain ⟨stSet, hSet⟩ := setThreadCpuAffinity_ok_of_tcb st targetTid affinity tcb hTcb
  have hSetSched := setThreadCpuAffinity_preserves_scheduler st targetTid affinity stSet hSet
  have hSetValid : ∀ c, replenishQueueValidOnCore stSet c := fun c =>
    (replenishQueueValidOnCore_frame (by rw [hSetSched])).mpr (hValid c)
  cases hBind : tcb.schedContextBinding.scId? with
  | some scId =>
      rw [setThreadCpuAffinityWithMigration_bound_state_eq st targetTid affinity executingCore
        tcb scId hTcb hBind stSet hSet st' hStep]
      intro c
      exact (replenishQueueValidOnCore_frame
        (migrateRunQueueOnAffinityChange_replenishQueueOnCore _ _ _ _ c)).mpr
          (migrateSchedContextReplenishment_preserves_replenishQueueValid_smp stSet scId _ _ hSetValid c)
  | none =>
      rw [setThreadCpuAffinityWithMigration_unbound_state_eq st targetTid affinity executingCore
        tcb hTcb hBind stSet hSet st' hStep]
      intro c
      exact (replenishQueueValidOnCore_frame
        (migrateRunQueueOnAffinityChange_replenishQueueOnCore _ _ _ _ c)).mpr (hSetValid c)

/-- WS-SM SM5.H.4 (A5): the full composite preserves replenishment-**pipeline
order** on every core.  None of the three steps advances the machine timer, and
only the replenishment migration relocates existing (future) entries (SM5.H.6). -/
theorem setThreadCpuAffinityWithMigration_preserves_replenishmentPipelineOrder_smp
    (st : SystemState) (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId)
    (executingCore : CoreId) (tcb : TCB)
    (st' : SystemState × Option (CoreId × SgiKind))
    (hTcb : st.getTcb? targetTid = some tcb)
    (hPipeline : ∀ c, replenishmentPipelineOrderOnCore st c)
    (hStep : setThreadCpuAffinityWithMigration st targetTid affinity executingCore = .ok st') :
    ∀ c, replenishmentPipelineOrderOnCore st'.1 c := by
  obtain ⟨stSet, hSet⟩ := setThreadCpuAffinity_ok_of_tcb st targetTid affinity tcb hTcb
  have hSetSched := setThreadCpuAffinity_preserves_scheduler st targetTid affinity stSet hSet
  have hSetMach := setThreadCpuAffinity_machine st targetTid affinity stSet hSet
  have hSetPipe : ∀ c, replenishmentPipelineOrderOnCore stSet c := fun c =>
    (replenishmentPipelineOrderOnCore_frame (by rw [hSetSched]) (by rw [hSetMach])).mpr (hPipeline c)
  cases hBind : tcb.schedContextBinding.scId? with
  | some scId =>
      rw [setThreadCpuAffinityWithMigration_bound_state_eq st targetTid affinity executingCore
        tcb scId hTcb hBind stSet hSet st' hStep]
      intro c
      exact (replenishmentPipelineOrderOnCore_frame
        (migrateRunQueueOnAffinityChange_replenishQueueOnCore _ _ _ _ c)
        (congrArg (·.timer) (migrateRunQueueOnAffinityChange_machine _ _ _ _))).mpr
          (migrateSchedContextReplenishment_preserves_replenishmentPipelineOrder_smp stSet scId _ _ hSetPipe c)
  | none =>
      rw [setThreadCpuAffinityWithMigration_unbound_state_eq st targetTid affinity executingCore
        tcb hTcb hBind stSet hSet st' hStep]
      intro c
      exact (replenishmentPipelineOrderOnCore_frame
        (migrateRunQueueOnAffinityChange_replenishQueueOnCore _ _ _ _ c)
        (congrArg (·.timer) (migrateRunQueueOnAffinityChange_machine _ _ _ _))).mpr (hSetPipe c)

/-- WS-SM SM5.H.4 (A5, the bundle): the full affinity-change-with-migration
composite preserves the **aggregate per-core CBS invariant**
(`perCoreCbsInvariant`) on **every** core, for a SchedContext-bound target, with
all hypotheses discharged from the live invariant surface
(`schedContextBindingConsistent`, `objects.invExt`, the per-core CBS invariant on
every core).  This is the SM5.I-consumed closure: the syscall path can migrate a
thread's affinity and know the whole CBS bookkeeping stays well-formed,
future-ordered, and affinity-consistent. -/
theorem setThreadCpuAffinityWithMigration_preserves_perCoreCbsInvariant_smp
    (st : SystemState) (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId)
    (executingCore : CoreId)
    (tcb : TCB) (scId : SchedContextId) (sc : SchedContext)
    (st' : SystemState × Option (CoreId × SgiKind))
    (hTcb : st.getTcb? targetTid = some tcb)
    (hInv : st.objects.invExt)
    (hBind : tcb.schedContextBinding.scId? = some scId)
    (hSc : st.getSchedContext? scId = some sc)
    (hBound : sc.boundThread = some targetTid)
    (hBindCons : schedContextBindingConsistent st)
    (hCbs : ∀ c, perCoreCbsInvariant st c)
    (hStep : setThreadCpuAffinityWithMigration st targetTid affinity executingCore = .ok st') :
    ∀ c, perCoreCbsInvariant st'.1 c := by
  have hValid := setThreadCpuAffinityWithMigration_preserves_replenishQueueValid_smp
    st targetTid affinity executingCore tcb st' hTcb (fun c => (hCbs c).1) hStep
  have hPipe := setThreadCpuAffinityWithMigration_preserves_replenishmentPipelineOrder_smp
    st targetTid affinity executingCore tcb st' hTcb (fun c => (hCbs c).2.1) hStep
  have hAff := schedContextMigration_consistent_of_bindingConsistent
    st targetTid affinity executingCore tcb scId sc st' hTcb hInv hBind hSc hBound hBindCons
    (fun c => (hCbs c).2.2) hStep
  exact fun c => ⟨hValid c, hPipe c, hAff c⟩

-- ============================================================================
-- §14  SM5.H.2 (A2/A4) — the production live-tick CBS bridge: the per-core timer
--      tick's replenish write IS `replenishOnCore`, and the tick preserves
--      replenish-queue validity on every core.
--
-- `replenishOnCore` / `replenishScOnCore` are the named SM5.H.2 CBS-replenishment
-- primitives.  `timerTickBudgetOnCore`'s bound-budget-exhausted branch open-codes
-- the *same* insert; this section proves they coincide, making the abstract
-- primitives the verified characterisation of the live CBS engine.  The bridge
-- rests on a small replenish-queue frame chain: the budget-exhausted branch's
-- only post-insert step (`timeoutBlockedThreads`) re-enqueues / reverts PIP for
-- IPC-blocked threads, touching only run-queue + object-store slots — never the
-- replenish queue.
-- ============================================================================

/-- WS-SM SM5.H (frame): a PIP-boost update never touches any replenish queue (it
writes only the boosted thread's TCB object + its boot-core run-queue bucket). -/
theorem updatePipBoost_replenishQueueOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : CoreId) :
    (PriorityInheritance.updatePipBoost st tid).scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
  simp only [PriorityInheritance.updatePipBoost]
  split
  · rename_i tcb hObj
    split
    · rfl
    · split
      · split
        · rfl
        · rfl
      · rfl
  · rfl

/-- WS-SM SM5.H (frame): reverting priority inheritance never touches any
replenish queue (every recursion step is a `updatePipBoost`). -/
theorem revertPriorityInheritance_replenishQueueOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) (fuel : Nat) :
    (PriorityInheritance.revertPriorityInheritance st tid fuel).scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
  induction fuel generalizing st tid with
  | zero => rfl
  | succ n ih =>
    unfold PriorityInheritance.revertPriorityInheritance
    split
    · rw [ih]; exact updatePipBoost_replenishQueueOnCore st tid c
    · exact updatePipBoost_replenishQueueOnCore st tid c

/-- WS-SM SM5.H (frame): making a thread runnable never touches any replenish
queue (it writes only the boot-core run-queue slot). -/
theorem ensureRunnable_replenishQueueOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : CoreId) :
    (ensureRunnable st tid).scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
  unfold ensureRunnable
  split
  · rfl
  · split
    · simp
    · rfl

/-- WS-SM SM5.H (frame): timing out one IPC-blocked thread never touches any
replenish queue.  Its steps are an endpoint-queue removal (scheduler-invariant),
a TCB store (scheduler-invariant), a run-queue re-enqueue, and a PIP reversion —
all replenish-queue-preserving. -/
theorem timeoutThread_replenishQueueOnCore (epId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (st st' : SystemState) (c : CoreId)
    (h : timeoutThread epId isReceiveQ tid st = .ok st') :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold timeoutThread at h
  split at h
  · simp at h
  · rename_i st1 hER
    have hSched1 := endpointQueueRemove_scheduler_eq epId isReceiveQ tid st st1 hER
    split at h
    · simp at h
    · rename_i tcb hLk
      simp only [storeObject] at h
      split at h <;>
        · simp only [Except.ok.injEq] at h
          subst h
          first
            | rw [revertPriorityInheritance_replenishQueueOnCore]
            | skip
          rw [ensureRunnable_replenishQueueOnCore]
          show st1.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c
          rw [hSched1]

/-- WS-SM SM5.H (frame): timing out **all** of a SchedContext's IPC-blocked threads
never touches any replenish queue (each step is a `timeoutThread`). -/
theorem timeoutBlockedThreads_replenishQueueOnCore (st : SystemState)
    (scId : SeLe4n.SchedContextId) (c : CoreId) :
    (timeoutBlockedThreads st scId).1.scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
  unfold timeoutBlockedThreads
  -- prove the fold preserves the queue from any accumulator
  suffices hFold : ∀ (tids : List SeLe4n.ThreadId)
      (acc : SystemState × List (SeLe4n.ThreadId × KernelError)),
      (tids.foldl (fun (acc : SystemState × List (SeLe4n.ThreadId × KernelError)) tid =>
        match acc.1.getTcb? tid with
        | some tcb =>
          match tcbBlockingInfo tcb with
          | some (epId, isReceiveQ) =>
            match timeoutThread epId isReceiveQ tid acc.1 with
            | .ok st'' => (st'', acc.2)
            | .error e => (acc.1, acc.2 ++ [(tid, e)])
          | none => (acc.1, acc.2)
        | none => (acc.1, acc.2)) acc).1.scheduler.replenishQueueOnCore c
        = acc.1.scheduler.replenishQueueOnCore c by
    exact hFold _ (st, [])
  intro tids
  induction tids with
  | nil => intro acc; rfl
  | cons hd tail ih =>
    intro acc
    rw [List.foldl_cons, ih]
    -- the single head step preserves the queue
    split
    · split
      · split
        · next st'' heqTo =>
            exact timeoutThread_replenishQueueOnCore _ _ hd acc.1 st'' c heqTo
        · rfl
      · rfl
    · rfl

/-- WS-SM SM5.H.2 (A2, the production bridge): in the budget-**exhausted** branch the
live per-core timer tick's replenish-queue write on **every** core is exactly the
abstract `replenishOnCore` primitive's (scheduling `scId` at `now + sc.period`).
The post-insert `timeoutBlockedThreads` + `setLastTimeoutErrors` steps frame every
replenish queue, so the abstract primitive is the verified characterisation of the
live CBS engine. -/
theorem timerTickBudgetOnCore_bound_exhausted_replenish_eq
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (st' : SystemState) (b : Bool)
    (hBound : tcb.schedContextBinding = .bound scId)
    (hSc : st.getSchedContext? scId = some sc)
    (hBudget : sc.budgetRemaining.val ≤ 1)
    (hStep : timerTickBudgetOnCore st c tid tcb = .ok (st', b)) (c' : CoreId) :
    st'.scheduler.replenishQueueOnCore c'
      = (replenishOnCore st c scId (st.machine.timer + sc.period.val)).scheduler.replenishQueueOnCore c' := by
  simp only [timerTickBudgetOnCore, hBound, hSc, if_pos hBudget, Except.ok.injEq,
    Prod.mk.injEq] at hStep
  obtain ⟨hst, _⟩ := hStep
  subst hst
  simp only [replenishOnCore,
    SeLe4n.Model.SchedulerState.setLastTimeoutErrorsOnCore_replenishQueueOnCore,
    timeoutBlockedThreads_replenishQueueOnCore,
    SeLe4n.Model.SchedulerState.setRunQueueOnCore_replenishQueueOnCore]

/-- WS-SM SM5.H.4 (A4): the per-core budget tick preserves replenish-queue validity
on **every** core.  The unbound and bound-not-exhausted branches leave every
replenish queue untouched; the bound/donated-exhausted branch's write is the
SM5.H.2 `replenishOnCore` insert (A2 bridge), which preserves validity (SM5.H.3).
The per-core CBS-validity half of the SM5.I live-tick maintenance obligation. -/
theorem timerTickBudgetOnCore_donated_exhausted_replenish_eq
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId) (sc : SchedContext)
    (st' : SystemState) (b : Bool)
    (hDonated : tcb.schedContextBinding = .donated scId owner)
    (hSc : st.getSchedContext? scId = some sc)
    (hBudget : sc.budgetRemaining.val ≤ 1)
    (hStep : timerTickBudgetOnCore st c tid tcb = .ok (st', b)) (c' : CoreId) :
    st'.scheduler.replenishQueueOnCore c'
      = (replenishOnCore st c scId (st.machine.timer + sc.period.val)).scheduler.replenishQueueOnCore c' := by
  simp only [timerTickBudgetOnCore, hDonated, hSc, if_pos hBudget, Except.ok.injEq,
    Prod.mk.injEq] at hStep
  obtain ⟨hst, _⟩ := hStep
  subst hst
  simp only [replenishOnCore,
    SeLe4n.Model.SchedulerState.setLastTimeoutErrorsOnCore_replenishQueueOnCore,
    timeoutBlockedThreads_replenishQueueOnCore,
    SeLe4n.Model.SchedulerState.setRunQueueOnCore_replenishQueueOnCore]

theorem timerTickBudgetOnCore_preserves_replenishQueueValidOnCore
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (st' : SystemState) (b : Bool) (c' : CoreId)
    (hValid : ∀ c'', replenishQueueValidOnCore st c'')
    (hStep : timerTickBudgetOnCore st c tid tcb = .ok (st', b)) :
    replenishQueueValidOnCore st' c' := by
  match hB : tcb.schedContextBinding with
  | .unbound =>
      simp only [timerTickBudgetOnCore, hB] at hStep
      split at hStep <;>
        · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨hst, _⟩ := hStep; subst hst
          refine (replenishQueueValidOnCore_frame ?_).mpr (hValid c'); rfl
  | .bound scId =>
      match hSc : st.getSchedContext? scId with
      | some sc =>
          by_cases hBud : sc.budgetRemaining.val ≤ 1
          · rw [(replenishQueueValidOnCore_frame (timerTickBudgetOnCore_bound_exhausted_replenish_eq
              st c tid tcb scId sc st' b hB hSc hBud hStep c'))]
            exact replenishOnCore_preserves_replenishQueueValid_smp st c scId _ hValid c'
          · simp only [timerTickBudgetOnCore, hB, hSc, if_neg hBud, Except.ok.injEq,
              Prod.mk.injEq] at hStep
            obtain ⟨hst, _⟩ := hStep; subst hst
            refine (replenishQueueValidOnCore_frame ?_).mpr (hValid c'); rfl
      | none =>
          simp only [timerTickBudgetOnCore, hB, hSc] at hStep
          exact absurd hStep (by simp)
  | .donated scId owner =>
      match hSc : st.getSchedContext? scId with
      | some sc =>
          by_cases hBud : sc.budgetRemaining.val ≤ 1
          · rw [(replenishQueueValidOnCore_frame (timerTickBudgetOnCore_donated_exhausted_replenish_eq
              st c tid tcb scId owner sc st' b hB hSc hBud hStep c'))]
            exact replenishOnCore_preserves_replenishQueueValid_smp st c scId _ hValid c'
          · simp only [timerTickBudgetOnCore, hB, hSc, if_neg hBud, Except.ok.injEq,
              Prod.mk.injEq] at hStep
            obtain ⟨hst, _⟩ := hStep; subst hst
            refine (replenishQueueValidOnCore_frame ?_).mpr (hValid c'); rfl
      | none =>
          simp only [timerTickBudgetOnCore, hB, hSc] at hStep
          exact absurd hStep (by simp)

-- ============================================================================
-- §15  SM5.H.4 (C10) — memory-model happens-before for the migration's
--      cross-core visibility.
--
-- When the full-thread-migration composite re-homes a thread to a *remote* core
-- and emits the `.reschedule` SGI, the executing core's release-store of the
-- migrated thread's new run-queue / replenish-queue slots must be visible on the
-- new home core before that core takes the SGI and re-runs its scheduler.  This
-- is the *same* BKL release→acquire ordering the wake (SM5.C.4) and the PIP boost
-- (SM5.F.4) establish — the `dsb ish`-before-`GICD_SGIR` discipline (SM1.F.8) —
-- so we lift the verified `wakeOrdering_*` memory-model results; the events differ
-- only in *meaning* (the published location carries the migrated thread's new home
-- placement rather than a wake's run-queue insertion).
-- ============================================================================

/-- WS-SM SM5.H.4 (memory-model synchronizes-with): the migrating (executing) core's
release-store of the re-homed thread's new run-queue bucket **synchronizes-with** the
new home core's acquire-load when it services the migration's `.reschedule` SGI — the
ARM ARM B2.3.7 release/acquire edge the `dsb ish`-before-`GICD_SGIR` discipline
(SM1.F.8) establishes.  Lifts `wakeOrdering_synchronizesWith` (same trace shape). -/
theorem affinityMigrationOrdering_synchronizesWith
    (execCore newHomeCore : SeLe4n.Kernel.Concurrency.CoreId)
    (loc : SeLe4n.Kernel.Concurrency.AtomicLocation) (v : Nat) :
    SeLe4n.Kernel.Concurrency.synchronizesWith
      (SeLe4n.Kernel.Concurrency.wakeOrderingTrace execCore newHomeCore loc v)
      (SeLe4n.Kernel.Concurrency.wakeReleaseEvent execCore loc v)
      (SeLe4n.Kernel.Concurrency.wakeAcquireEvent newHomeCore loc v) :=
  SeLe4n.Kernel.Concurrency.wakeOrdering_synchronizesWith execCore newHomeCore loc v

/-- WS-SM SM5.H.4 (memory-model headline HB): the migration's re-homing publication
**happens-before** the new home core observes it on the `.reschedule` SGI.  When the
new home core services the SGI and re-runs `handleRescheduleSgiOnCore`, the migrated
thread's run-queue + replenish-queue placement is *guaranteed visible* — the
machine-checked statement of the migration's BKL ordering ("emit the SGI after the
re-homing is visible"), the affinity-migration analogue of `wakeOrdering_happensBefore`. -/
theorem affinityMigrationOrdering_happensBefore
    (execCore newHomeCore : SeLe4n.Kernel.Concurrency.CoreId)
    (loc : SeLe4n.Kernel.Concurrency.AtomicLocation) (v : Nat) :
    SeLe4n.Kernel.Concurrency.happensBefore
      (SeLe4n.Kernel.Concurrency.wakeOrderingTrace execCore newHomeCore loc v)
      (SeLe4n.Kernel.Concurrency.wakeReleaseEvent execCore loc v)
      (SeLe4n.Kernel.Concurrency.wakeAcquireEvent newHomeCore loc v) :=
  SeLe4n.Kernel.Concurrency.wakeOrdering_happensBefore execCore newHomeCore loc v

-- ============================================================================
-- §16  SM5.H.4 (D15) — the run-queue migration preserves the SM4.C scheduler
--      invariant `schedContextRunQueueConsistent_perCore` (run-queue membership
--      ⇒ positive SchedContext budget) on every core.
--
-- The full-thread-migration run-queue move relocates a thread's run-queue entry
-- but never touches the object store, so every queued thread's budget is framed.
-- A thread added to the new core's queue came from the old core's queue, where —
-- by the invariant — it had positive budget; a thread is only ever *removed* from
-- the old core's queue.  Hence the per-core run-queue↔budget consistency is
-- preserved on every core.
-- ============================================================================

/-- WS-SM SM5.H.4 (frame): the run-queue migration frames every TCB resolution. -/
theorem migrateRunQueueOnAffinityChange_getTcb? (st : SystemState)
    (tid : SeLe4n.ThreadId) (fromCore toCore : CoreId) (tid' : SeLe4n.ThreadId) :
    (migrateRunQueueOnAffinityChange st tid fromCore toCore).getTcb? tid'
      = st.getTcb? tid' := by
  unfold SystemState.getTcb?; rw [migrateRunQueueOnAffinityChange_objects]

/-- WS-SM SM5.H.4 (D15): the full-thread-migration run-queue move preserves the SM4.C
per-core run-queue↔budget consistency on **every** core, given the invariant holds
on every core pre-migration.  The migrated thread carries its (unchanged) positive
budget to the new core; every other core's membership only shrinks or is untouched. -/
theorem migrateRunQueueOnAffinityChange_preserves_schedContextRunQueueConsistent_perCore
    (st : SystemState) (tid : SeLe4n.ThreadId) (fromCore toCore c' : CoreId)
    (hAll : ∀ c, schedContextRunQueueConsistent_perCore st c) :
    schedContextRunQueueConsistent_perCore
      (migrateRunQueueOnAffinityChange st tid fromCore toCore) c' := by
  intro x hxMem tcb hTcb scId hBind
  rw [migrateRunQueueOnAffinityChange_getTcb?] at hTcb
  -- It suffices to find the SchedContext in `st` (objects are framed).
  suffices h : ∃ sc, st.getSchedContext? scId = some sc ∧ sc.budgetRemaining.val > 0 by
    obtain ⟨sc, hsc, hbud⟩ := h
    exact ⟨sc, by rw [migrateRunQueueOnAffinityChange_getSchedContext?]; exact hsc, hbud⟩
  -- Reduce the membership hypothesis to membership in some `st` run queue.
  revert hxMem
  unfold migrateRunQueueOnAffinityChange
  split
  · intro hxMem; exact hAll c' x hxMem tcb hTcb scId hBind
  · split
    · intro hxMem; exact hAll c' x hxMem tcb hTcb scId hBind
    · rename_i migTcb _
      split
      · -- write branch: the scheduler is the two-core run-queue update.
        rename_i hContains
        intro hxMem
        by_cases hToc : toCore = c'
        · -- c' = toCore: the migrated `x` is an old member or `tid` itself.
          subst hToc
          rw [SeLe4n.Model.SchedulerState.setRunQueueOnCore_runQueueOnCore_self] at hxMem
          rw [RunQueue.mem_toList_iff_mem, RunQueue.mem_insert] at hxMem
          rcases hxMem with hOld | hEq
          · exact hAll toCore x ((RunQueue.mem_toList_iff_mem _ _).mpr hOld) tcb hTcb scId hBind
          · subst hEq
            exact hAll fromCore x
              ((RunQueue.mem_toList_iff_mem _ _).mpr ((RunQueue.mem_iff_contains).mpr hContains))
              tcb hTcb scId hBind
        · rw [SeLe4n.Model.SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hToc] at hxMem
          by_cases hFromc : fromCore = c'
          · -- c' = fromCore: a removal can only shrink the membership.
            subst hFromc
            rw [SeLe4n.Model.SchedulerState.setRunQueueOnCore_runQueueOnCore_self] at hxMem
            rw [RunQueue.mem_toList_iff_mem, RunQueue.mem_remove] at hxMem
            exact hAll fromCore x ((RunQueue.mem_toList_iff_mem _ _).mpr hxMem.1) tcb hTcb scId hBind
          · rw [SeLe4n.Model.SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hFromc] at hxMem
            exact hAll c' x hxMem tcb hTcb scId hBind
      · intro hxMem; exact hAll c' x hxMem tcb hTcb scId hBind

-- ============================================================================
-- §17  SM5.H.4 (D15, composite) — the **full** affinity-change composite
--      (`setThreadCpuAffinityWithMigration`) preserves the SM4.C scheduler
--      invariant `schedContextRunQueueConsistent_perCore` on every core.
--
-- §16 proved this for the run-queue *move* in isolation; the composite also
-- performs the affinity write (`setThreadCpuAffinity`, which touches only the
-- target TCB's `cpuAffinity` field — never the binding, the SchedContext store,
-- or any run queue) and the optional SchedContext-replenishment migration
-- (`migrateSchedContextReplenishment`, which touches only replenish queues).
-- Neither disturbs the run-queue↔budget consistency, so the composite preserves
-- it.  This is the standalone companion of the run-queue-move helper D15 — the
-- whole-transition obligation a future SM5.I scheduler-bundle preservation
-- consumes.
-- ============================================================================

/-- WS-SM SM5.H.4 (frame): `setThreadCpuAffinity targetTid` reads back the
target's TCB with only `cpuAffinity` rewritten — its `schedContextBinding`,
`priority`, run-queue membership, etc. are untouched.  AK7-clean. -/
theorem setThreadCpuAffinity_getTcb?_self (st : SystemState)
    (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId) (st' : SystemState)
    (tcb : TCB) (hTcb : st.getTcb? targetTid = some tcb) (hInv : st.objects.invExt)
    (h : setThreadCpuAffinity st targetTid affinity = .ok st') :
    st'.getTcb? targetTid = some { tcb with cpuAffinity := affinity } := by
  unfold setThreadCpuAffinity at h
  rw [hTcb] at h
  simp only [Except.ok.injEq] at h
  subst h
  simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
  rw [RobinHood.RHTable.getElem?_insert_self st.objects targetTid.toObjId _ hInv]

/-- WS-SM SM5.H.4 (D15 helper): the affinity write preserves the SM4.C per-core
run-queue↔budget consistency.  It touches only the target TCB's `cpuAffinity`
(leaving every binding and every SchedContext budget intact) and no run queue, so
each queued thread keeps the same binding and the same (positive-budget) witness. -/
theorem setThreadCpuAffinity_preserves_schedContextRunQueueConsistent_perCore
    (st : SystemState) (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId)
    (st' : SystemState) (c : CoreId) (hInv : st.objects.invExt)
    (hCons : schedContextRunQueueConsistent_perCore st c)
    (h : setThreadCpuAffinity st targetTid affinity = .ok st') :
    schedContextRunQueueConsistent_perCore st' c := by
  -- The target TCB exists (else the write would have errored).
  obtain ⟨tcbT, hTcbT⟩ : ∃ tcb, st.getTcb? targetTid = some tcb := by
    cases hT : st.getTcb? targetTid with
    | none => unfold setThreadCpuAffinity at h; rw [hT] at h; simp at h
    | some tcb => exact ⟨tcb, rfl⟩
  have hSched : st'.scheduler = st.scheduler :=
    setThreadCpuAffinity_preserves_scheduler st targetTid affinity st' h
  have hScFrame : ∀ scId'', st'.getSchedContext? scId'' = st.getSchedContext? scId'' :=
    fun scId'' => setThreadCpuAffinity_getSchedContext? st targetTid affinity st' tcbT hTcbT hInv h scId''
  intro x hxMem tcb' hTcb' scId hBind
  rw [hSched] at hxMem
  by_cases hx : x = targetTid
  · rw [hx] at hxMem hTcb'
    rw [setThreadCpuAffinity_getTcb?_self st targetTid affinity st' tcbT hTcbT hInv h] at hTcb'
    injection hTcb' with hEq
    subst hEq
    -- `{tcbT with cpuAffinity := _}.schedContextBinding = tcbT.schedContextBinding`
    have hBindSt : tcbT.schedContextBinding.scId? = some scId := hBind
    obtain ⟨sc, hsc, hbud⟩ := hCons targetTid hxMem tcbT hTcbT scId hBindSt
    exact ⟨sc, by rw [hScFrame]; exact hsc, hbud⟩
  · have hNe := setThreadCpuAffinity_getTcb?_ne st targetTid affinity x st' hInv hx h
    rw [hNe] at hTcb'
    obtain ⟨sc, hsc, hbud⟩ := hCons x hxMem tcb' hTcb' scId hBind
    exact ⟨sc, by rw [hScFrame]; exact hsc, hbud⟩

/-- WS-SM SM5.H.4 (D15 helper): the SchedContext-replenishment migration preserves
the SM4.C per-core run-queue↔budget consistency.  It writes only replenish queues,
so every run queue, every TCB, and every SchedContext is framed. -/
theorem migrateSchedContextReplenishment_preserves_schedContextRunQueueConsistent_perCore
    (st : SystemState) (scId : SchedContextId) (fromCore toCore c' : CoreId)
    (hCons : schedContextRunQueueConsistent_perCore st c') :
    schedContextRunQueueConsistent_perCore
      (migrateSchedContextReplenishment st scId fromCore toCore) c' := by
  intro x hxMem tcb hTcb scId' hBind
  rw [migrateSchedContextReplenishment_runQueueOnCore] at hxMem
  have hTcbFrame : (migrateSchedContextReplenishment st scId fromCore toCore).getTcb? x
      = st.getTcb? x := by
    unfold SystemState.getTcb?; rw [migrateSchedContextReplenishment_objects]
  rw [hTcbFrame] at hTcb
  obtain ⟨sc, hsc, hbud⟩ := hCons x hxMem tcb hTcb scId' hBind
  exact ⟨sc, by rw [migrateSchedContextReplenishment_getSchedContext?]; exact hsc, hbud⟩

/-- WS-SM SM5.H.4 (D15, composite — the whole-transition obligation): the full
affinity-change composite preserves the SM4.C per-core run-queue↔budget
consistency on **every** core.  Composes the three step preservations: the
affinity write (cpuAffinity-only), the optional replenishment migration
(replenish-queues-only), and the run-queue move (§16). -/
theorem setThreadCpuAffinityWithMigration_preserves_schedContextRunQueueConsistent_perCore
    (st : SystemState) (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId)
    (executingCore c' : CoreId) (tcb : TCB)
    (st' : SystemState × Option (CoreId × SgiKind))
    (hTcb : st.getTcb? targetTid = some tcb) (hInv : st.objects.invExt)
    (hCons : ∀ c, schedContextRunQueueConsistent_perCore st c)
    (hStep : setThreadCpuAffinityWithMigration st targetTid affinity executingCore = .ok st') :
    schedContextRunQueueConsistent_perCore st'.1 c' := by
  unfold setThreadCpuAffinityWithMigration at hStep
  rw [hTcb] at hStep
  cases hSet : setThreadCpuAffinity st targetTid affinity with
  | error e => rw [hSet] at hStep; simp at hStep
  | ok stSet =>
      rw [hSet] at hStep
      simp only [Except.ok.injEq] at hStep
      have hConsSet : ∀ c, schedContextRunQueueConsistent_perCore stSet c :=
        fun c => setThreadCpuAffinity_preserves_schedContextRunQueueConsistent_perCore
          st targetTid affinity stSet c hInv (hCons c) hSet
      subst hStep
      apply migrateRunQueueOnAffinityChange_preserves_schedContextRunQueueConsistent_perCore
      intro c
      cases hb : tcb.schedContextBinding.scId? with
      | none => exact hConsSet c
      | some scId =>
          exact migrateSchedContextReplenishment_preserves_schedContextRunQueueConsistent_perCore
            stSet scId _ _ c (hConsSet c)

-- ============================================================================
-- §18  SM5.H.4 (B8/SGI) — the cross-core `.reschedule` SGI the composite emits
--      is exactly characterised: it fires iff the new home is **remote** from
--      the executing core AND the migrated thread is now **runnable** there.
--      (The whole point of the full-thread-migration composite — the run loop
--      reads this to decide whether to poke a remote core.)
-- ============================================================================

/-- WS-SM SM5.H.4 (SGI characterisation): the composite's emitted SGI is exactly
the def's `if`-expression — `none` when the new home is the executing core (local,
no cross-core poke), and otherwise a `.reschedule` SGI to the new home iff the
migrated thread is runnable there (its run-queue entry landed on the new home). -/
theorem setThreadCpuAffinityWithMigration_sgi_eq
    (st : SystemState) (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId)
    (executingCore : CoreId) (tcb : TCB) (stSet : SystemState)
    (st' : SystemState × Option (CoreId × SgiKind))
    (hTcb : st.getTcb? targetTid = some tcb)
    (hSet : setThreadCpuAffinity st targetTid affinity = .ok stSet)
    (hStep : setThreadCpuAffinityWithMigration st targetTid affinity executingCore = .ok st') :
    st'.2 =
      (if determineTargetCore stSet targetTid == executingCore then none
       else if (st'.1.scheduler.runQueueOnCore (determineTargetCore stSet targetTid)).contains targetTid then
         some (determineTargetCore stSet targetTid, SgiKind.reschedule)
       else none) := by
  unfold setThreadCpuAffinityWithMigration at hStep
  rw [hTcb, hSet] at hStep
  simp only [Except.ok.injEq] at hStep
  subst hStep
  rfl

/-- WS-SM SM5.H.4: a local affinity change (new home = executing core) emits no
cross-core SGI. -/
theorem setThreadCpuAffinityWithMigration_no_sgi_if_local
    (st : SystemState) (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId)
    (executingCore : CoreId) (tcb : TCB) (stSet : SystemState)
    (st' : SystemState × Option (CoreId × SgiKind))
    (hTcb : st.getTcb? targetTid = some tcb)
    (hSet : setThreadCpuAffinity st targetTid affinity = .ok stSet)
    (hStep : setThreadCpuAffinityWithMigration st targetTid affinity executingCore = .ok st')
    (hLocal : (determineTargetCore stSet targetTid == executingCore) = true) :
    st'.2 = none := by
  rw [setThreadCpuAffinityWithMigration_sgi_eq st targetTid affinity executingCore tcb stSet st'
        hTcb hSet hStep, if_pos hLocal]

/-- WS-SM SM5.H.4: a remote affinity change whose migrated thread is runnable on
the new home emits exactly one `.reschedule` SGI to that new home — the cross-core
poke the run loop fires after the state write is visible. -/
theorem setThreadCpuAffinityWithMigration_emits_reschedule_of_remote_runnable
    (st : SystemState) (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId)
    (executingCore : CoreId) (tcb : TCB) (stSet : SystemState)
    (st' : SystemState × Option (CoreId × SgiKind))
    (hTcb : st.getTcb? targetTid = some tcb)
    (hSet : setThreadCpuAffinity st targetTid affinity = .ok stSet)
    (hStep : setThreadCpuAffinityWithMigration st targetTid affinity executingCore = .ok st')
    (hRemote : (determineTargetCore stSet targetTid == executingCore) = false)
    (hRun : (st'.1.scheduler.runQueueOnCore (determineTargetCore stSet targetTid)).contains targetTid = true) :
    st'.2 = some (determineTargetCore stSet targetTid, SgiKind.reschedule) := by
  rw [setThreadCpuAffinityWithMigration_sgi_eq st targetTid affinity executingCore tcb stSet st'
        hTcb hSet hStep, if_neg (by simp [hRemote]), if_pos hRun]

/-- WS-SM SM5.H.4 (C10, tightened to the composite): whenever the affinity-change
composite emits an SGI `some (newHome, k)`, that SGI necessarily targets the
migrated thread's new home core, is a `.reschedule`, and — modelling the SM5.I FFI
firing in SM2.A's operational memory model — the executing core's release-store
(the state write) **happens-before** the new home's acquire-load (its SGI handler
reads the updated run queue).  This pins the generic
`affinityMigrationOrdering_happensBefore` to the composite's actual emission. -/
theorem setThreadCpuAffinityWithMigration_sgi_happensBefore
    (st : SystemState) (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId)
    (executingCore : CoreId) (tcb : TCB) (stSet : SystemState)
    (st' : SystemState × Option (CoreId × SgiKind))
    (hTcb : st.getTcb? targetTid = some tcb)
    (hSet : setThreadCpuAffinity st targetTid affinity = .ok stSet)
    (hStep : setThreadCpuAffinityWithMigration st targetTid affinity executingCore = .ok st')
    (newHome : CoreId) (k : SgiKind) (hEmit : st'.2 = some (newHome, k))
    (loc : SeLe4n.Kernel.Concurrency.AtomicLocation) (v : Nat) :
    newHome = determineTargetCore stSet targetTid ∧ k = SgiKind.reschedule ∧
    SeLe4n.Kernel.Concurrency.happensBefore
      (SeLe4n.Kernel.Concurrency.wakeOrderingTrace executingCore newHome loc v)
      (SeLe4n.Kernel.Concurrency.wakeReleaseEvent executingCore loc v)
      (SeLe4n.Kernel.Concurrency.wakeAcquireEvent newHome loc v) := by
  rw [setThreadCpuAffinityWithMigration_sgi_eq st targetTid affinity executingCore tcb stSet st'
        hTcb hSet hStep] at hEmit
  -- Reduce the emission to determine `newHome` and `k`.
  split at hEmit
  · exact absurd hEmit (by simp)
  · split at hEmit
    · simp only [Option.some.injEq, Prod.mk.injEq] at hEmit
      obtain ⟨hHome, hK⟩ := hEmit
      subst hHome; subst hK
      exact ⟨rfl, rfl, affinityMigrationOrdering_happensBefore executingCore _ loc v⟩
    · exact absurd hEmit (by simp)

end SeLe4n.Kernel
