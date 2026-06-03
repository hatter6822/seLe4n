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
open SeLe4n.Kernel.Concurrency (numCores CoreId bootCoreId)

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

/-- WS-SM SM5.H.2 (plan §3.8): schedule a CBS replenishment for SchedContext
`scId` on core `c`, eligible at absolute tick `eligibleAt`.

Inserts `(scId, eligibleAt)` into core `c`'s replenish queue
(`replenishQueueOnCore c`, sorted-by-eligibility, SM4.B per-core field), leaving
every other per-core scheduler slot, every *other* core's replenish queue, and
the object store untouched.  This is the per-core "schedule a replenishment"
primitive — the clean, reusable named extraction of the queue insert
`timerTickBudgetOnCore` / `handleYieldWithBudget` open-code as
`(replenishQueueOnCore c).insert scId (now + period)`.

The plan signature `replenishOnCore (s, c, sc)` realises `sc` as the pair
`(scId, eligibleAt)`: the replenish queue is keyed by `SchedContextId`, and the
eligibility tick (which the CBS engine computes as `now + period.val`) is made an
explicit argument so this primitive is agnostic to *how* the eligibility time was
derived (the SM5.H.6 pipeline-order theorem then requires `eligibleAt >
machine.timer`, which the CBS engine guarantees since `period.val > 0`). -/
def replenishOnCore (st : SystemState) (c : CoreId) (scId : SchedContextId)
    (eligibleAt : Nat) : SystemState :=
  let rq := (st.scheduler.replenishQueueOnCore c).insert scId eligibleAt
  { st with scheduler := st.scheduler.setReplenishQueueOnCore c rq }

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

/-- WS-SM SM5.H.4 (plan §3.8): migrate SchedContext `scId`'s pending
replenishments from core `fromCore`'s replenish queue to core `toCore`'s.

Removes every `(scId, _)` entry from `fromCore`'s queue (`ReplenishQueue.remove`)
and re-inserts each — at its **original** eligibility time — into `toCore`'s queue
(a fold of `ReplenishQueue.insert`s, which keeps each destination queue sorted).
A no-op when `fromCore = toCore` (a self-migration is the identity).  Writes only
the two replenish-queue slots; the object store, every run queue / current thread,
and every other per-core slot are untouched — so `getSchedContext?` /
`determineTargetCore` (the object-store reads the affinity-consistency invariant
depends on) are unchanged by the migration itself.

This is the operation an affinity-change syscall composes with the affinity write
(`setThreadCpuAffinityWithMigration`) so a thread's CBS budget-refill schedule
follows it to its new home core, restoring `replenishQueueAffinityConsistentOnCore`
(SM5.H.5). -/
def migrateSchedContextReplenishment (st : SystemState) (scId : SchedContextId)
    (fromCore toCore : CoreId) : SystemState :=
  if fromCore = toCore then st
  else
    let fromQ := st.scheduler.replenishQueueOnCore fromCore
    let toQ := st.scheduler.replenishQueueOnCore toCore
    let moved := fromQ.entries.filter (fun e => e.1 == scId)
    let fromQ' := fromQ.remove scId
    let toQ' := moved.foldl (fun q e => q.insert scId e.2) toQ
    let sched' := (st.scheduler.setReplenishQueueOnCore fromCore fromQ').setReplenishQueueOnCore toCore toQ'
    { st with scheduler := sched' }

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

-- §6c  The composite: affinity write + replenishment migration.

/-- WS-SM SM5.H.4 (plan §3.8): set a thread's CPU affinity **and** migrate its
bound SchedContext's pending replenishments to the new home core.

Composes the production SM5.C.8 affinity-control op (`setThreadCpuAffinity`) with
the SM5.H.4 replenishment migration: after the affinity write moves the thread's
home core from `determineTargetCore st targetTid` (old) to
`determineTargetCore stSet targetTid` (new — the just-written affinity), the bound
SchedContext's replenishments migrate from the old core's replenish queue to the
new core's, restoring `replenishQueueAffinityConsistentOnCore` (the migrated
budget-refill schedule now lives where the thread will wake).  Unbound threads
(`schedContextBinding.scId? = none`) have no SchedContext to migrate, so the op is
just the affinity write.  Fail-closed (`.invalidArgument`) on a non-TCB target.

**Authority**: like `setThreadCpuAffinity`, this primitive performs **no** in-op
capability check; the `tcbSetAffinity` syscall (SM5.I+) must verify a scheduler-
control capability before invoking it (see `setThreadCpuAffinity`'s authority
note). -/
def setThreadCpuAffinityWithMigration (st : SystemState) (targetTid : SeLe4n.ThreadId)
    (affinity : Option CoreId) : Except KernelError SystemState :=
  match st.getTcb? targetTid with
  | some tcb =>
      match setThreadCpuAffinity st targetTid affinity with
      | .ok stSet =>
          match tcb.schedContextBinding.scId? with
          | some scId => .ok (migrateSchedContextReplenishment stSet scId
              (determineTargetCore st targetTid) (determineTargetCore stSet targetTid))
          | none => .ok stSet
      | .error e => .error e
  | none => .error .invalidArgument

/-- WS-SM SM5.H.4: the composite rejects a non-TCB target (fail-closed). -/
theorem setThreadCpuAffinityWithMigration_error_of_no_tcb (st : SystemState)
    (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId)
    (hTcb : st.getTcb? targetTid = none) :
    setThreadCpuAffinityWithMigration st targetTid affinity = .error .invalidArgument := by
  simp only [setThreadCpuAffinityWithMigration, hTcb]

/-- WS-SM SM5.H.4: for a SchedContext-**bound** target, the composite is the
affinity write `stSet` followed by the replenishment migration from the old home
core to the new. -/
theorem setThreadCpuAffinityWithMigration_bound_eq (st : SystemState)
    (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId) (tcb : TCB) (scId : SchedContextId)
    (hTcb : st.getTcb? targetTid = some tcb) (hBind : tcb.schedContextBinding.scId? = some scId)
    (stSet : SystemState) (hSet : setThreadCpuAffinity st targetTid affinity = .ok stSet) :
    setThreadCpuAffinityWithMigration st targetTid affinity
      = .ok (migrateSchedContextReplenishment stSet scId
          (determineTargetCore st targetTid) (determineTargetCore stSet targetTid)) := by
  simp only [setThreadCpuAffinityWithMigration, hTcb, hSet, hBind]

/-- WS-SM SM5.H.4: for an **unbound** target (no SchedContext), the composite is
just the affinity write — there is no replenishment schedule to migrate. -/
theorem setThreadCpuAffinityWithMigration_unbound_eq (st : SystemState)
    (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId) (tcb : TCB)
    (hTcb : st.getTcb? targetTid = some tcb) (hBind : tcb.schedContextBinding.scId? = none)
    (stSet : SystemState) (hSet : setThreadCpuAffinity st targetTid affinity = .ok stSet) :
    setThreadCpuAffinityWithMigration st targetTid affinity = .ok stSet := by
  simp only [setThreadCpuAffinityWithMigration, hTcb, hSet, hBind]

/-- WS-SM SM5.H.4 (plan §6.1 `schedContextMigration_consistent`): binding
`targetTid` to a new core (`some newCore`) **and** migrating its SchedContext's
replenishments *restores* per-core CBS affinity consistency on **every** core.

Pre-state hypotheses: the target is a SchedContext-bound TCB (`hTcb`, `hBind`,
`hSc`, `hBound`); the binding is 1:1 — no other SchedContext names `targetTid` as
its bound thread (`hUnique`, supplied by `schedContextBindingConsistent`); and the
whole state is already affinity-consistent (`hCons`).  Conclusion: the composite's
output state is affinity-consistent on every core.

The migration moves `targetTid`'s SchedContext (`scId`) from its old home core
(`determineTargetCore st targetTid`) to the new one (`newCore`), where the affinity
write has made `determineTargetCore = newCore`; every other SchedContext's entries
and home core are unchanged (the 1:1 binding means only `scId` referenced
`targetTid`), so consistency is preserved everywhere else and *established* for the
migrated entries on `newCore`. -/
theorem schedContextMigration_consistent
    (st : SystemState) (targetTid : SeLe4n.ThreadId) (newCore : CoreId)
    (tcb : TCB) (scId : SchedContextId) (sc : SchedContext) (st' : SystemState)
    (hTcb : st.getTcb? targetTid = some tcb)
    (hInv : st.objects.invExt)
    (hBind : tcb.schedContextBinding.scId? = some scId)
    (hSc : st.getSchedContext? scId = some sc)
    (hBound : sc.boundThread = some targetTid)
    (hUnique : ∀ (scId'' : SchedContextId) (sc'' : SchedContext),
      st.getSchedContext? scId'' = some sc'' → sc''.boundThread = some targetTid → scId'' = scId)
    (hCons : ∀ c, replenishQueueAffinityConsistentOnCore st c)
    (hStep : setThreadCpuAffinityWithMigration st targetTid (some newCore) = .ok st') :
    replenishQueueAffinityConsistent_smp st' := by
  obtain ⟨stSet, hSet⟩ := setThreadCpuAffinity_ok_of_tcb st targetTid (some newCore) tcb hTcb
  -- stSet facts (the affinity write).
  have hSchedEq : stSet.scheduler = st.scheduler :=
    setThreadCpuAffinity_preserves_scheduler st targetTid (some newCore) stSet hSet
  have hScFrame : ∀ scId'', stSet.getSchedContext? scId'' = st.getSchedContext? scId'' :=
    fun scId'' => setThreadCpuAffinity_getSchedContext? st targetTid (some newCore) stSet tcb hTcb hInv hSet scId''
  have hTgtSelf : determineTargetCore stSet targetTid = newCore :=
    setThreadCpuAffinity_affects_determineTargetCore st targetTid newCore stSet tcb hTcb hInv hSet
  have hTgtNe : ∀ other, other ≠ targetTid → determineTargetCore stSet other = determineTargetCore st other :=
    fun other hNe => setThreadCpuAffinity_determineTargetCore_ne st targetTid (some newCore) other stSet hInv hNe hSet
  -- st' is the migration of stSet from the old home core to newCore.
  have hSt'Eq : st' = migrateSchedContextReplenishment stSet scId (determineTargetCore st targetTid) newCore := by
    have hb := setThreadCpuAffinityWithMigration_bound_eq st targetTid (some newCore) tcb scId hTcb hBind stSet hSet
    rw [hStep, hTgtSelf] at hb
    exact Except.ok.inj hb
  subst hSt'Eq
  -- scId's replenishments live only on `targetTid`'s old home core (by pre-state consistency).
  have hOldEntries : ∀ (c : CoreId) (t : Nat),
      (scId, t) ∈ (st.scheduler.replenishQueueOnCore c).entries →
      c = determineTargetCore st targetTid := by
    intro c t hMem
    exact (hCons c scId t hMem sc hSc targetTid hBound).symm
  -- The home-core bridge: for any consistent st-entry whose SchedContext ≠ scId,
  -- the affinity write leaves the bound thread's home core unchanged.
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
  -- stSet is consistent on every core OTHER than `targetTid`'s old home core
  -- (those cores never held `scId`'s entries, so nothing moved out from under them).
  have hStSetOff : ∀ c, c ≠ determineTargetCore st targetTid →
      replenishQueueAffinityConsistentOnCore stSet c := by
    intro c hcNeOld scId₀ t hMem sc₀ hSc₀ tid₀ hBound₀
    rw [hSchedEq] at hMem
    rw [hScFrame scId₀] at hSc₀
    have hNeScId : scId₀ ≠ scId := fun hEq => hcNeOld (hOldEntries c t (hEq ▸ hMem))
    exact bridge c scId₀ t sc₀ tid₀ hMem hSc₀ hBound₀ hNeScId
  intro c
  by_cases hON : determineTargetCore st targetTid = newCore
  · -- Old home = new home: the migration is a no-op, and the affinity write left
    -- every thread's home core unchanged ⇒ stSet is fully consistent.
    rw [hON, migrateSchedContextReplenishment_noop]
    intro scId₀ t hMem sc₀ hSc₀ tid₀ hBound₀
    rw [hSchedEq] at hMem
    rw [hScFrame scId₀] at hSc₀
    by_cases hTid : tid₀ = targetTid
    · subst hTid
      have hScEq : scId₀ = scId := hUnique scId₀ sc₀ hSc₀ hBound₀
      subst hScEq
      rw [hTgtSelf, ← hON]
      exact (hOldEntries c t hMem).symm
    · rw [hTgtNe tid₀ hTid]
      exact hCons c scId₀ t hMem sc₀ hSc₀ tid₀ hBound₀
  · -- Old home ≠ new home: apply the migration-level establish/preserve lemmas.
    by_cases hcNew : c = newCore
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
          stSet scId (determineTargetCore st targetTid) newCore (fun hEq => hON hEq) ?_
        intro scId₀ t hMem hNeScId sc₀ hSc₀ tid₀ hBound₀
        rw [hSchedEq] at hMem
        rw [hScFrame scId₀] at hSc₀
        exact bridge (determineTargetCore st targetTid) scId₀ t sc₀ tid₀ hMem hSc₀ hBound₀ hNeScId
      · exact migrateSchedContextReplenishment_preserves_affinityConsistentOnCore_other
          stSet scId (determineTargetCore st targetTid) newCore c
          (fun hEq => hcOld hEq.symm) (fun hEq => hcNew hEq.symm) (hStSetOff c hcOld)

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

end SeLe4n.Kernel
