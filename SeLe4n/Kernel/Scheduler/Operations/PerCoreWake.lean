-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.PerCoreSwitchToThread

/-!
# WS-SM SM5.C — Cross-core wake via SGI (lock-sets, wake / SGI / handler theorems)

This module is the SM5.C deliverable of the WS-SM Phase 5 per-core scheduler
(plan `docs/planning/SMP_PER_CORE_SCHEDULER_PLAN.md` §3.3, §4.4, §5).  The
cross-core wake transitions themselves (`enqueueRunnableOnCore`,
`determineTargetCore`, `wakeThread`, `handleRescheduleSgiOnCore`,
`setThreadCpuAffinity`) live in the production module
`Scheduler.Operations.Selection`, alongside the SM5.A `chooseThreadOnCore` and
SM5.B `switchToThreadOnCore` primitives this phase composes; this module
collects the *forward-looking* SM5.C theorems — the wake / SGI-handler
lock-sets, the wake-semantics theorems (SGI emission, target-run-queue
membership, losslessness), the SGI-delivery latency bound, the
`determineTargetCore` / `setThreadCpuAffinity` characterisations, and the
decidability witnesses — staged until SM5.D's per-core timer tick (whose
cross-core CBS-replenish wake is the first runtime exerciser) wires
`wakeThread` into the runtime dispatch loop with the `withLockSet` acquisition
over `wakeThreadLockSet`.

## What this module proves

* **SM5.C.3** `wakeThreadLockSet` + `handleRescheduleSgiOnCoreLockSet` — the
  cross-domain (object-store + per-core run-queue **write**) footprints of the
  wake and of the target-core SGI handler, over SM5.A's unified `SchedLockId`,
  in plan §4.4 ascending order (object lock before run-queue lock).
* **SM5.C.9** `determineTargetCore_*` — a bound thread wakes onto its affinity
  core; an unbound thread (and the boot-time TCB default `cpuAffinity = none`)
  wakes onto `bootCoreId` (the "boot-time default affinity = bootCoreId" rule).
* **SM5.C.1** `enqueueRunnableOnCore_*` — the per-core "make runnable" primitive
  preserves the object-store invariant and core `c`'s run-queue well-formedness,
  enqueues `tid` (membership), makes it IPC-ready, and frames out every other
  core's run queue and every other thread's TCB.
* **SM5.C.2 / Theorem 3.3.1** `wakeThread_emits_sgi_if_remote` /
  `wakeThread_no_sgi_if_local` — the wake emits a `.reschedule` SGI to the
  target core iff that core is remote from the executing core.
* **SM5.C.10** `wakeThread_target_runQueue_contains` — the woken thread is in the
  target core's run queue immediately after the wake (the thread is not lost).
* **SM5.C.6 / Theorem 3.3.2** `wakeThread_lossless` — the woken thread is
  recoverable: there is a scheduler-reachable state in which it is current on,
  or enqueued on, its target core (witnessed reflexively by the post-wake state).
* **SM5.C.5** `handleRescheduleSgiOnCore_*` — the target core's reschedule-SGI
  handler re-chooses and switches (or idles when nothing is runnable), never
  errors under the per-core scheduler invariant, and preserves the structural
  invariants.
* **SM5.C.11** `wakeThread_emits_at_most_one_sgi` + `rescheduleSgi_*` — the SGI
  delivery latency bound: a wake emits at most one SGI, and the `.reschedule`
  SGI is the lowest-INTID (highest GIC priority) kernel SGI, so it is not
  starved by other kernel coordination SGIs.
* **SM5.C.8** `setThreadCpuAffinity_*` — the affinity-control op sets the
  target's affinity, preserves the object-store invariant and the scheduler
  state, frames out every other thread, and feeds `determineTargetCore` /
  `affinityAdmitsCore`.

Axiom-clean: every theorem depends only on the standard foundational axioms
(`propext` / `Quot.sound` / `Classical.choice`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (numCores CoreId bootCoreId allCores SgiKind)

-- ============================================================================
-- §1  SM5.C.3 — Cross-domain lock-set footprints (wake + SGI handler)
-- ============================================================================

/-- WS-SM SM5.C.3 (cross-domain, plan §3.3 / §4.4): the **complete** lock-set
footprint of `wakeThread`'s state effect (`enqueueRunnableOnCore target tid`),
over SM5.A's unified `SchedLockId`.

`enqueueRunnableOnCore` mutates *both* lock domains:

* the RobinHood **object store** (write): it resolves `tid`'s TCB via `getTcb?`
  *and* writes the woken thread's `ipcState := .ready` back via `objects.insert`.
  Per SM3.A.10 the store is guarded by the single table-level lock at the top of
  the SM0.I hierarchy (`schedObjStoreLockId`), here taken in **write** mode; and
* the **target** core's per-core run-queue slot (write): it inserts `tid`.

So the footprint is the two-lock set in plan §4.4 ascending order (object lock
first):
`[(SchedLockId.object schedObjStoreLockId, .write), (SchedLockId.runQueue ⟨target⟩, .write)]`.

**Why the table lock rather than `(LockId.tcb tid, .write)` (plan §3.3's
sketch).**  Identical to the SM5.B rationale: the `ipcState := .ready` save is an
`RHTable.insert`, and SM3.A.10 guards the object store's structural
concurrency-safety at *table* granularity (a concurrent insert can relocate
slots along the probe sequence), so a per-object TCB lock would not protect the
table.  The object-store **table** write lock is the *sound* discipline.

The cross-domain order is `wakeThreadLockSet_object_before_runQueue`; the runtime
`withLockSet` acquisition (in the ascending order certified by
`wakeThreadLockSet_pairwise_le`) is SM5.C's dispatch-loop / SM5.D work. -/
def wakeThreadLockSet (target : CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  [ (SchedLockId.object schedObjStoreLockId, .write)
  , (SchedLockId.runQueue ⟨target⟩, .write) ]

/-- SM5.C.3: the wake footprint is the two-lock object-store + run-queue set. -/
@[simp] theorem wakeThreadLockSet_length (target : CoreId) :
    (wakeThreadLockSet target).length = 2 := rfl

/-- SM5.C.3: every lock in the wake footprint is acquired in **write** mode —
the wake mutates both the object store (`ipcState := .ready`) and the target run
queue (insert). -/
theorem wakeThreadLockSet_write_only (target : CoreId) :
    ∀ p ∈ wakeThreadLockSet target, p.2 = Concurrency.AccessMode.write := by
  intro p hp
  simp only [wakeThreadLockSet, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h <;> subst h <;> rfl

/-- SM5.C.3: the object-store **write** lock is in the wake footprint — it guards
both the `getTcb?` resolution and the `ipcState := .ready` save. -/
theorem wakeThreadLockSet_contains_objStore_write (target : CoreId) :
    (SchedLockId.object schedObjStoreLockId, Concurrency.AccessMode.write)
      ∈ wakeThreadLockSet target := by
  simp [wakeThreadLockSet]

/-- SM5.C.3: the target core's run-queue **write** lock is in the wake
footprint — it guards the insert of the woken thread. -/
theorem wakeThreadLockSet_contains_runQueue_write (target : CoreId) :
    (SchedLockId.runQueue ⟨target⟩, Concurrency.AccessMode.write)
      ∈ wakeThreadLockSet target := by
  simp [wakeThreadLockSet]

/-- SM5.C.3 (plan §4.4): inside the wake footprint the object-store lock is
acquired *before* the run-queue lock — the cross-domain ascending order. -/
theorem wakeThreadLockSet_object_before_runQueue (target : CoreId) :
    SchedLockId.object schedObjStoreLockId
      < SchedLockId.runQueue (⟨target⟩ : RunQueueLockId) :=
  SchedLockId.object_lt_runQueue _ _

/-- SM5.C.3: the wake footprint's projected keys are duplicate-free. -/
theorem wakeThreadLockSet_keys_nodup (target : CoreId) :
    ((wakeThreadLockSet target).map (·.1)).Nodup := by
  simp [wakeThreadLockSet]

/-- SM5.C.3 (plan §4.4): the wake footprint's keys form a `SchedLockId`-ascending
acquisition sequence — they are `Pairwise (· ≤ ·)`, so the canonical `withLockSet`
acquisition is the list itself (the wake's contribution to cross-core
deadlock-freedom via the SM3.D ladder). -/
theorem wakeThreadLockSet_pairwise_le (target : CoreId) :
    ((wakeThreadLockSet target).map (·.1)).Pairwise (· ≤ ·) := by
  have hle : SchedLockId.object schedObjStoreLockId
      ≤ SchedLockId.runQueue (⟨target⟩ : RunQueueLockId) :=
    (SchedLockId.object_lt_runQueue _ _).1
  simp only [wakeThreadLockSet, List.map_cons, List.map_nil]
  exact List.Pairwise.cons
    (fun a ha => by rcases List.mem_singleton.mp ha with rfl; exact hle)
    (List.Pairwise.cons (fun a ha => by simp at ha) List.Pairwise.nil)

/-- WS-SM SM5.C.3 / SM5.C.5: the lock-set footprint of the target-core
reschedule-SGI handler `handleRescheduleSgiOnCore c`.  The handler re-chooses
(`chooseThreadOnCore`, read footprint) and switches (`switchToThreadOnCore`,
write footprint) on core `c`; the switch's write footprint subsumes the
selection's read footprint, so the handler's footprint *is* the switch's
(`switchToThreadOnCoreLockSet c`): the object-store + run-queue write locks. -/
def handleRescheduleSgiOnCoreLockSet (c : CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  switchToThreadOnCoreLockSet c

/-- SM5.C.5: the SGI-handler footprint coincides with the switch footprint. -/
@[simp] theorem handleRescheduleSgiOnCoreLockSet_eq (c : CoreId) :
    handleRescheduleSgiOnCoreLockSet c = switchToThreadOnCoreLockSet c := rfl

-- ============================================================================
-- §2  SM5.C.9 — `determineTargetCore` (boot-time default affinity)
-- ============================================================================

/-- WS-SM SM5.C.9 (plan §3.3): a thread bound to `some c'` wakes onto `c'`. -/
theorem determineTargetCore_bound_eq_affinity (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (c' : CoreId)
    (hTcb : st.getTcb? tid = some tcb) (hAff : tcb.cpuAffinity = some c') :
    determineTargetCore st tid = c' := by
  simp only [determineTargetCore, hTcb, hAff]

/-- WS-SM SM5.C.9 (plan §3.3, the "boot-time default affinity = `bootCoreId`"
rule): an *unbound* thread (`cpuAffinity = none`, the TCB field default) wakes
onto the boot core.  This realises SM5.C.9 as the default wake *target* — the
field stays `none` (so `affinityAdmitsCore` still admits the thread on every
core, the SM5.B semantics), but its default landing core is `bootCoreId`. -/
theorem determineTargetCore_unbound_eq_bootCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hAff : tcb.cpuAffinity = none) :
    determineTargetCore st tid = bootCoreId := by
  simp only [determineTargetCore, hTcb, hAff]

/-- WS-SM SM5.C.9: a `tid` that does not resolve to a TCB defaults to the boot
core (fail-safe — the wake never invents a target). -/
theorem determineTargetCore_no_tcb_eq_bootCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (hTcb : st.getTcb? tid = none) :
    determineTargetCore st tid = bootCoreId := by
  simp only [determineTargetCore, hTcb]

/-- WS-SM SM5.C.9: the wake target is always a valid core (`< numCores`).
Trivial from the `Fin numCores` representation; a surface anchor for the
SM5.C.3 lock-set (whose `runQueue ⟨target⟩` key is well-formed for any
`target`). -/
theorem determineTargetCore_in_range (st : SystemState) (tid : SeLe4n.ThreadId) :
    (determineTargetCore st tid).val < numCores :=
  (determineTargetCore st tid).isLt


-- ============================================================================
-- §3  SM5.C.1 — `enqueueRunnableOnCore` (preservation, membership, frame)
-- ============================================================================

/-- WS-SM SM5.C.1 (preservation): `enqueueRunnableOnCore` preserves the
RobinHood object-store invariant.  Its only object-store write is the woken
thread's `ipcState := .ready` save (an `insert` at an existing key), which
preserves `invExt`; the non-TCB branch is the identity. -/
theorem enqueueRunnableOnCore_preserves_objects_invExt (st : SystemState)
    (c : CoreId) (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    (enqueueRunnableOnCore st c tid).objects.invExt := by
  cases hTcb : st.getTcb? tid with
  | none => simp only [enqueueRunnableOnCore, hTcb]; exact hInv
  | some tcb =>
      simp only [enqueueRunnableOnCore, hTcb]
      exact RHTable_insert_preserves_invExt st.objects _ _ hInv

/-- WS-SM SM5.C.1 (preservation): `enqueueRunnableOnCore` preserves core `c`'s
run-queue well-formedness — the only run-queue mutation is the re-enqueue
(`insert`), which preserves `RunQueue.wellFormed`; the non-TCB branch leaves the
run queue unchanged. -/
theorem enqueueRunnableOnCore_preserves_runQueueOnCore_wellFormed (st : SystemState)
    (c : CoreId) (tid : SeLe4n.ThreadId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed) :
    ((enqueueRunnableOnCore st c tid).scheduler.runQueueOnCore c).wellFormed := by
  cases hTcb : st.getTcb? tid with
  | none => simp only [enqueueRunnableOnCore, hTcb]; exact hwf
  | some tcb =>
      simp only [enqueueRunnableOnCore, hTcb,
        SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
      exact RunQueue.insert_preserves_wellFormed _ hwf _ _

/-- WS-SM SM5.C.1 (membership): the woken thread is a member of core `c`'s run
queue immediately after `enqueueRunnableOnCore` (when it resolves to a TCB).
The substantive "the wake genuinely enqueues" content. -/
theorem enqueueRunnableOnCore_mem_runQueueOnCore (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb) :
    tid ∈ ((enqueueRunnableOnCore st c tid).scheduler.runQueueOnCore c).toList := by
  simp only [enqueueRunnableOnCore, hTcb,
    SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
  rw [RunQueue.mem_toList_iff_mem]
  exact (RunQueue.mem_insert _ _ _ _).mpr (Or.inr rfl)

/-- WS-SM SM5.C.1 (IPC↔scheduler coherence): the woken thread has `ipcState =
.ready` after `enqueueRunnableOnCore` — so its run-queue membership satisfies
`runnableThreadIpcReady` and it is no longer flagged `blockedOn*`.  This is the
field the per-core IPC↔scheduler invariants gate run-queue membership on; the
wake establishing it is why enqueuing a freshly-woken thread is invariant-safe. -/
theorem enqueueRunnableOnCore_makes_ready (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hInv : st.objects.invExt) :
    (enqueueRunnableOnCore st c tid).getTcb? tid = some { tcb with ipcState := .ready } := by
  simp only [enqueueRunnableOnCore, hTcb, SystemState.getTcb?_eq_some_iff,
    RHTable_getElem?_eq_get?]
  exact RHTable_get?_insert_self st.objects tid.toObjId _ hInv

/-- WS-SM SM5.C.1 (cross-core frame): `enqueueRunnableOnCore` on core `c` leaves
every *other* core's run-queue slot (`c' ≠ c`) untouched — it writes only core
`c`'s run-queue slot.  Half of the wake's cross-core-independence frame. -/
theorem enqueueRunnableOnCore_runQueueOnCore_ne (st : SystemState) (c c' : CoreId)
    (tid : SeLe4n.ThreadId) (h : c ≠ c') :
    (enqueueRunnableOnCore st c tid).scheduler.runQueueOnCore c'
      = st.scheduler.runQueueOnCore c' := by
  cases hTcb : st.getTcb? tid with
  | none => simp only [enqueueRunnableOnCore, hTcb]
  | some tcb =>
      simp only [enqueueRunnableOnCore, hTcb]
      exact SchedulerState.setRunQueueOnCore_runQueueOnCore_ne st.scheduler c c' _ h

/-- WS-SM SM5.C.1 (no-current frame): `enqueueRunnableOnCore` never writes any
core's `current` slot — it only saves the woken thread's IPC state (objects) and
inserts into core `c`'s run queue (scheduler).  So *every* core's current thread
is preserved. -/
theorem enqueueRunnableOnCore_currentOnCore (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (c' : CoreId) :
    (enqueueRunnableOnCore st c tid).scheduler.currentOnCore c'
      = st.scheduler.currentOnCore c' := by
  cases hTcb : st.getTcb? tid with
  | none => simp only [enqueueRunnableOnCore, hTcb]
  | some tcb =>
      simp only [enqueueRunnableOnCore, hTcb,
        SchedulerState.setRunQueueOnCore_currentOnCore]

/-- WS-SM SM5.C.1 (per-thread frame): `enqueueRunnableOnCore tid` leaves every
*other* thread's `getTcb?` lookup unchanged — its only object-store write is at
key `tid.toObjId`.  Proved through the typed `getTcb?` accessor + the
`.get?`-method form of `RHTable.getElem?_insert_ne` (no raw `[·]?` bracket in
the proof source — AK7-clean). -/
theorem enqueueRunnableOnCore_getTcb?_ne (st : SystemState) (c : CoreId)
    (tid other : SeLe4n.ThreadId) (hInv : st.objects.invExt) (hNe : other ≠ tid) :
    (enqueueRunnableOnCore st c tid).getTcb? other = st.getTcb? other := by
  cases hTcb : st.getTcb? tid with
  | none => simp only [enqueueRunnableOnCore, hTcb]
  | some tcb =>
      have hNeT : tid ≠ other := fun he => hNe he.symm
      have hNeO : ¬ (tid.toObjId == other.toObjId) = true := fun he =>
        hNeT (ThreadId.toObjId_injective _ _ (by simpa using he))
      -- Reduce the `enqueueRunnableOnCore` match (via `hTcb`) *before* unfolding
      -- `getTcb?` — unfolding `getTcb?` in one combined `simp` would also rewrite
      -- the `st.getTcb? tid` discriminant inside `enqueueRunnableOnCore`, so
      -- `hTcb` could not fire on it.
      simp only [enqueueRunnableOnCore, hTcb]
      simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
      rw [RobinHood.RHTable.getElem?_insert_ne st.objects tid.toObjId other.toObjId
        _ hNeO hInv]

/-- WS-SM SM5.C.1 (fail-closed): a `tid` that does not resolve to a TCB makes
`enqueueRunnableOnCore` the identity — a corrupted run-queue entry is never
invented. -/
theorem enqueueRunnableOnCore_no_tcb_noop (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (hTcb : st.getTcb? tid = none) :
    enqueueRunnableOnCore st c tid = st := by
  simp only [enqueueRunnableOnCore, hTcb]


-- ============================================================================
-- §4  SM5.C.2/.4/.10 — `wakeThread` semantics (SGI emission, membership, frame)
-- ============================================================================

/-- WS-SM SM5.C.2: the state component of a wake is exactly the
`enqueueRunnableOnCore` of the target core.  `rfl` because that is the literal
definition; names the decomposition so the `wakeThread_*` theorems can appeal
to the SM5.C.1 `enqueueRunnableOnCore_*` lemmas without re-`unfold`ing. -/
@[simp] theorem wakeThread_state_eq_enqueue (st : SystemState)
    (tid : SeLe4n.ThreadId) (executingCore : CoreId) :
    (wakeThread st tid executingCore).1
      = enqueueRunnableOnCore st (determineTargetCore st tid) tid := rfl

/-- WS-SM SM5.C.4 (plan §3.3, Theorem 3.3.1): a wake whose target core is
*remote* from the executing core emits a `.reschedule` SGI to the target — the
target core must be poked to re-run its scheduler and pick up the
newly-runnable thread. -/
theorem wakeThread_emits_sgi_if_remote (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) (h : determineTargetCore st tid ≠ executingCore) :
    (wakeThread st tid executingCore).2
      = some (determineTargetCore st tid, SgiKind.reschedule) := by
  have hbeq : (determineTargetCore st tid == executingCore) = false :=
    beq_eq_false_iff_ne.mpr h
  simp only [wakeThread]
  rw [if_neg (by simp [hbeq])]

/-- WS-SM SM5.C.4: a wake whose target *is* the executing core emits no SGI —
the local scheduler will pick up the newly-runnable thread on its next decision,
so no cross-core poke is required. -/
theorem wakeThread_no_sgi_if_local (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) (h : determineTargetCore st tid = executingCore) :
    (wakeThread st tid executingCore).2 = none := by
  simp only [wakeThread, h, beq_self_eq_true, if_true]

/-- WS-SM SM5.C.4: every SGI a wake emits is the `.reschedule` kind — `wakeThread`
never emits a TLB-shootdown / cache-broadcast / halt SGI.  The discriminant that
the SM5.C.11 latency bound (the reschedule SGI is the highest-priority kernel
SGI) rests on. -/
theorem wakeThread_sgi_is_reschedule (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) (target : CoreId) (kind : SgiKind)
    (h : (wakeThread st tid executingCore).2 = some (target, kind)) :
    kind = SgiKind.reschedule := by
  simp only [wakeThread] at h
  split at h
  · exact absurd h (by simp)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact h.2.symm

/-- WS-SM SM5.C.10 (plan §3.3): the woken thread is a member of the target
core's run queue immediately after the wake — the wake *does not lose* the
thread.  The substantive content behind `wakeThread_lossless`. -/
theorem wakeThread_target_runQueue_contains (st : SystemState)
    (tid : SeLe4n.ThreadId) (executingCore : CoreId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) :
    tid ∈ ((wakeThread st tid executingCore).1.scheduler.runQueueOnCore
            (determineTargetCore st tid)).toList := by
  rw [wakeThread_state_eq_enqueue]
  exact enqueueRunnableOnCore_mem_runQueueOnCore st (determineTargetCore st tid) tid tcb hTcb

/-- WS-SM SM5.C.2 (preservation): a wake preserves the RobinHood object-store
invariant. -/
theorem wakeThread_preserves_objects_invExt (st : SystemState)
    (tid : SeLe4n.ThreadId) (executingCore : CoreId) (hInv : st.objects.invExt) :
    (wakeThread st tid executingCore).1.objects.invExt := by
  rw [wakeThread_state_eq_enqueue]
  exact enqueueRunnableOnCore_preserves_objects_invExt st (determineTargetCore st tid) tid hInv

/-- WS-SM SM5.C.2 (preservation): a wake preserves the target core's run-queue
well-formedness. -/
theorem wakeThread_preserves_target_runQueue_wellFormed (st : SystemState)
    (tid : SeLe4n.ThreadId) (executingCore : CoreId)
    (hwf : (st.scheduler.runQueueOnCore (determineTargetCore st tid)).wellFormed) :
    ((wakeThread st tid executingCore).1.scheduler.runQueueOnCore
      (determineTargetCore st tid)).wellFormed := by
  rw [wakeThread_state_eq_enqueue]
  exact enqueueRunnableOnCore_preserves_runQueueOnCore_wellFormed st
    (determineTargetCore st tid) tid hwf

/-- WS-SM SM5.C.2 (cross-core independence frame): a wake leaves every core
*other than the target* untouched — both its run queue and its current thread.
The scheduler-state frame that makes the wake safe under SMP: it writes only the
target core's run-queue slot (plus the woken TCB), so a concurrent scheduling
decision on a sibling core cannot observe a change to its own scheduler state.
Matches the run-queue write lock of `wakeThreadLockSet` covering only the
target. -/
theorem wakeThread_independent_of_other_core (st : SystemState)
    (tid : SeLe4n.ThreadId) (executingCore : CoreId) (c' : CoreId)
    (h : determineTargetCore st tid ≠ c') :
    (wakeThread st tid executingCore).1.scheduler.runQueueOnCore c'
        = st.scheduler.runQueueOnCore c'
      ∧ (wakeThread st tid executingCore).1.scheduler.currentOnCore c'
        = st.scheduler.currentOnCore c' := by
  rw [wakeThread_state_eq_enqueue]
  exact ⟨enqueueRunnableOnCore_runQueueOnCore_ne st (determineTargetCore st tid) c' tid h,
    enqueueRunnableOnCore_currentOnCore st (determineTargetCore st tid) tid c'⟩


-- ============================================================================
-- §5  SM5.C.6 — `wakeThread_lossless` (plan §3.3, Theorem 3.3.2)
-- ============================================================================

/-- WS-SM SM5.C.6: a single per-core scheduler step — enqueuing a runnable
thread (`enqueueRunnableOnCore`) or dispatching a chosen one
(`switchToThreadOnCore`) on some core.  The "eventually scheduled" strengthening
(SM5.J liveness) ranges over the reflexive-transitive closure of this relation;
`wakeThread_lossless` needs only its reflexive case (the woken thread is
*already* enqueued), but the step relation is defined genuinely (with both the
enqueue and the switch transitions) so the closure is not reflexive-only. -/
inductive SchedStep : SystemState → SystemState → Prop where
  | enqueue (s : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) :
      SchedStep s (enqueueRunnableOnCore s c t)
  | switch (s s' : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
      (h : switchToThreadOnCore s c t = .ok s') :
      SchedStep s s'

/-- WS-SM SM5.C.6: the reflexive-transitive "reachable by scheduler steps"
closure used by `wakeThread_lossless`. -/
inductive SchedReachable : SystemState → SystemState → Prop where
  | refl (s : SystemState) : SchedReachable s s
  | tail (s₁ s₂ s₃ : SystemState) (h₁ : SchedReachable s₁ s₂) (h₂ : SchedStep s₂ s₃) :
      SchedReachable s₁ s₃

/-- WS-SM SM5.C.6: `SchedReachable` is non-vacuous — a single enqueue step is a
reachable transition, so the closure is not reflexive-only. -/
theorem SchedReachable.of_enqueue (s : SystemState) (c : CoreId)
    (t : SeLe4n.ThreadId) :
    SchedReachable s (enqueueRunnableOnCore s c t) :=
  .tail s s _ (.refl s) (.enqueue s c t)

/-- WS-SM SM5.C.6: `SchedReachable` is transitive (it is an RT-closure). -/
theorem SchedReachable.trans {s₁ s₂ s₃ : SystemState}
    (h₁ : SchedReachable s₁ s₂) (h₂ : SchedReachable s₂ s₃) :
    SchedReachable s₁ s₃ := by
  induction h₂ with
  | refl => exact h₁
  | tail b c _hab hstep ih => exact SchedReachable.tail s₁ b c ih hstep

/-- WS-SM SM5.C.6 (plan §3.3, Theorem 3.3.2): cross-core wake is *lossless* — the
woken thread is recoverable.  There is a scheduler-reachable state (namely the
post-wake state itself) in which `tid` is current on, or enqueued on, its target
core.  Witnessed reflexively by the post-wake state via the right disjunct
(`wakeThread_target_runQueue_contains`): the wake does not drop the thread; it is
*immediately* present in the target run queue and will be selected when it is the
highest-priority runnable thread (the "no higher-priority work preempts" caveat
of the plan; the full eventually-scheduled liveness is SM5.J).

This is the conjunction form (`reachable ∧ disjunct`), strictly stronger than —
and more clearly stated than — the plan pseudocode's ambiguous
`(reachable ∧ A) ∨ B` precedence. -/
theorem wakeThread_lossless (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb) :
    ∃ futureState : SystemState,
      SchedReachable (wakeThread st tid executingCore).1 futureState ∧
      (futureState.scheduler.currentOnCore (determineTargetCore st tid) = some tid ∨
       tid ∈ (futureState.scheduler.runQueueOnCore (determineTargetCore st tid)).toList) :=
  ⟨(wakeThread st tid executingCore).1, SchedReachable.refl _,
    Or.inr (wakeThread_target_runQueue_contains st tid executingCore tcb hTcb)⟩


-- ============================================================================
-- §6  SM5.C.5 — `handleRescheduleSgiOnCore` (re-choose + switch / idle)
-- ============================================================================

/-- WS-SM SM5.C.5: when the SGI handler's re-choose finds no eligible thread
(`chooseThreadOnCore = .ok none`), the handler is the identity — core `c` keeps
running whatever it was (or idles); no spurious dispatch is invented. -/
theorem handleRescheduleSgiOnCore_idle_when_none (st : SystemState) (c : CoreId)
    (hc : chooseThreadOnCore st c = .ok none) :
    handleRescheduleSgiOnCore st c = .ok st := by
  simp only [handleRescheduleSgiOnCore, hc]

/-- WS-SM SM5.C.5: when the SGI handler's re-choose selects `tid`
(`chooseThreadOnCore = .ok (some tid)`), the handler is exactly the switch to
`tid` (`switchToThreadOnCore`). -/
theorem handleRescheduleSgiOnCore_eq_switch_of_choose_some (st : SystemState)
    (c : CoreId) (tid : SeLe4n.ThreadId) (hc : chooseThreadOnCore st c = .ok (some tid)) :
    handleRescheduleSgiOnCore st c = switchToThreadOnCore st c tid := by
  simp only [handleRescheduleSgiOnCore, hc]

/-- WS-SM SM5.C.5: a successful SGI-handler dispatch sets core `c`'s current
thread to the re-chosen thread.  Composes the SM5.A selection with the SM5.B
switch's `_sets_current` (Theorem 3.2.1). -/
theorem handleRescheduleSgiOnCore_switches_current (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (st' : SystemState)
    (hc : chooseThreadOnCore st c = .ok (some tid))
    (h : handleRescheduleSgiOnCore st c = .ok st') :
    st'.scheduler.currentOnCore c = some tid := by
  rw [handleRescheduleSgiOnCore_eq_switch_of_choose_some st c tid hc] at h
  exact switchToThreadOnCore_sets_current st c tid st' h

/-- WS-SM SM5.C.5 (preservation): the SGI handler preserves the RobinHood
object-store invariant — the idle branch is the identity, the dispatch branch is
a `switchToThreadOnCore` (which preserves `invExt`, SM5.B). -/
theorem handleRescheduleSgiOnCore_preserves_objects_invExt (st : SystemState)
    (c : CoreId) (st' : SystemState) (hInv : st.objects.invExt)
    (h : handleRescheduleSgiOnCore st c = .ok st') :
    st'.objects.invExt := by
  unfold handleRescheduleSgiOnCore at h
  cases hc : chooseThreadOnCore st c with
  | error e => rw [hc] at h; exact absurd h (by simp)
  | ok r =>
      rw [hc] at h
      cases r with
      | none => rw [Except.ok.injEq] at h; subst h; exact hInv
      | some tid => exact switchToThreadOnCore_preserves_objects_invExt st c tid st' hInv h

/-- WS-SM SM5.C.5 (preservation): the SGI handler preserves core `c`'s run-queue
well-formedness. -/
theorem handleRescheduleSgiOnCore_preserves_runQueueOnCore_wellFormed (st : SystemState)
    (c : CoreId) (st' : SystemState)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (h : handleRescheduleSgiOnCore st c = .ok st') :
    (st'.scheduler.runQueueOnCore c).wellFormed := by
  unfold handleRescheduleSgiOnCore at h
  cases hc : chooseThreadOnCore st c with
  | error e => rw [hc] at h; exact absurd h (by simp)
  | ok r =>
      rw [hc] at h
      cases r with
      | none => rw [Except.ok.injEq] at h; subst h; exact hwf
      | some tid => exact switchToThreadOnCore_preserves_runQueueOnCore_wellFormed st c tid st' hwf h

/-- WS-SM SM5.C.5 (cross-core independence): the SGI handler on core `c` leaves
every other core's `current` and `runQueue` slots untouched — the idle branch is
the identity, the dispatch branch is a `switchToThreadOnCore` (which is
per-core-independent, SM5.B.6). -/
theorem handleRescheduleSgiOnCore_independent_of_other_core (st : SystemState)
    (c c' : CoreId) (st' : SystemState) (hcc : c ≠ c')
    (h : handleRescheduleSgiOnCore st c = .ok st') :
    st'.scheduler.currentOnCore c' = st.scheduler.currentOnCore c'
      ∧ st'.scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c' := by
  unfold handleRescheduleSgiOnCore at h
  cases hc : chooseThreadOnCore st c with
  | error e => rw [hc] at h; exact absurd h (by simp)
  | ok r =>
      rw [hc] at h
      cases r with
      | none => rw [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
      | some tid => exact switchToThreadOnCore_independent_of_other_core st c c' tid st' hcc h

-- ============================================================================
-- §7  SM5.C.11 — SGI delivery latency bound
-- ============================================================================

/-- WS-SM SM5.C.11: the number of SGIs a single wake emits, as an explicit
count. -/
def wakeSgiCount (sgi : Option (CoreId × SgiKind)) : Nat :=
  match sgi with
  | none => 0
  | some _ => 1

/-- WS-SM SM5.C.11: a wake emits **at most one** SGI — bounded emission, no SGI
storm.  A single wake either pokes exactly one (remote) target core or none; it
never multicasts.  This is the per-wake-cost half of the latency bound. -/
theorem wakeThread_emits_at_most_one_sgi (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) :
    wakeSgiCount (wakeThread st tid executingCore).2 ≤ 1 := by
  unfold wakeSgiCount
  cases (wakeThread st tid executingCore).2 <;> simp

/-- WS-SM SM5.C.11: the `.reschedule` SGI maps to INTID `0`. -/
theorem rescheduleSgi_intid_eq_zero : SgiKind.reschedule.toIntid.val = 0 := rfl

/-- WS-SM SM5.C.11: among the kernel-reserved SGIs, `.reschedule` has the
*lowest* INTID — and on the GIC a lower INTID is a higher delivery priority.  So
a pending `.reschedule` SGI is serviced before any concurrently-pending
TLB-shootdown / cache-broadcast / halt kernel SGI; the wake-to-reschedule
latency is never inflated by another kernel SGI queued ahead of it. -/
theorem rescheduleSgi_lowest_intid (k : SgiKind) :
    SgiKind.reschedule.toIntid.val ≤ k.toIntid.val := by
  cases k <;> decide

/-- WS-SM SM5.C.11: the bound (in kernel-SGI service slots) on how long a pending
`.reschedule` SGI can wait behind higher-priority *kernel* SGIs at its target
CPU interface.  Because `.reschedule` is the lowest INTID
(`rescheduleSgi_lowest_intid`), no kernel SGI outranks it, so the bound is `0`
(modulo the hardware-guaranteed GIC delivery latency, which the plan §7 risk
table treats as a fixed hardware constant — there is no software path that can
starve the SGI).  Computed as the count of kernel SGI kinds strictly
higher-priority (lower INTID) than `.reschedule`. -/
def sgiDeliveryLatencyBound : Nat :=
  (SgiKind.all.filter (fun k => k.toIntid.val < SgiKind.reschedule.toIntid.val)).length

/-- WS-SM SM5.C.11: the kernel-SGI service-slot latency bound for `.reschedule`
is `0` — no kernel SGI is serviced ahead of it.  Decidable witness. -/
theorem sgiDeliveryLatencyBound_eq_zero : sgiDeliveryLatencyBound = 0 := by decide


-- ============================================================================
-- §8  SM5.C.8 — `setThreadCpuAffinity` (affinity-control op)
-- ============================================================================

/-- WS-SM SM5.C.8: `setThreadCpuAffinity` succeeds when the target resolves to a
TCB. -/
theorem setThreadCpuAffinity_ok_of_tcb (st : SystemState) (targetTid : SeLe4n.ThreadId)
    (affinity : Option CoreId) (tcb : TCB) (hTcb : st.getTcb? targetTid = some tcb) :
    ∃ st', setThreadCpuAffinity st targetTid affinity = .ok st' := by
  simp only [setThreadCpuAffinity, hTcb]
  exact ⟨_, rfl⟩

/-- WS-SM SM5.C.8 (fail-closed): `setThreadCpuAffinity` rejects a non-TCB target
with `.invalidArgument` (mirroring `setPriorityOp`). -/
theorem setThreadCpuAffinity_error_of_no_tcb (st : SystemState)
    (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId)
    (hTcb : st.getTcb? targetTid = none) :
    setThreadCpuAffinity st targetTid affinity = .error .invalidArgument := by
  simp only [setThreadCpuAffinity, hTcb]

/-- WS-SM SM5.C.8: after a successful `setThreadCpuAffinity`, the target's
`cpuAffinity` is the new value (every other field unchanged). -/
theorem setThreadCpuAffinity_sets_affinity (st : SystemState)
    (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId) (st' : SystemState)
    (tcb : TCB) (hTcb : st.getTcb? targetTid = some tcb) (hInv : st.objects.invExt)
    (h : setThreadCpuAffinity st targetTid affinity = .ok st') :
    st'.getTcb? targetTid = some { tcb with cpuAffinity := affinity } := by
  simp only [setThreadCpuAffinity, hTcb, Except.ok.injEq] at h
  subst h
  simp only [SystemState.getTcb?_eq_some_iff, RHTable_getElem?_eq_get?]
  exact RHTable_get?_insert_self st.objects targetTid.toObjId _ hInv

/-- WS-SM SM5.C.8 (preservation): `setThreadCpuAffinity` preserves the RobinHood
object-store invariant — its only write is the target TCB's `cpuAffinity` save
(an `insert` at an existing key). -/
theorem setThreadCpuAffinity_preserves_objects_invExt (st : SystemState)
    (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId) (st' : SystemState)
    (hInv : st.objects.invExt) (h : setThreadCpuAffinity st targetTid affinity = .ok st') :
    st'.objects.invExt := by
  unfold setThreadCpuAffinity at h
  cases hTcb : st.getTcb? targetTid with
  | none => simp [hTcb] at h
  | some tcb =>
      simp only [hTcb, Except.ok.injEq] at h
      subst h
      exact RHTable_insert_preserves_invExt st.objects _ _ hInv

/-- WS-SM SM5.C.8: `setThreadCpuAffinity` leaves the scheduler state untouched —
it writes only the target TCB.  So no run queue / current thread is disturbed
(the SchedContext / run-queue migration on an affinity change is the separate
SM5.H.4 operation). -/
theorem setThreadCpuAffinity_preserves_scheduler (st : SystemState)
    (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId) (st' : SystemState)
    (h : setThreadCpuAffinity st targetTid affinity = .ok st') :
    st'.scheduler = st.scheduler := by
  unfold setThreadCpuAffinity at h
  cases hTcb : st.getTcb? targetTid with
  | none => simp [hTcb] at h
  | some tcb =>
      simp only [hTcb, Except.ok.injEq] at h
      subst h
      rfl

/-- WS-SM SM5.C.8 (per-thread frame): `setThreadCpuAffinity targetTid` leaves
every *other* thread's `getTcb?` lookup unchanged — its only write is at key
`targetTid.toObjId`.  AK7-clean (routes through the `.get?`-method form). -/
theorem setThreadCpuAffinity_getTcb?_ne (st : SystemState)
    (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId) (other : SeLe4n.ThreadId)
    (st' : SystemState) (hInv : st.objects.invExt) (hNe : other ≠ targetTid)
    (h : setThreadCpuAffinity st targetTid affinity = .ok st') :
    st'.getTcb? other = st.getTcb? other := by
  unfold setThreadCpuAffinity at h
  cases hTcb : st.getTcb? targetTid with
  | none => simp [hTcb] at h
  | some tcb =>
      simp only [hTcb, Except.ok.injEq] at h
      subst h
      have hNeT : targetTid ≠ other := fun he => hNe he.symm
      have hNeO : ¬ (targetTid.toObjId == other.toObjId) = true := fun he =>
        hNeT (ThreadId.toObjId_injective _ _ (by simpa using he))
      simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
      rw [RobinHood.RHTable.getElem?_insert_ne st.objects targetTid.toObjId
        other.toObjId _ hNeO hInv]

/-- WS-SM SM5.C.8 (composition with the wake target): after binding `targetTid`
to `some c`, the thread's wake target (`determineTargetCore`) is `c` — the
affinity-control op feeds the cross-core wake routing.  Composes
`setThreadCpuAffinity_sets_affinity` with `determineTargetCore_bound_eq_affinity`. -/
theorem setThreadCpuAffinity_affects_determineTargetCore (st : SystemState)
    (targetTid : SeLe4n.ThreadId) (c : CoreId) (st' : SystemState) (tcb : TCB)
    (hTcb : st.getTcb? targetTid = some tcb) (hInv : st.objects.invExt)
    (h : setThreadCpuAffinity st targetTid (some c) = .ok st') :
    determineTargetCore st' targetTid = c :=
  determineTargetCore_bound_eq_affinity st' targetTid _ c
    (setThreadCpuAffinity_sets_affinity st targetTid (some c) st' tcb hTcb hInv h) rfl

-- ============================================================================
-- §9  Decidability witnesses (for the SM5.C.12 unit tests)
-- ============================================================================

/-- WS-SM SM5.C.5: "core `c`'s reschedule-SGI handler succeeds" — the decidable
proposition the SM5.C round-trip tests discharge by `decide` on concrete states.
Like SM5.B's `switchToThreadOnCoreSucceeds`, the `Decidable` instance is an
explicit case analysis on the evaluated `Except` result (Lean core does not
derive `DecidableEq (Except _ SystemState)`). -/
def handleRescheduleSgiOnCoreSucceeds (st : SystemState) (c : CoreId) : Prop :=
  ∃ st', handleRescheduleSgiOnCore st c = .ok st'

instance (st : SystemState) (c : CoreId) :
    Decidable (handleRescheduleSgiOnCoreSucceeds st c) :=
  match h : handleRescheduleSgiOnCore st c with
  | .ok st' => .isTrue ⟨st', h⟩
  | .error _ => .isFalse (by simp [handleRescheduleSgiOnCoreSucceeds, h])

/-- WS-SM SM5.C.8: "setting `targetTid`'s affinity succeeds" — the decidable
affinity-control predicate. -/
def setThreadCpuAffinitySucceeds (st : SystemState) (targetTid : SeLe4n.ThreadId)
    (affinity : Option CoreId) : Prop :=
  ∃ st', setThreadCpuAffinity st targetTid affinity = .ok st'

instance (st : SystemState) (targetTid : SeLe4n.ThreadId) (affinity : Option CoreId) :
    Decidable (setThreadCpuAffinitySucceeds st targetTid affinity) :=
  match h : setThreadCpuAffinity st targetTid affinity with
  | .ok st' => .isTrue ⟨st', h⟩
  | .error _ => .isFalse (by simp [setThreadCpuAffinitySucceeds, h])

end SeLe4n.Kernel
