-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.PerCoreSwitchToThread
import SeLe4n.Kernel.IPC.Invariant.PerCore

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
  `wakeThread_no_sgi_if_local` / `wakeThread_no_sgi_if_no_tcb` — the wake emits a
  `.reschedule` SGI to the target core iff `tid` resolves to a TCB (audit-pass-1
  ghost-wake guard: a no-op wake pokes no core) **and** the target is remote from
  the executing core.
* **SM5.C.10** `wakeThread_target_runQueue_contains` — the woken thread is in the
  target core's run queue immediately after the wake (the thread is not lost).
* **SM5.C.6 / Theorem 3.3.2** `wakeThread_lossless` — the woken thread is
  recoverable: there is a scheduler-reachable state in which it is current on,
  or enqueued on, its target core (witnessed reflexively by the post-wake state).
  Its genuine *multi-step* strengthening (§6b, audit-pass-1)
  `wakeThread_then_handle_dispatches_current` / `wakeThread_roundtrip_reachable_current`
  walks the `SchedReachable` closure through `.tail`/`.switch`: a wake followed
  by the target's reschedule-SGI handler dispatches the woken thread to
  **current** in two real scheduler steps.
* **SM5.C.5** `handleRescheduleSgiOnCore_*` — the target core's reschedule-SGI
  handler re-chooses and switches (or idles when nothing is runnable), never
  errors under the per-core scheduler invariant, and preserves the structural
  invariants.
* **Invariant preservation (§10, audit-pass-1, the SM5.B-parity coverage)** —
  the wake preserves SM4.C `currentThreadValidOnCore` (every core, unconditional)
  and `queueCurrentConsistentOnCore` (under the seL4-faithful "don't-wake-current"
  precondition), and the full SM4.D `ipcSchedulerContractPredicates_perCore`
  IPC↔scheduler-coherence bundle (`wakeThread_preserves_ipcSchedulerContract`):
  enqueuing a freshly-woken thread is coherent *because* the wake sets
  `ipcState := .ready` — it can never create a runnable-but-blocked thread.
* **SM5.C.11** `wakeThread_emits_at_most_one_sgi` + `rescheduleSgi_*` — the SGI
  delivery latency bound: a wake emits at most one SGI, and the `.reschedule`
  SGI is the lowest-INTID (highest GIC priority) kernel SGI, so it is not
  starved by other kernel coordination SGIs
  (`sgiDeliveryLatencyBound_counts_higher_priority_kernel_sgis` makes the "= 0"
  scope precise: a kernel-SGI-ordering / non-starvation property, not an
  absolute hardware-delivery latency).
* **SM5.C.8** `setThreadCpuAffinity_*` — the affinity-control op sets the
  target's affinity, preserves the object-store invariant and the scheduler
  state, frames out every other thread, and feeds `determineTargetCore` /
  `affinityAdmitsCore`.
* **SM5.C.4 memory-model HB (§11, audit-pass-1)** `wakeOrdering_happensBefore` —
  the wake's BKL-discipline ordering ("the run-queue publication is visible on
  the target before it acts on the SGI") modeled in SM2.A's operational memory
  model: the executing core's release-store synchronizes-with the target core's
  acquire-load, hence happens-before.  The prose ordering is now a theorem.

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

/-- WS-SM SM5.C.9 (audit-pass-2, security / no-liveness-stranding): the wake
**target always admits the woken thread** — `affinityAdmitsCore tcb
(determineTargetCore st tid) = true`.

This is the consistency keystone between `determineTargetCore` (where a thread is
woken to) and `affinityAdmitsCore` (which cores will *dispatch* it,
`switchToThreadOnCore` / `handleRescheduleSgiOnCore`): a bound thread wakes onto
its affinity core, which admits exactly that core; an unbound thread wakes onto
`bootCoreId`, and an unbound thread is admitted on *every* core.  Either way the
target admits it.

Without this, a wake could strand a thread on a run queue of a core whose
dispatch gate rejects it (`.threadOnDifferentCore`) — the thread would be
enqueued but never runnable there, a silent liveness hole.  This theorem proves
that hole cannot exist: every wake lands the thread on a core that will dispatch
it. -/
theorem determineTargetCore_admits_thread (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (hTcb : st.getTcb? tid = some tcb) :
    affinityAdmitsCore tcb (determineTargetCore st tid) = true := by
  unfold determineTargetCore affinityAdmitsCore
  rw [hTcb]
  cases h : tcb.cpuAffinity with
  | none => simp
  | some c' => simp [h]


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
      split
      · exact hInv
      · exact RHTable_insert_preserves_invExt st.objects _ _ hInv

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
      simp only [enqueueRunnableOnCore, hTcb]
      split
      · exact hwf
      · simp only [SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
        exact RunQueue.insert_preserves_wellFormed _ hwf _ _

/-- WS-SM SM5.C.1 (membership): the woken thread is a member of core `c`'s run
queue immediately after `enqueueRunnableOnCore` (when it resolves to a TCB).
The substantive "the wake genuinely enqueues" content. -/
theorem enqueueRunnableOnCore_mem_runQueueOnCore (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb)
    (hFresh : runnableOnSomeCore st tid = false) :
    tid ∈ ((enqueueRunnableOnCore st c tid).scheduler.runQueueOnCore c).toList := by
  simp only [enqueueRunnableOnCore, hTcb, hFresh, Bool.false_eq_true, if_false,
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
    (hTcb : st.getTcb? tid = some tcb) (hInv : st.objects.invExt)
    (hFresh : runnableOnSomeCore st tid = false) :
    (enqueueRunnableOnCore st c tid).getTcb? tid = some { tcb with ipcState := .ready } := by
  simp only [enqueueRunnableOnCore, hTcb, hFresh, Bool.false_eq_true, if_false,
    SystemState.getTcb?_eq_some_iff, RHTable_getElem?_eq_get?]
  exact RHTable_get?_insert_self st.objects tid.toObjId _ hInv

/-- WS-SM SM5.C.1 (audit-pass-2, woken-thread field frame): `enqueueRunnableOnCore`
changes **only** the `ipcState` field of the woken thread — every other field
(`priority`, `domain`, `cpuAffinity`, `threadState`, `registerContext`,
`schedContextBinding`, `pipBoost`, …) is preserved.  The post-state TCB is
exactly `{ tcb with ipcState := .ready }`, which differs from the pre-state TCB
in `ipcState` alone (a record-update of a single field).

This is the "the wake does not silently corrupt thread state" guarantee: the
only mutation the wake makes to the woken thread is clearing its scheduler-visible
IPC block — it cannot, e.g., change the thread's CPU affinity (which would be a
placement leak) or its priority (which would be a scheduling exploit).  Stated as
the four security-relevant projections that callers / NI-reasoning depend on
(`priority` / `domain` / `cpuAffinity` / `threadState`); the full record equality
to `{ tcb with ipcState := .ready }` is `enqueueRunnableOnCore_makes_ready`. -/
theorem enqueueRunnableOnCore_preserves_woken_thread_fields (st : SystemState)
    (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hInv : st.objects.invExt)
    (hFresh : runnableOnSomeCore st tid = false) :
    ∃ tcb', (enqueueRunnableOnCore st c tid).getTcb? tid = some tcb' ∧
      tcb'.priority = tcb.priority ∧ tcb'.domain = tcb.domain ∧
      tcb'.cpuAffinity = tcb.cpuAffinity ∧ tcb'.threadState = tcb.threadState :=
  ⟨{ tcb with ipcState := .ready },
    enqueueRunnableOnCore_makes_ready st c tid tcb hTcb hInv hFresh, rfl, rfl, rfl, rfl⟩

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
      split
      · rfl
      · exact SchedulerState.setRunQueueOnCore_runQueueOnCore_ne st.scheduler c c' _ h

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
      simp only [enqueueRunnableOnCore, hTcb]
      split
      · rfl
      · simp only [SchedulerState.setRunQueueOnCore_currentOnCore]

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
      split
      · rfl
      · simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_ne st.objects tid.toObjId other.toObjId
          _ hNeO hInv]

/-- WS-SM SM5.C.1 (fail-closed): a `tid` that does not resolve to a TCB makes
`enqueueRunnableOnCore` the identity — a corrupted run-queue entry is never
invented. -/
theorem enqueueRunnableOnCore_no_tcb_noop (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (hTcb : st.getTcb? tid = none) :
    enqueueRunnableOnCore st c tid = st := by
  simp only [enqueueRunnableOnCore, hTcb]

/-- WS-SM SM5.C.1 (audit-pass-3 / Codex-P2): when `tid` is *already* runnable on
some core, the single-placement guard makes `enqueueRunnableOnCore` the identity
— the wake creates no second placement.  The structural fact every preservation
proof uses to discharge the reject branch (the post-state is `st`, so any
invariant trivially carries over). -/
theorem enqueueRunnableOnCore_eq_self_of_runnable (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (hRun : runnableOnSomeCore st tid = true) :
    enqueueRunnableOnCore st c tid = st := by
  cases hTcb : st.getTcb? tid with
  | none => simp only [enqueueRunnableOnCore, hTcb]
  | some tcb => simp [enqueueRunnableOnCore, hTcb, hRun]


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

/-- WS-SM SM5.C.4 (plan §3.3, Theorem 3.3.1): a wake of a genuine TCB whose
target core is *remote* from the executing core emits a `.reschedule` SGI to the
target — the target core must be poked to re-run its scheduler and pick up the
newly-runnable thread.

The `hTcb` hypothesis is the audit-pass-1 ghost-wake guard: only a wake that
*actually* enqueues `tid` (i.e. `tid` resolves to a TCB) emits the cross-core
SGI.  Well-formed callers always wake real threads, so this is the operative
form. -/
theorem wakeThread_emits_sgi_if_remote (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb)
    (h : determineTargetCore st tid ≠ executingCore) :
    (wakeThread st tid executingCore).2
      = some (determineTargetCore st tid, SgiKind.reschedule) := by
  have hbeq : (determineTargetCore st tid == executingCore) = false :=
    beq_eq_false_iff_ne.mpr h
  simp only [wakeThread, hTcb]
  rw [if_neg (by simp [hbeq])]

/-- WS-SM SM5.C.4: a wake whose target *is* the executing core emits no SGI —
the local scheduler will pick up the newly-runnable thread on its next decision,
so no cross-core poke is required.  (Holds whether or not `tid` resolves to a
TCB: a local wake never pokes a remote core, and a ghost wake pokes no core.) -/
theorem wakeThread_no_sgi_if_local (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) (h : determineTargetCore st tid = executingCore) :
    (wakeThread st tid executingCore).2 = none := by
  simp only [wakeThread]
  cases st.getTcb? tid with
  | none => rfl
  | some _ => simp only [h, beq_self_eq_true, if_true]

/-- WS-SM SM5.C.4 (audit-pass-1, ghost-wake guard): a wake of a `tid` that does
**not** resolve to a TCB emits *no* SGI — the wake was a fail-closed no-op on the
state (`enqueueRunnableOnCore_no_tcb_noop`), so it must not poke a remote core
for nothing.  This is the soundness content of the SGI-emission guard: the SGI
decision is consistent with the state effect (no enqueue ⇒ no cross-core
notification). -/
theorem wakeThread_no_sgi_if_no_tcb (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) (hTcb : st.getTcb? tid = none) :
    (wakeThread st tid executingCore).2 = none := by
  simp only [wakeThread, hTcb]

/-- WS-SM SM5.C.4: every SGI a wake emits is the `.reschedule` kind — `wakeThread`
never emits a TLB-shootdown / cache-broadcast / halt SGI.  The discriminant that
the SM5.C.11 latency bound (the reschedule SGI is the highest-priority kernel
SGI) rests on. -/
theorem wakeThread_sgi_is_reschedule (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) (target : CoreId) (kind : SgiKind)
    (h : (wakeThread st tid executingCore).2 = some (target, kind)) :
    kind = SgiKind.reschedule := by
  simp only [wakeThread] at h
  -- Two nested matches: the ghost guard (`getTcb?`) then the target==exec `if`.
  cases hTcb : st.getTcb? tid with
  | none => rw [hTcb] at h; simp at h
  | some _ =>
      rw [hTcb] at h
      by_cases hEq : (determineTargetCore st tid == executingCore) = true
      · rw [if_pos hEq] at h; simp at h
      · rw [if_neg hEq, Option.some.injEq, Prod.mk.injEq] at h
        exact h.2.symm

/-- WS-SM SM5.C.10 (plan §3.3): the woken thread is a member of the target
core's run queue immediately after the wake — the wake *does not lose* the
thread.  The substantive content behind `wakeThread_lossless`. -/
theorem wakeThread_target_runQueue_contains (st : SystemState)
    (tid : SeLe4n.ThreadId) (executingCore : CoreId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb)
    (hFresh : runnableOnSomeCore st tid = false) :
    tid ∈ ((wakeThread st tid executingCore).1.scheduler.runQueueOnCore
            (determineTargetCore st tid)).toList := by
  rw [wakeThread_state_eq_enqueue]
  exact enqueueRunnableOnCore_mem_runQueueOnCore st (determineTargetCore st tid) tid tcb hTcb hFresh

/-- WS-SM SM5.C.2 (audit-pass-2, no-liveness-stranding at the wake level): the
target core a wake lands `tid` on **admits** `tid` — so the woken thread, sitting
in the target run queue (`wakeThread_target_runQueue_contains`), is genuinely
dispatchable there (`switchToThreadOnCore` / `handleRescheduleSgiOnCore` will not
reject it with `.threadOnDifferentCore`).  The composition of
`determineTargetCore_admits_thread` with the wake's `determineTargetCore` target:
a wake never strands a thread on a core that cannot run it. -/
theorem wakeThread_target_admits_thread (st : SystemState)
    (tid : SeLe4n.ThreadId) (_executingCore : CoreId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) :
    affinityAdmitsCore tcb (determineTargetCore st tid) = true :=
  determineTargetCore_admits_thread st tid tcb hTcb

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
`(reachable ∧ A) ∨ B` precedence.

The *genuine multi-step* strengthening — the woken thread reaches **current** via
a real `switch` step once its reschedule SGI is serviced — is
`wakeThread_then_handle_dispatches_current` / `wakeThread_roundtrip_reachable_current`
(§6b), which walk the `SchedReachable` closure through `.tail`/`.switch` rather
than witnessing reflexively here. -/
theorem wakeThread_lossless (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb)
    (hFresh : runnableOnSomeCore st tid = false) :
    ∃ futureState : SystemState,
      SchedReachable (wakeThread st tid executingCore).1 futureState ∧
      (futureState.scheduler.currentOnCore (determineTargetCore st tid) = some tid ∨
       tid ∈ (futureState.scheduler.runQueueOnCore (determineTargetCore st tid)).toList) :=
  ⟨(wakeThread st tid executingCore).1, SchedReachable.refl _,
    Or.inr (wakeThread_target_runQueue_contains st tid executingCore tcb hTcb hFresh)⟩


-- ============================================================================
-- §6  SM5.C.5 — `handleRescheduleSgiOnCore` (re-choose + switch / idle)
-- ============================================================================

/-- WS-SM SM5.C.5: when the SGI handler's budget-aware re-choose finds no
eligible thread (`chooseThreadEffectiveOnCore = .ok none`), the handler is the
identity — core `c` keeps running whatever it was (or idles); no spurious
dispatch is invented. -/
theorem handleRescheduleSgiOnCore_idle_when_none (st : SystemState) (c : CoreId)
    (hc : chooseThreadEffectiveOnCore st c = .ok none) :
    handleRescheduleSgiOnCore st c = .ok st := by
  simp only [handleRescheduleSgiOnCore, hc]

/-- WS-SM SM5.C.5 (audit-pass-3): when the budget-aware re-choose selects `tid`
(`chooseThreadEffectiveOnCore = .ok (some tid)`) AND `tid` strictly outranks the
current thread (`candidateOutranksCurrentOnCore`), the handler is exactly the
switch to `tid` (`switchToThreadOnCore`). -/
theorem handleRescheduleSgiOnCore_eq_switch_of_choose_some (st : SystemState)
    (c : CoreId) (tid : SeLe4n.ThreadId)
    (hc : chooseThreadEffectiveOnCore st c = .ok (some tid))
    (hout : candidateOutranksCurrentOnCore st c tid = true) :
    handleRescheduleSgiOnCore st c = switchToThreadOnCore st c tid := by
  simp [handleRescheduleSgiOnCore, hc, hout]

/-- WS-SM SM5.C.5 (audit-pass-3 / Codex-P1): when the budget-aware candidate
`tid` does NOT outrank the current thread (`candidateOutranksCurrentOnCore =
false`), the handler keeps the current thread (identity) — a lower-priority
cross-core wake never preempts a higher-priority running thread. -/
theorem handleRescheduleSgiOnCore_keeps_current_when_outranked (st : SystemState)
    (c : CoreId) (tid : SeLe4n.ThreadId)
    (hc : chooseThreadEffectiveOnCore st c = .ok (some tid))
    (hout : candidateOutranksCurrentOnCore st c tid = false) :
    handleRescheduleSgiOnCore st c = .ok st := by
  simp [handleRescheduleSgiOnCore, hc, hout]

/-- WS-SM SM5.C.5: a successful SGI-handler dispatch (candidate outranks current)
sets core `c`'s current thread to the re-chosen thread.  Composes the SM5.A
selection with the SM5.B switch's `_sets_current` (Theorem 3.2.1). -/
theorem handleRescheduleSgiOnCore_switches_current (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (st' : SystemState)
    (hc : chooseThreadEffectiveOnCore st c = .ok (some tid))
    (hout : candidateOutranksCurrentOnCore st c tid = true)
    (h : handleRescheduleSgiOnCore st c = .ok st') :
    st'.scheduler.currentOnCore c = some tid := by
  rw [handleRescheduleSgiOnCore_eq_switch_of_choose_some st c tid hc hout] at h
  exact switchToThreadOnCore_sets_current st c tid st' h

/-- WS-SM SM5.C.5 (preservation): the SGI handler preserves the RobinHood
object-store invariant — the idle and keep-current branches are the identity,
the dispatch branch is a `switchToThreadOnCore` (which preserves `invExt`,
SM5.B). -/
theorem handleRescheduleSgiOnCore_preserves_objects_invExt (st : SystemState)
    (c : CoreId) (st' : SystemState) (hInv : st.objects.invExt)
    (h : handleRescheduleSgiOnCore st c = .ok st') :
    st'.objects.invExt := by
  unfold handleRescheduleSgiOnCore at h
  split at h
  · exact absurd h (by simp)
  · rw [Except.ok.injEq] at h; subst h; exact hInv
  · split at h
    · exact switchToThreadOnCore_preserves_objects_invExt st c _ st' hInv h
    · rw [Except.ok.injEq] at h; subst h; exact hInv

/-- WS-SM SM5.F.6 (PR #811 P2-5 support): the SGI handler frames out **any** thread
that is not core `c`'s current thread.  The idle / keep-current branches are the
identity; the dispatch branch is a `switchToThreadOnCore` whose only TCB write is the
preempted (current) thread's register-context save (`switchToThreadOnCore_getTcb?_ne_current`).
In particular the resumed thread of `resumeThreadOnCore` — never the executing core's
current, since it was `.Inactive` — retains its `threadState := .Ready` across the inline
local reschedule.  Routes through the typed `getTcb?` accessor (AK7-clean). -/
theorem handleRescheduleSgiOnCore_getTcb?_ne_current (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (st' : SystemState) (hInv : st.objects.invExt)
    (hNe : st.scheduler.currentOnCore c ≠ some tid)
    (h : handleRescheduleSgiOnCore st c = .ok st') :
    st'.getTcb? tid = st.getTcb? tid := by
  unfold handleRescheduleSgiOnCore at h
  split at h
  · exact absurd h (by simp)
  · rw [Except.ok.injEq] at h; subst h; rfl
  · split at h
    · exact switchToThreadOnCore_getTcb?_ne_current st c _ tid st' hInv hNe h
    · rw [Except.ok.injEq] at h; subst h; rfl

/-- WS-SM SM5.C.5 (preservation): the SGI handler preserves core `c`'s run-queue
well-formedness. -/
theorem handleRescheduleSgiOnCore_preserves_runQueueOnCore_wellFormed (st : SystemState)
    (c : CoreId) (st' : SystemState)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (h : handleRescheduleSgiOnCore st c = .ok st') :
    (st'.scheduler.runQueueOnCore c).wellFormed := by
  unfold handleRescheduleSgiOnCore at h
  split at h
  · exact absurd h (by simp)
  · rw [Except.ok.injEq] at h; subst h; exact hwf
  · split at h
    · exact switchToThreadOnCore_preserves_runQueueOnCore_wellFormed st c _ st' hwf h
    · rw [Except.ok.injEq] at h; subst h; exact hwf

/-- WS-SM SM5.C.5 (cross-core independence): the SGI handler on core `c` leaves
every other core's `current` and `runQueue` slots untouched — the idle and
keep-current branches are the identity, the dispatch branch is a
`switchToThreadOnCore` (which is per-core-independent, SM5.B.6). -/
theorem handleRescheduleSgiOnCore_independent_of_other_core (st : SystemState)
    (c c' : CoreId) (st' : SystemState) (hcc : c ≠ c')
    (h : handleRescheduleSgiOnCore st c = .ok st') :
    st'.scheduler.currentOnCore c' = st.scheduler.currentOnCore c'
      ∧ st'.scheduler.runQueueOnCore c' = st.scheduler.runQueueOnCore c' := by
  unfold handleRescheduleSgiOnCore at h
  split at h
  · exact absurd h (by simp)
  · rw [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  · split at h
    · exact switchToThreadOnCore_independent_of_other_core st c c' _ st' hcc h
    · rw [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩

-- ============================================================================
-- §6b  SM5.C.6 — Multi-step wake→dispatch liveness (audit-pass-1)
-- ============================================================================
--
-- `wakeThread_lossless` is the *reflexive* losslessness witness (the woken
-- thread is sitting in the target run queue).  This section proves the genuine
-- *multi-step* statement the `SchedStep` / `SchedReachable` closure exists for:
-- a wake followed by the target core's reschedule-SGI handler dispatches the
-- woken thread to **current**, in two real scheduler steps (an `enqueue` step
-- then a `switch` step) — exercising the `.tail` / `.switch` constructors that
-- `wakeThread_lossless` alone leaves unused.  This is the operational realisation
-- of the cross-core wake → SGI → re-schedule round-trip.

/-- WS-SM SM5.C.6 (multi-step liveness): the wake → reschedule-SGI-handler
round-trip dispatches the woken thread to **current** on its target core, in two
genuine `SchedStep`s.

Hypotheses: after the wake, the target core's budget-aware scheduler selects
`tid` as its next thread (`hChoose` — the handler's `chooseThreadEffectiveOnCore`
picks `tid`) AND `tid` strictly outranks the target core's current thread
(`hOutrank` — the plan's "no higher-priority work preempts" condition, made
precise by the audit-pass-3 preemption gate `candidateOutranksCurrentOnCore`).
Under these, there is a state reachable from the post-wake state — by a real
`switch` step, NOT reflexively — in which `tid` is **current** on the target
core.

This is the operational liveness `wakeThread_lossless` defers: it composes the
enqueue (wake) with the dispatch (SGI handler) and genuinely walks the
`SchedReachable` closure via `.tail`/`.switch`, witnessing that a cross-core wake
is not merely "not lost" but *actually scheduled* once its SGI is serviced and
the woken thread outranks the running one.  The fully-unconditional
eventual-scheduling property (discharging `hChoose` / `hOutrank` from the
per-core scheduler invariant + idle fallback) is SM5.E/SM5.J. -/
theorem wakeThread_then_handle_dispatches_current (st : SystemState)
    (tid : SeLe4n.ThreadId) (executingCore : CoreId)
    (st2 : SystemState)
    (hChoose : chooseThreadEffectiveOnCore (wakeThread st tid executingCore).1
                  (determineTargetCore st tid) = .ok (some tid))
    (hOutrank : candidateOutranksCurrentOnCore (wakeThread st tid executingCore).1
                  (determineTargetCore st tid) tid = true)
    (hHandle : handleRescheduleSgiOnCore (wakeThread st tid executingCore).1
                  (determineTargetCore st tid) = .ok st2) :
    SchedReachable (wakeThread st tid executingCore).1 st2 ∧
      st2.scheduler.currentOnCore (determineTargetCore st tid) = some tid := by
  refine ⟨?_, ?_⟩
  · -- A genuine 2nd `SchedStep`: the handler reduces to a `switchToThreadOnCore`
    -- (since the budget-aware choice is `.ok (some tid)` and `tid` outranks
    -- current), which is a `.switch` step.
    have hSwitch : switchToThreadOnCore (wakeThread st tid executingCore).1
        (determineTargetCore st tid) tid = .ok st2 := by
      rw [← handleRescheduleSgiOnCore_eq_switch_of_choose_some _ _ _ hChoose hOutrank]
      exact hHandle
    exact SchedReachable.tail _ _ _ (SchedReachable.refl _)
      (SchedStep.switch _ _ (determineTargetCore st tid) tid hSwitch)
  · exact handleRescheduleSgiOnCore_switches_current _ (determineTargetCore st tid) tid st2
      hChoose hOutrank hHandle

/-- WS-SM SM5.C.6 (multi-step liveness, the full chain from the *pre*-wake state):
the whole `wake → SGI handler → current` round-trip is a `SchedReachable` path
from the **original** state to the dispatched state — composing the wake's
`enqueue` step with the handler's `switch` step into a single 2-step closure
witness from `st`.  This is the end-to-end cross-core wake liveness: starting
from any state, waking `tid` and servicing the resulting reschedule SGI (when the
woken thread outranks the target's current) reaches a state in which `tid` runs
on its target core. -/
theorem wakeThread_roundtrip_reachable_current (st : SystemState)
    (tid : SeLe4n.ThreadId) (executingCore : CoreId)
    (st2 : SystemState)
    (hChoose : chooseThreadEffectiveOnCore (wakeThread st tid executingCore).1
                  (determineTargetCore st tid) = .ok (some tid))
    (hOutrank : candidateOutranksCurrentOnCore (wakeThread st tid executingCore).1
                  (determineTargetCore st tid) tid = true)
    (hHandle : handleRescheduleSgiOnCore (wakeThread st tid executingCore).1
                  (determineTargetCore st tid) = .ok st2) :
    SchedReachable st st2 ∧
      st2.scheduler.currentOnCore (determineTargetCore st tid) = some tid := by
  obtain ⟨hReach, hCur⟩ :=
    wakeThread_then_handle_dispatches_current st tid executingCore st2 hChoose hOutrank hHandle
  refine ⟨?_, hCur⟩
  -- Prepend the wake's `enqueue` step: `st → (wakeThread …).1` is a `SchedStep`.
  have hWakeStep : SchedReachable st (wakeThread st tid executingCore).1 := by
    rw [wakeThread_state_eq_enqueue]
    exact SchedReachable.of_enqueue st (determineTargetCore st tid) tid
  exact SchedReachable.trans hWakeStep hReach

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

/-- WS-SM SM5.C.11 (audit-pass-1, honest scoping): `sgiDeliveryLatencyBound`
counts *exactly* the kernel SGIs that outrank `.reschedule` in GIC priority
(lower INTID), and that count is `0`.  This theorem makes the *precise meaning*
of the "= 0" headline unambiguous, separating what is proven from what is not:

* **Proven (software):** zero kernel coordination SGIs are serviced ahead of a
  pending `.reschedule` at the target CPU interface — no software path
  (TLB-shootdown / cache-broadcast / halt SGI) can queue ahead of and starve the
  reschedule.  This is `sgiDeliveryLatencyBound = (kinds with lower INTID).length
  = 0`.
* **NOT proven here (hardware / future phases):** the *absolute* wall-clock
  delivery + preemption latency, which depends on the GIC hardware, the target
  core's DAIF/PMR interrupt-masking window, and ties into the WCRT analysis
  (SM5.J).  The plan §7 risk table treats GIC SGI delivery as a fixed hardware
  constant; SM5.J bounds the end-to-end response time.

So `sgiDeliveryLatencyBound` is a *kernel-SGI-ordering* bound (a software
non-starvation property), not an absolute-latency bound — the honest reading of
the "= 0". -/
theorem sgiDeliveryLatencyBound_counts_higher_priority_kernel_sgis :
    sgiDeliveryLatencyBound
      = (SgiKind.all.filter (fun k => k.toIntid.val < SgiKind.reschedule.toIntid.val)).length :=
  rfl


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

-- ============================================================================
-- §10  SM5.C invariant preservation (audit-pass-1: the SM5.B-parity coverage)
-- ============================================================================
--
-- `enqueueRunnableOnCore` / `wakeThread` are genuine state mutations (they set
-- `ipcState := .ready` and insert into a run queue), so — like SM5.B's switch —
-- they carry preservation obligations.  This section proves the SM4.C per-core
-- scheduler-invariant conjuncts and the SM4.D per-core IPC↔scheduler-contract
-- conjuncts that the wake must preserve, closing the audit-pass-1 gap where the
-- wake shipped with strictly weaker invariant coverage than the switch.
--
-- The pivotal soundness fact (the rebuttal to "a wake makes a thread runnable
-- while still blocked"): `enqueueRunnableOnCore` sets `ipcState := .ready` on the
-- enqueued thread, so it *establishes* `runnableThreadIpcReady` and *vacates*
-- every `blockedOn*` predicate for that thread — enqueuing a freshly-woken thread
-- is therefore IPC↔scheduler-coherent by construction, not in spite of the
-- mutation.  The one genuine precondition is on `queueCurrentConsistentOnCore`:
-- you must not "wake" a core's *currently-running* thread (the seL4-faithful
-- "don't enqueue the current thread" discipline); under that precondition the
-- consistency conjunct is preserved.

/-- WS-SM SM5.C.1 (preservation helper): `enqueueRunnableOnCore` preserves
TCB-resolvability of *any* thread.  A thread `t` that resolved to a TCB before
the wake still resolves to one after — the only object write is at `tid`'s key,
and it writes a TCB (`{tcb with ipcState := .ready}`), so neither the `t = tid`
case (the new value is still a TCB) nor the `t ≠ tid` case (framed out) can lose
resolvability.  Routes through the typed `getTcb?` accessor (AK7-clean). -/
theorem enqueueRunnableOnCore_getTcb?_isSome (st : SystemState) (c : CoreId)
    (tid t : SeLe4n.ThreadId) (tcb : TCB) (hInv : st.objects.invExt)
    (hres : st.getTcb? t = some tcb) :
    ∃ tcb', (enqueueRunnableOnCore st c tid).getTcb? t = some tcb' := by
  cases hFresh : runnableOnSomeCore st tid with
  | true =>
      -- Single-placement reject: the wake is the identity, so the lookup is `st`'s.
      rw [enqueueRunnableOnCore_eq_self_of_runnable st c tid hFresh]; exact ⟨tcb, hres⟩
  | false =>
      by_cases hEq : t = tid
      · subst hEq
        -- `tid` resolves to a TCB pre-wake; post-wake it is `{tcb with ipcState := .ready}`.
        exact ⟨_, enqueueRunnableOnCore_makes_ready st c t tcb hres hInv hFresh⟩
      · -- `t ≠ tid`: framed out, so the lookup is unchanged.
        rw [enqueueRunnableOnCore_getTcb?_ne st c tid t hInv hEq]
        exact ⟨tcb, hres⟩

/-- WS-SM SM5.C.1 (preservation, SM4.C `currentThreadValidOnCore`): a wake
preserves current-thread validity on **every** core `c'`.  The wake never writes
any `current` slot (`enqueueRunnableOnCore_currentOnCore`), and it preserves
TCB-resolvability of whatever thread is current there
(`enqueueRunnableOnCore_getTcb?_isSome`).  Holds unconditionally — no
"don't-wake-current" precondition is needed for validity (only for queue
consistency, below). -/
theorem enqueueRunnableOnCore_preserves_currentThreadValidOnCore (st : SystemState)
    (c c' : CoreId) (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (hValid : currentThreadValidOnCore st c') :
    currentThreadValidOnCore (enqueueRunnableOnCore st c tid) c' := by
  unfold currentThreadValidOnCore at hValid ⊢
  rw [enqueueRunnableOnCore_currentOnCore st c tid c']
  cases hCur : st.scheduler.currentOnCore c' with
  | none => exact trivial
  | some cur =>
      rw [hCur] at hValid
      obtain ⟨curTcb, hCurTcb⟩ := hValid
      exact enqueueRunnableOnCore_getTcb?_isSome st c tid cur curTcb hInv hCurTcb

/-- WS-SM SM5.C.1 (preservation, SM4.C `queueCurrentConsistentOnCore`): a wake on
core `c` preserves dequeue-on-dispatch consistency on a **sibling** core `c' ≠ c`
unconditionally — it touches neither `c'`'s `current` slot nor `c'`'s run queue
(`enqueueRunnableOnCore_currentOnCore` + `_runQueueOnCore_ne`). -/
theorem enqueueRunnableOnCore_preserves_queueCurrentConsistentOnCore_ne
    (st : SystemState) (c c' : CoreId) (tid : SeLe4n.ThreadId) (hcc : c ≠ c')
    (hcons : queueCurrentConsistentOnCore st.scheduler c') :
    queueCurrentConsistentOnCore (enqueueRunnableOnCore st c tid).scheduler c' := by
  unfold queueCurrentConsistentOnCore at hcons ⊢
  rw [enqueueRunnableOnCore_currentOnCore st c tid c']
  cases hCur : st.scheduler.currentOnCore c' with
  | none => exact trivial
  | some cur =>
      rw [hCur] at hcons
      rw [enqueueRunnableOnCore_runQueueOnCore_ne st c c' tid hcc]
      exact hcons

/-- WS-SM SM5.C.1 (preservation, SM4.C `queueCurrentConsistentOnCore`, the
target core): a wake on core `c` preserves dequeue-on-dispatch consistency on
core `c` itself **provided the woken thread is not core `c`'s current thread**
(`hNotCur`).  This is the seL4-faithful "do not enqueue the running thread"
precondition: the real wake only ever targets *blocked* threads, never the one
currently executing, so `hNotCur` always holds at the call site.

Without `hNotCur`, the wake could enqueue `tid` while `current c = some tid`,
which would put the current thread into its own run queue — exactly the
inconsistency this conjunct forbids.  Stating the precondition explicitly (rather
than adding a never-taken runtime guard) is the SM5.B discipline
(`currentThreadValid` is likewise a stated precondition, not a runtime branch). -/
theorem enqueueRunnableOnCore_preserves_queueCurrentConsistentOnCore_self
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hNotCur : st.scheduler.currentOnCore c ≠ some tid)
    (hcons : queueCurrentConsistentOnCore st.scheduler c) :
    queueCurrentConsistentOnCore (enqueueRunnableOnCore st c tid).scheduler c := by
  unfold queueCurrentConsistentOnCore at hcons ⊢
  rw [enqueueRunnableOnCore_currentOnCore st c tid c]
  cases hCur : st.scheduler.currentOnCore c with
  | none => exact trivial
  | some cur =>
      simp only [hCur] at hcons
      -- `cur ≠ tid` (else `current c = some tid`, contradicting `hNotCur`).
      have hCurNeTid : cur ≠ tid := by
        intro he; apply hNotCur; rw [hCur, he]
      -- Post-wake `runQueue c = (runQueue c).insert tid prio`; `cur ∈` it iff
      -- `cur ∈ old ∨ cur = tid`; the latter is false, the former is `hcons`.
      cases hTcb : st.getTcb? tid with
      | none =>
          -- No-op wake: run queue unchanged.
          rw [enqueueRunnableOnCore_no_tcb_noop st c tid hTcb]; exact hcons
      | some tcb =>
          cases hFresh : runnableOnSomeCore st tid with
          | true =>
              -- Single-placement reject: the wake is the identity, run queue unchanged.
              rw [enqueueRunnableOnCore_eq_self_of_runnable st c tid hFresh]; exact hcons
          | false =>
              simp only [enqueueRunnableOnCore, hTcb, hFresh, Bool.false_eq_true, if_false,
                SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
              -- Goal: `cur ∉ ((rq).insert tid prio).toList`.  Reduce both the goal
              -- and `hcons` to `RunQueue`-membership and use `mem_insert`.
              rw [RunQueue.mem_toList_iff_mem] at hcons
              rw [RunQueue.mem_toList_iff_mem]
              intro hmem
              rcases (RunQueue.mem_insert _ tid _ cur).mp hmem with hOld | hEqTid
              · exact hcons hOld
              · exact hCurNeTid hEqTid

-- ── §10b  IPC↔scheduler-contract preservation (the gap-(b) soundness result) ──
--
-- The substantive rebuttal to "a wake makes a thread runnable while still
-- blocked": `enqueueRunnableOnCore` sets `ipcState := .ready` on the enqueued
-- thread, so the wake *cannot* create a runnable-but-blocked inconsistency — it
-- establishes the very `ipcState = .ready` that `runnableThreadIpcReady` requires
-- and vacates every `blockedOn*` predicate for the woken thread.  These proofs
-- discharge the SM4.D per-core IPC↔scheduler coherence conjuncts.
--
-- (Caller obligation, documented not proved here: the *structural* IPC side —
-- removing `tid` from any endpoint `sendQ`/`receiveQ` or notification
-- `waitingThreads` list it was blocked on — is the caller's job.  The
-- `queueHeadBlockedConsistent` / `ipcStateQueueMembershipConsistent` /
-- `notificationWaiterConsistent` invariants (IPC/Invariant/Defs.lean) require an
-- endpoint/notification-queue member to carry a matching `blockedOn*` ipcState;
-- since `enqueueRunnableOnCore` sets `ipcState := .ready`, the IPC operation that
-- calls the wake must have *already dequeued* `tid` from those IPC structures
-- (otherwise it would leave a `.ready` thread sitting in a wait queue).  This is
-- the same dequeue-then-wake discipline `IPC.ensureRunnable`'s callers follow —
-- with one honest difference: `ensureRunnable` itself does *not* touch `ipcState`
-- (its callers clear it separately via `storeTcbIpcStateAndMessage` after the
-- dequeue), whereas `enqueueRunnableOnCore` bundles the `ipcState := .ready`
-- clear into the wake.  Either way the dequeue-from-IPC-structures step is the
-- caller's responsibility and is outside this run-queue-membership footprint; the
-- `currentNot*` / queue-structural conjuncts are likewise not
-- run-queue-membership predicates and are outside the wake's footprint.)

/-- WS-SM SM5.C.1 (SM4.D `runnableThreadIpcReady_perCore` preservation): every
TCB in core `c`'s run queue after the wake has `ipcState = .ready`.

The woken thread `wtid` has `.ready` by construction (`_makes_ready`); every
*other* run-queue member was already in the queue (`mem_insert`) and its TCB is
unchanged (`_getTcb?_ne`), so it inherits the pre-state's readiness.  This is the
formal statement that enqueuing a freshly-woken thread is IPC↔scheduler-coherent
*because* of — not in spite of — the `ipcState := .ready` write. -/
theorem enqueueRunnableOnCore_preserves_runnableThreadIpcReady (st : SystemState)
    (c : CoreId) (wtid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (hpre : runnableThreadIpcReady_perCore st c) :
    runnableThreadIpcReady_perCore (enqueueRunnableOnCore st c wtid) c := by
  cases hFresh : runnableOnSomeCore st wtid with
  | true =>
      -- Single-placement reject: the wake is the identity, so the predicate carries over.
      rw [enqueueRunnableOnCore_eq_self_of_runnable st c wtid hFresh]; exact hpre
  | false =>
    unfold runnableThreadIpcReady_perCore at hpre ⊢
    intro t tcb hTcb hMem
    by_cases hEq : t = wtid
    · -- The woken thread: its post-state TCB is `{orig with ipcState := .ready}`.
      subst hEq
      cases hOrig : st.getTcb? t with
      | none =>
          -- No-op wake: `getTcb? t` post = pre = none, contradicting `hTcb`.
          rw [enqueueRunnableOnCore_no_tcb_noop st c t hOrig] at hTcb
          rw [hOrig] at hTcb; exact absurd hTcb (by simp)
      | some origTcb =>
          have hReady := enqueueRunnableOnCore_makes_ready st c t origTcb hOrig hInv hFresh
          rw [hTcb] at hReady
          -- `some tcb = some {origTcb with ipcState := .ready}` ⇒ tcb.ipcState = .ready.
          injection hReady with hEqTcb
          rw [hEqTcb]
    · -- A non-woken thread: framed TCB + membership came from the pre-queue.
      rw [enqueueRunnableOnCore_getTcb?_ne st c wtid t hInv hEq] at hTcb
      -- Reduce post-queue membership to pre-queue membership (drop the `= wtid` arm).
      have hMemPre : t ∈ (st.scheduler.runQueueOnCore c).toList := by
        cases hOrig : st.getTcb? wtid with
        | none =>
            rw [enqueueRunnableOnCore_no_tcb_noop st c wtid hOrig] at hMem; exact hMem
        | some origTcb =>
            simp only [enqueueRunnableOnCore, hOrig, hFresh, Bool.false_eq_true, if_false,
              SchedulerState.setRunQueueOnCore_runQueueOnCore_self] at hMem
            rw [RunQueue.mem_toList_iff_mem] at hMem ⊢
            rcases (RunQueue.mem_insert _ wtid _ t).mp hMem with hOld | hEqW
            · exact hOld
            · exact absurd hEqW hEq
      exact hpre t tcb hTcb hMemPre

/-- WS-SM SM5.C.1 (SM4.D `blockedOn*NotRunnable_perCore` preservation, generic
form): a thread that is `blockedOn*` after the wake is not in core `c`'s run
queue.  The woken thread is `.ready` post-wake (not `blockedOn*`), so the
hypothesis can only fire on a *non-woken* thread, whose block-state and run-queue
membership are both framed by the wake — reducing to the pre-state predicate.

This single lemma is parameterised over the block-state extractor so all five
`blockedOnSend/Receive/Call/Reply/Notification` conjuncts reduce to it. -/
private theorem enqueueRunnableOnCore_preserves_blockedNotRunnable_aux
    (st : SystemState) (c : CoreId) (wtid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (P : TCB → Prop)
    (hPnotReady : ∀ tcb : TCB, P tcb → tcb.ipcState ≠ .ready)
    (hpre : ∀ (t : SeLe4n.ThreadId) (tcb : TCB),
      st.getTcb? t = some tcb → P tcb → t ∉ (st.scheduler.runQueueOnCore c).toList) :
    ∀ (t : SeLe4n.ThreadId) (tcb : TCB),
      (enqueueRunnableOnCore st c wtid).getTcb? t = some tcb → P tcb →
      t ∉ ((enqueueRunnableOnCore st c wtid).scheduler.runQueueOnCore c).toList := by
  cases hFresh : runnableOnSomeCore st wtid with
  | true =>
      -- Single-placement reject: the wake is the identity; the predicate carries over.
      rw [enqueueRunnableOnCore_eq_self_of_runnable st c wtid hFresh]; exact hpre
  | false =>
    intro t tcb hTcb hP hMem
    by_cases hEq : t = wtid
    · -- The woken thread is `.ready`, so it cannot satisfy a `blockedOn*` predicate.
      subst hEq
      cases hOrig : st.getTcb? t with
      | none =>
          rw [enqueueRunnableOnCore_no_tcb_noop st c t hOrig] at hTcb
          rw [hOrig] at hTcb; exact absurd hTcb (by simp)
      | some origTcb =>
          have hReady := enqueueRunnableOnCore_makes_ready st c t origTcb hOrig hInv hFresh
          rw [hTcb] at hReady
          injection hReady with hEqTcb
          exact hPnotReady tcb hP (by rw [hEqTcb])
    · -- Non-woken thread: framed TCB + run-queue membership; reduce to the pre-state.
      rw [enqueueRunnableOnCore_getTcb?_ne st c wtid t hInv hEq] at hTcb
      have hMemPre : t ∈ (st.scheduler.runQueueOnCore c).toList := by
        cases hOrig : st.getTcb? wtid with
        | none =>
            rw [enqueueRunnableOnCore_no_tcb_noop st c wtid hOrig] at hMem; exact hMem
        | some origTcb =>
            simp only [enqueueRunnableOnCore, hOrig, hFresh, Bool.false_eq_true, if_false,
              SchedulerState.setRunQueueOnCore_runQueueOnCore_self] at hMem
            rw [RunQueue.mem_toList_iff_mem] at hMem ⊢
            rcases (RunQueue.mem_insert _ wtid _ t).mp hMem with hOld | hEqW
            · exact hOld
            · exact absurd hEqW hEq
      exact hpre t tcb hTcb hP hMemPre

/-- WS-SM SM5.C.1: `blockedOnSendNotRunnable_perCore` preservation. -/
theorem enqueueRunnableOnCore_preserves_blockedOnSendNotRunnable (st : SystemState)
    (c : CoreId) (wtid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (hpre : blockedOnSendNotRunnable_perCore st c) :
    blockedOnSendNotRunnable_perCore (enqueueRunnableOnCore st c wtid) c := by
  intro t tcb ep hTcb hBlocked
  exact enqueueRunnableOnCore_preserves_blockedNotRunnable_aux st c wtid hInv
    (fun tc => ∃ e, tc.ipcState = .blockedOnSend e)
    (fun tc ⟨e, he⟩ => by rw [he]; simp)
    (fun t' tc' hTc' ⟨e', he'⟩ => hpre t' tc' e' hTc' he')
    t tcb hTcb ⟨ep, hBlocked⟩

/-- WS-SM SM5.C.1: `blockedOnReceiveNotRunnable_perCore` preservation. -/
theorem enqueueRunnableOnCore_preserves_blockedOnReceiveNotRunnable (st : SystemState)
    (c : CoreId) (wtid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (hpre : blockedOnReceiveNotRunnable_perCore st c) :
    blockedOnReceiveNotRunnable_perCore (enqueueRunnableOnCore st c wtid) c := by
  intro t tcb ep hTcb hBlocked
  exact enqueueRunnableOnCore_preserves_blockedNotRunnable_aux st c wtid hInv
    (fun tc => ∃ e, tc.ipcState = .blockedOnReceive e)
    (fun tc ⟨e, he⟩ => by rw [he]; simp)
    (fun t' tc' hTc' ⟨e', he'⟩ => hpre t' tc' e' hTc' he')
    t tcb hTcb ⟨ep, hBlocked⟩

/-- WS-SM SM5.C.1: `blockedOnCallNotRunnable_perCore` preservation. -/
theorem enqueueRunnableOnCore_preserves_blockedOnCallNotRunnable (st : SystemState)
    (c : CoreId) (wtid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (hpre : blockedOnCallNotRunnable_perCore st c) :
    blockedOnCallNotRunnable_perCore (enqueueRunnableOnCore st c wtid) c := by
  intro t tcb ep hTcb hBlocked
  exact enqueueRunnableOnCore_preserves_blockedNotRunnable_aux st c wtid hInv
    (fun tc => ∃ e, tc.ipcState = .blockedOnCall e)
    (fun tc ⟨e, he⟩ => by rw [he]; simp)
    (fun t' tc' hTc' ⟨e', he'⟩ => hpre t' tc' e' hTc' he')
    t tcb hTcb ⟨ep, hBlocked⟩

/-- WS-SM SM5.C.1: `blockedOnReplyNotRunnable_perCore` preservation.  The reply
state carries an extra `replyTarget` field, so the existential packs both. -/
theorem enqueueRunnableOnCore_preserves_blockedOnReplyNotRunnable (st : SystemState)
    (c : CoreId) (wtid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (hpre : blockedOnReplyNotRunnable_perCore st c) :
    blockedOnReplyNotRunnable_perCore (enqueueRunnableOnCore st c wtid) c := by
  intro t tcb ep rt hTcb hBlocked
  exact enqueueRunnableOnCore_preserves_blockedNotRunnable_aux st c wtid hInv
    (fun tc => ∃ e r, tc.ipcState = .blockedOnReply e r)
    (fun tc ⟨e, r, he⟩ => by rw [he]; simp)
    (fun t' tc' hTc' ⟨e', r', he'⟩ => hpre t' tc' e' r' hTc' he')
    t tcb hTcb ⟨ep, rt, hBlocked⟩

/-- WS-SM SM5.C.1: `blockedOnNotificationNotRunnable_perCore` preservation. -/
theorem enqueueRunnableOnCore_preserves_blockedOnNotificationNotRunnable (st : SystemState)
    (c : CoreId) (wtid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (hpre : blockedOnNotificationNotRunnable_perCore st c) :
    blockedOnNotificationNotRunnable_perCore (enqueueRunnableOnCore st c wtid) c := by
  intro t tcb ntfn hTcb hBlocked
  exact enqueueRunnableOnCore_preserves_blockedNotRunnable_aux st c wtid hInv
    (fun tc => ∃ n, tc.ipcState = .blockedOnNotification n)
    (fun tc ⟨n, hn⟩ => by rw [hn]; simp)
    (fun t' tc' hTc' ⟨n', hn'⟩ => hpre t' tc' n' hTc' hn')
    t tcb hTcb ⟨ntfn, hBlocked⟩

/-- WS-SM SM5.C.1 (the aggregate gap-(b) result): `enqueueRunnableOnCore`
preserves the full SM4.D **IPC↔scheduler coherence** bundle
`ipcSchedulerContractPredicates_perCore` on the target core — all six conjuncts
(runnable-are-ready + the five blocked-not-runnable).  This is the formal
statement that a cross-core wake never produces a runnable-but-still-blocked
thread: the wake establishes `ipcState = .ready`, which simultaneously satisfies
`runnableThreadIpcReady` and falsifies every `blockedOn*` antecedent for the
woken thread, while framing every other thread. -/
theorem enqueueRunnableOnCore_preserves_ipcSchedulerContract (st : SystemState)
    (c : CoreId) (wtid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (hpre : ipcSchedulerContractPredicates_perCore st c) :
    ipcSchedulerContractPredicates_perCore (enqueueRunnableOnCore st c wtid) c := by
  obtain ⟨hReady, hSend, hRecv, hCall, hReply, hNotif⟩ := hpre
  exact ⟨enqueueRunnableOnCore_preserves_runnableThreadIpcReady st c wtid hInv hReady,
    enqueueRunnableOnCore_preserves_blockedOnSendNotRunnable st c wtid hInv hSend,
    enqueueRunnableOnCore_preserves_blockedOnReceiveNotRunnable st c wtid hInv hRecv,
    enqueueRunnableOnCore_preserves_blockedOnCallNotRunnable st c wtid hInv hCall,
    enqueueRunnableOnCore_preserves_blockedOnReplyNotRunnable st c wtid hInv hReply,
    enqueueRunnableOnCore_preserves_blockedOnNotificationNotRunnable st c wtid hInv hNotif⟩

-- ── §10d  `wakeThread`-level invariant preservation (the headline closures) ──
--
-- The `wakeThread` state component is `enqueueRunnableOnCore st (target) tid`
-- (`wakeThread_state_eq_enqueue`), so each `enqueueRunnableOnCore_preserves_*`
-- lifts directly.  These are the SM5.B-parity headline preservation theorems for
-- the wake: a wake preserves current-thread validity and the IPC↔scheduler
-- contract unconditionally, and queue/current consistency under the
-- "don't-wake-current" precondition.

/-- WS-SM SM5.C.2 (preservation): a wake preserves `currentThreadValidOnCore` on
every core.  Unconditional (no wake precondition needed for validity). -/
theorem wakeThread_preserves_currentThreadValidOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (executingCore : CoreId) (c' : CoreId)
    (hInv : st.objects.invExt) (hValid : currentThreadValidOnCore st c') :
    currentThreadValidOnCore (wakeThread st tid executingCore).1 c' := by
  rw [wakeThread_state_eq_enqueue]
  exact enqueueRunnableOnCore_preserves_currentThreadValidOnCore st
    (determineTargetCore st tid) c' tid hInv hValid

/-- WS-SM SM5.C.2 (preservation, the gap-(b) headline): a wake preserves the full
SM4.D IPC↔scheduler coherence bundle on the target core — it never creates a
runnable-but-blocked thread.  This is the wake-level statement of the soundness
property that closes the audit-pass-1 gap. -/
theorem wakeThread_preserves_ipcSchedulerContract (st : SystemState)
    (tid : SeLe4n.ThreadId) (executingCore : CoreId) (hInv : st.objects.invExt)
    (hpre : ipcSchedulerContractPredicates_perCore st (determineTargetCore st tid)) :
    ipcSchedulerContractPredicates_perCore (wakeThread st tid executingCore).1
      (determineTargetCore st tid) := by
  rw [wakeThread_state_eq_enqueue]
  exact enqueueRunnableOnCore_preserves_ipcSchedulerContract st
    (determineTargetCore st tid) tid hInv hpre

/-- WS-SM SM5.C.2 (preservation, SM4.C `queueCurrentConsistentOnCore`): a wake
preserves dequeue-on-dispatch consistency on **every** core `c'`, provided the
woken thread is not core `c'`'s current thread when `c'` is the target.

For a sibling core (`c' ≠ target`) the wake doesn't touch `c'` at all; for the
target core itself the "don't-wake-current" precondition `hNotCur` is required (a
wake never targets the running thread, so `hNotCur` always holds at the call
site).  This unifies the sibling and target cases into the single
`queueCurrentConsistentOnCore` headline. -/
theorem wakeThread_preserves_queueCurrentConsistentOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (executingCore : CoreId) (c' : CoreId)
    (hNotCur : st.scheduler.currentOnCore (determineTargetCore st tid) ≠ some tid)
    (hcons : queueCurrentConsistentOnCore st.scheduler c') :
    queueCurrentConsistentOnCore (wakeThread st tid executingCore).1.scheduler c' := by
  rw [wakeThread_state_eq_enqueue]
  by_cases hcc : determineTargetCore st tid = c'
  · subst hcc
    exact enqueueRunnableOnCore_preserves_queueCurrentConsistentOnCore_self st
      (determineTargetCore st tid) tid hNotCur hcons
  · exact enqueueRunnableOnCore_preserves_queueCurrentConsistentOnCore_ne st
      (determineTargetCore st tid) c' tid hcc hcons

/-- WS-SM SM5.I.8 (preservation, SM5.I `runQueueUniqueOnCore`): a wake on core `c`
preserves run-queue `Nodup` on **every** core `c'` — a sibling's queue is framed;
the target's queue takes a `RunQueue.insert` (or a no-op), both `Nodup`-preserving. -/
theorem enqueueRunnableOnCore_preserves_runQueueUniqueOnCore (st : SystemState)
    (c c' : CoreId) (tid : SeLe4n.ThreadId)
    (hnd : (st.scheduler.runQueueOnCore c').toList.Nodup) :
    ((enqueueRunnableOnCore st c tid).scheduler.runQueueOnCore c').toList.Nodup := by
  by_cases hcc : c = c'
  · subst hcc
    cases hTcb : st.getTcb? tid with
    | none => rw [enqueueRunnableOnCore_no_tcb_noop st c tid hTcb]; exact hnd
    | some tcb =>
      cases hFresh : runnableOnSomeCore st tid with
      | true => rw [enqueueRunnableOnCore_eq_self_of_runnable st c tid hFresh]; exact hnd
      | false =>
        simp only [enqueueRunnableOnCore, hTcb, hFresh, Bool.false_eq_true, if_false,
          SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
        exact RunQueue.insert_preserves_toList_nodup _ _ _ hnd
  · rw [enqueueRunnableOnCore_runQueueOnCore_ne st c c' tid hcc]; exact hnd

/-- WS-SM SM5.I.8: a wake preserves run-queue `Nodup` on every core `c'`. -/
theorem wakeThread_preserves_runQueueUniqueOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore c' : CoreId)
    (hnd : (st.scheduler.runQueueOnCore c').toList.Nodup) :
    ((wakeThread st tid executingCore).1.scheduler.runQueueOnCore c').toList.Nodup := by
  rw [wakeThread_state_eq_enqueue]
  exact enqueueRunnableOnCore_preserves_runQueueUniqueOnCore st
    (determineTargetCore st tid) c' tid hnd

-- ============================================================================
-- §11  SM5.C.4 — Memory-model happens-before for the wake (audit-pass-1, gap e)
-- ============================================================================
--
-- The BKL-discipline ordering "the run-queue insertion is visible on the target
-- core before the `.reschedule` SGI is acted upon there" is, until now, asserted
-- only in prose (backed by the Rust `dsb ish` before `GICD_SGIR`, SM1.F.8).  This
-- section *models* that ordering in SM2.A's operational memory model: it exhibits
-- the wake's two cross-core-relevant atomic events — a **release-store** by the
-- executing core (publishing the run-queue update, the `dsb ish`/release that
-- precedes the SGI) and an **acquire-load** by the target core (the GIC
-- delivering the SGI is the acquire that observes the published state) — and
-- proves they form a `synchronizesWith` edge, hence a `happensBefore` edge.
--
-- This is the *abstract* release→acquire instance (SM2.A primitives), with the
-- correspondence to the concrete `wakeThread` written out in the docstrings.  The
-- full SystemState↔MemoryTrace *refinement* (mapping every `enqueueRunnableOnCore`
-- / `ffiSendSgi` to a trace event and proving the wake's runtime emits exactly
-- this trace) is a large new modeling surface that belongs with the cross-core
-- IPC / TLB-shootdown phase (SM6/SM7), where multiple cross-core protocols share
-- the bridge; it is deliberately *not* built here.  What §11 delivers is the
-- formal statement, in the verified memory model, that the wake's release/acquire
-- pair is genuinely a happens-before edge — closing the "ordering asserted only
-- in prose" gap with a machine-checked theorem.

-- These memory-model constructs live in `SeLe4n.Kernel.Concurrency` (with
-- `MemoryEvent` / `MemoryTrace` / `synchronizesWith`).  The file's outer
-- `namespace SeLe4n.Kernel` is still open here, so the relative `namespace
-- Concurrency` resolves to `SeLe4n.Kernel.Concurrency` (not a doubly-nested one).
namespace Concurrency

/-- WS-SM SM5.C.4 (memory-model): the executing core's **release-store** event of
a cross-core wake — publishing the run-queue insertion to the shared
run-queue-state location `loc` with the released token `v`, under `release`
order.  Corresponds to the `enqueueRunnableOnCore` write made visible by the
`dsb ish` that `ffi_send_sgi` emits *before* writing `GICD_SGIR` (SM1.F.8). -/
def wakeReleaseEvent (execCore : CoreId) (loc : AtomicLocation) (v : Nat) : MemoryEvent :=
  ⟨execCore, loc, true, .release, v, 0⟩

/-- WS-SM SM5.C.4 (memory-model): the target core's **acquire-load** event of a
cross-core wake — observing the published run-queue-state token `v` at `loc`
under `acquire` order.  Corresponds to the target core taking the `.reschedule`
SGI (the GIC delivery is the acquire that observes the executing core's release),
after which `handleRescheduleSgiOnCore` re-runs the scheduler and sees the woken
thread in its run queue. -/
def wakeAcquireEvent (tgtCore : CoreId) (loc : AtomicLocation) (v : Nat) : MemoryEvent :=
  ⟨tgtCore, loc, false, .acquire, v, 0⟩

/-- WS-SM SM5.C.4 (memory-model): the two-event trace of a cross-core wake's
ordering — the executing core's release-store followed by the target core's
acquire-load, in execution order. -/
def wakeOrderingTrace (execCore tgtCore : CoreId) (loc : AtomicLocation) (v : Nat) :
    MemoryTrace :=
  (MemoryTrace.empty.append (wakeReleaseEvent execCore loc v)).append
    (wakeAcquireEvent tgtCore loc v)

/-- WS-SM SM5.C.4: the release event and the acquire event are distinct — they
disagree on `isWrite` (store vs load).  Needed so they occupy distinct trace
positions. -/
theorem wakeReleaseEvent_ne_acquireEvent (execCore tgtCore : CoreId)
    (loc : AtomicLocation) (v : Nat) :
    wakeReleaseEvent execCore loc v ≠ wakeAcquireEvent tgtCore loc v := by
  intro h
  have hw : (wakeReleaseEvent execCore loc v).isWrite
      = (wakeAcquireEvent tgtCore loc v).isWrite := by rw [h]
  simp [wakeReleaseEvent, wakeAcquireEvent] at hw

/-- WS-SM SM5.C.4: the wake's ordering trace is well-formed (`Nodup` + per-core
seqNum monotonicity), provided the executing and target cores are distinct (a
cross-core wake).  Both events sit at `seqNum 0` but on *different* cores, so the
per-core monotonicity is vacuous; distinctness gives `Nodup`. -/
theorem wakeOrderingTrace_wellFormed (execCore tgtCore : CoreId)
    (loc : AtomicLocation) (v : Nat) (hcores : execCore ≠ tgtCore) :
    (wakeOrderingTrace execCore tgtCore loc v).wellFormed := by
  have hne := wakeReleaseEvent_ne_acquireEvent execCore tgtCore loc v
  have ht : (wakeOrderingTrace execCore tgtCore loc v).events
      = [wakeReleaseEvent execCore loc v, wakeAcquireEvent tgtCore loc v] := by
    simp [wakeOrderingTrace, MemoryTrace.append, MemoryTrace.empty]
  unfold MemoryTrace.wellFormed
  rw [ht]
  refine ⟨?_, ?_⟩
  · simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_iff,
      List.nodup_nil, and_true]
    exact hne
  · rw [List.pairwise_cons]
    refine ⟨?_, by simp⟩
    intro e he
    rw [List.mem_singleton] at he
    rw [he]
    intro hcoreEq
    exact absurd hcoreEq hcores

/-- WS-SM SM5.C.4 (the core ordering result): the executing core's release-store
**synchronizes-with** the target core's acquire-load in the wake's ordering trace
— a release store of a value paired with an acquire load that observes the same
value at the same location, in trace order.  This is the ARM ARM B2.3.7
release/acquire synchronisation that the `dsb ish`-before-`GICD_SGIR` discipline
(SM1.F.8) establishes for the wake. -/
theorem wakeOrdering_synchronizesWith (execCore tgtCore : CoreId)
    (loc : AtomicLocation) (v : Nat) :
    synchronizesWith (wakeOrderingTrace execCore tgtCore loc v)
      (wakeReleaseEvent execCore loc v) (wakeAcquireEvent tgtCore loc v) := by
  have hne := wakeReleaseEvent_ne_acquireEvent execCore tgtCore loc v
  have ht : (wakeOrderingTrace execCore tgtCore loc v).events
      = [wakeReleaseEvent execCore loc v, wakeAcquireEvent tgtCore loc v] := by
    simp [wakeOrderingTrace, MemoryTrace.append, MemoryTrace.empty]
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · rw [ht]; simp
  · rw [ht]; simp
  · show (wakeOrderingTrace execCore tgtCore loc v).eventPos _
        < (wakeOrderingTrace execCore tgtCore loc v).eventPos _
    unfold MemoryTrace.eventPos
    rw [ht]
    have hbeq_ab : (wakeReleaseEvent execCore loc v == wakeAcquireEvent tgtCore loc v) = false := by
      rw [beq_eq_false_iff_ne]; exact hne
    simp only [List.idxOf_cons, beq_self_eq_true, hbeq_ab, cond_true, cond_false]
    omega

/-- WS-SM SM5.C.4 (the headline ordering theorem): the run-queue publication
**happens-before** the target core observes it on the SGI.  Lifts the
synchronizes-with edge to happens-before (SM2.A `synchronizesWith_implies_happensBefore`).

This is the machine-checked statement of the wake's BKL-discipline ordering: in
the verified operational memory model, the executing core's release of the
run-queue state happens-before the target core's acquire of it — so when the
target services the `.reschedule` SGI and re-runs its scheduler
(`handleRescheduleSgiOnCore`), the woken thread is *guaranteed visible* in its run
queue.  The prose "emit the SGI after the state write is visible" is now a
theorem, not a comment. -/
theorem wakeOrdering_happensBefore (execCore tgtCore : CoreId)
    (loc : AtomicLocation) (v : Nat) :
    happensBefore (wakeOrderingTrace execCore tgtCore loc v)
      (wakeReleaseEvent execCore loc v) (wakeAcquireEvent tgtCore loc v) :=
  synchronizesWith_implies_happensBefore _
    (wakeOrdering_synchronizesWith execCore tgtCore loc v)

end Concurrency

end SeLe4n.Kernel
