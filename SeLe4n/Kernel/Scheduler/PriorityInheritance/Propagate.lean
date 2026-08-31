-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.PriorityInheritance.Compute

namespace SeLe4n.Kernel.PriorityInheritance

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (bootCoreId CoreId SgiKind)

-- ============================================================================
-- D4-G: updatePipBoost (single-thread priority update)
-- ============================================================================

/-- D4-G / AN5-C: Update the `pipBoost` field for a single thread based on
its current waiters. If the thread has higher-priority waiters than its
base priority, sets `pipBoost` to the maximum waiter priority. Otherwise
clears it.

If the thread is in the run queue and effective priority changed,
performs remove-then-insert for bucket migration (D2-E pattern).

**Lifecycle relationship (AN5-C)**:
* `propagatePriorityInheritance` — top-level "forward" entry point
  that walks a blocking chain from `startTid` and invokes
  `updatePipBoost` on each server in the chain (up to fuel).
* `revertPriorityInheritance` — symmetric "cleanup" path that clears
  `pipBoost` when the blocking chain dissolves (IPC reply, timeout).
  Invokes `updatePipBoost` to reset each server's boost after the
  waiter exits the chain.
* `updatePipBoost` (this function) — idempotent single-thread update.
  `propagate` / `revert` compose it across the chain. Frame lemmas
  in `PriorityInheritance/Preservation.lean` (D4-O family) establish
  which fields it preserves (current, services, activeDomain, etc.),
  and the NI-preservation theorem
  `updatePipBoost_preserves_projection` in
  `InformationFlow/Invariant/Operations.lean` discharges cross-domain
  information-flow safety. -/
def updatePipBoost (st : SystemState) (tid : ThreadId) : SystemState :=
  match st.objects[tid.toObjId]? with
  | some (KernelObject.tcb tcb) =>
    let newBoost := computeMaxWaiterPriority st tid
    -- Only update if pipBoost actually changed
    if tcb.pipBoost == newBoost then st
    else
      -- Update TCB with new pipBoost
      let tcb' := { tcb with pipBoost := newBoost }
      let st' := { st with objects := st.objects.insert tid.toObjId (KernelObject.tcb tcb') }
      -- Conditional run queue bucket migration
      if tid ∈ (st.scheduler.runQueueOnCore bootCoreId) then
        let oldPrio := (resolveEffectivePrioDeadline st tcb).1
        let newPrio := (resolveEffectivePrioDeadline st' tcb').1
        if oldPrio != newPrio then
          { st' with
            scheduler := st'.scheduler.setRunQueueOnCore bootCoreId
              (((st'.scheduler.runQueueOnCore bootCoreId).remove tid).insert tid newPrio)
          }
        else st'
      else st'
  | _ => st

-- ============================================================================
-- D4-H: propagatePriorityInheritance (chain walk)
-- ============================================================================

/-- D4-H: Walk the blocking chain upward from `startTid`, applying
`updatePipBoost` at each step. If the thread is itself blocked on
another server via Reply, continues propagation upward.

Terminates when fuel exhausted, thread not blocked, or no server found.
Default fuel = objectIndex.length (sufficient by D4-E). -/
def propagatePriorityInheritance (st : SystemState) (startTid : ThreadId)
    (fuel : Nat := st.objectIndex.length) : SystemState :=
  match fuel with
  | 0 => st
  | fuel' + 1 =>
    -- Apply updatePipBoost to the current thread
    let st' := updatePipBoost st startTid
    -- AF1-J: Reads `blockingServer` from pre-mutation state `st`, not post-
    -- `updatePipBoost` state `st'`. Sound because `updatePipBoost` only modifies
    -- `pipBoost` (never `ipcState`), so the blocking graph topology is unchanged.
    -- See AE3-I/S-01 frame theorems.
    match blockingServer st startTid with
    | some nextServer =>
      -- Propagate upward through the chain
      propagatePriorityInheritance st' nextServer fuel'
    | none => st'

-- ============================================================================
-- D4-I: revertPriorityInheritance (chain reversion)
-- ============================================================================

/-- D4-I: Revert priority inheritance for `tid` and its blocking chain.
Called when a client is unblocked (Reply completes) — recomputes `pipBoost`
for `tid` based on remaining waiters, then propagates upward.

Structurally identical to propagation: the `updatePipBoost` function
uniformly handles both boost and reversion because it always recomputes
from the current `waitersOf`. -/
def revertPriorityInheritance (st : SystemState) (tid : ThreadId)
    (fuel : Nat := st.objectIndex.length) : SystemState :=
  match fuel with
  | 0 => st
  | fuel' + 1 =>
    let st' := updatePipBoost st tid
    -- AF1-J: Same pre-mutation read pattern as propagatePriorityInheritance.
    match blockingServer st tid with
    | some nextServer =>
      revertPriorityInheritance st' nextServer fuel'
    | none => st'

-- ============================================================================
-- D4-J: Propagation correctness
-- ============================================================================

/-- D4-J: Propagation with zero fuel is identity. -/
theorem propagate_zero (st : SystemState) (tid : ThreadId) :
    propagatePriorityInheritance st tid 0 = st := by
  rfl

/-- D4-J: Propagation with nonzero fuel applies updatePipBoost first. -/
theorem propagate_step (st : SystemState) (tid : ThreadId) (n : Nat) :
    propagatePriorityInheritance st tid (n + 1) =
      match blockingServer st tid with
      | some nextServer => propagatePriorityInheritance (updatePipBoost st tid) nextServer n
      | none => updatePipBoost st tid := by
  rfl

-- ============================================================================
-- D4-K: Reversion correctness
-- ============================================================================

/-- D4-K: Reversion is functionally identical to propagation on the
current state. Both compute from current `waitersOf`. -/
theorem revert_eq_propagate (st : SystemState) (tid : ThreadId)
    (fuel : Nat) :
    revertPriorityInheritance st tid fuel =
    propagatePriorityInheritance st tid fuel := by
  induction fuel generalizing st tid with
  | zero => simp [revertPriorityInheritance, propagatePriorityInheritance]
  | succ n ih =>
    simp only [revertPriorityInheritance, propagatePriorityInheritance]
    split
    · exact ih ..
    · rfl

-- ============================================================================
-- AE3-I/S-01: Frame theorem — updatePipBoost preserves ipcState
-- ============================================================================

/-- AE3-I/S-01: `updatePipBoost` only modifies `pipBoost` (and optionally the
scheduler's RunQueue) — it never touches `ipcState` on any TCB. This makes it
safe for `propagatePriorityInheritance` to read `blockingServer` from the
pre-mutation state: the blocking graph (which depends on `ipcState`) is
unchanged by PIP boost updates.

`updatePipBoost` has three code paths:
1. TCB not found or not-TCB → state unchanged (trivial)
2. `pipBoost` already equals `newBoost` → state unchanged (trivial)
3. `pipBoost` changed → record-with update only sets `pipBoost`,
   then optionally migrates RunQueue bucket (scheduler-only, no objects change
   beyond the `pipBoost` update at `tid.toObjId`)

In all paths, `blockingServer` reads `ipcState` which is untouched. -/
theorem updatePipBoost_ipcState_frame (st : SystemState) (tid : ThreadId)
    (hObjInv : st.objects.invExt)
    (t : ThreadId) (hNe : t ≠ tid) :
    (updatePipBoost st tid).objects[t.toObjId]? = st.objects[t.toObjId]? := by
  unfold updatePipBoost
  split
  case h_1 tcb _ =>
      simp only []
      split
      · rfl
      · -- pipBoost changed → objects insert at tid.toObjId
        have hObjNe : ¬(tid.toObjId == t.toObjId) = true := by
          intro h; apply hNe
          exact (ThreadId.toObjId_injective tid t (eq_of_beq h)).symm
        -- After insert at tid.toObjId, lookup at t.toObjId is unchanged
        split
        · -- In run queue
          split
          · -- Priority changed → scheduler updated, objects have insert
            show (st.objects.insert tid.toObjId _).get? t.toObjId = _
            exact RHTable_get?_insert_ne st.objects tid.toObjId t.toObjId _ hObjNe hObjInv
          · -- Priority unchanged → same objects with insert
            exact RHTable_get?_insert_ne st.objects tid.toObjId t.toObjId _ hObjNe hObjInv
        · -- Not in run queue → same objects with insert
          exact RHTable_get?_insert_ne st.objects tid.toObjId t.toObjId _ hObjNe hObjInv
  case h_2 => rfl

/-- AE3-I/S-01: For the target thread itself, `updatePipBoost` only modifies
`pipBoost`. The `ipcState` field is definitionally preserved by the
`{ tcb with pipBoost := newBoost }` record-with update. -/
theorem updatePipBoost_self_ipcState (st : SystemState) (tid : ThreadId)
    (hObjInv : st.objects.invExt) (tcb : TCB)
    (hObj : st.objects[tid.toObjId]? = some (.tcb tcb)) :
    match (updatePipBoost st tid).objects[tid.toObjId]? with
    | some (.tcb tcb') => tcb'.ipcState = tcb.ipcState
    | _ => True := by
  -- Factor: if we know the lookup gives a TCB with preserved ipcState, the match resolves
  suffices h : ∃ tcb', (updatePipBoost st tid).objects[tid.toObjId]? = some (.tcb tcb') ∧
      tcb'.ipcState = tcb.ipcState by
    obtain ⟨tcb', hLook, hIpc⟩ := h; simp only [hLook, hIpc]
  -- Now prove the lookup gives such a TCB
  unfold updatePipBoost
  simp only [hObj]
  split
  · -- pipBoost unchanged → state is st, lookup is hObj
    exact ⟨tcb, hObj, rfl⟩
  · -- pipBoost changed → lookup gives { tcb with pipBoost := ... }
    have hSelf : (st.objects.insert tid.toObjId
        (.tcb { tcb with pipBoost := computeMaxWaiterPriority st tid }))[tid.toObjId]? =
        some (.tcb { tcb with pipBoost := computeMaxWaiterPriority st tid }) :=
      RHTable_get?_insert_self st.objects tid.toObjId _ hObjInv
    refine ⟨{ tcb with pipBoost := computeMaxWaiterPriority st tid }, ?_, rfl⟩
    -- All scheduler branches have .objects = st.objects.insert ..., so hSelf applies
    by_cases hRQ : tid ∈ (st.scheduler.runQueueOnCore bootCoreId)
    · simp only [hRQ, ite_true]; split <;> exact hSelf
    · simp only [hRQ, ite_false]; exact hSelf

/-- AE3-I/S-01: `updatePipBoost` preserves `blockingServer` for all threads.
This is the main frame theorem: the blocking graph is invariant under PIP
boost updates. `propagatePriorityInheritance` reads `blockingServer` from
the pre-mutation state, and this theorem justifies that the result would be
identical on the post-mutation state.

For `t ≠ tid`: objects[t] is unchanged (`updatePipBoost_ipcState_frame`).
For `t = tid`: `ipcState` is preserved by the record-with update
(`updatePipBoost_self_ipcState`). Since `blockingServer` reads only
`ipcState`, the result is identical in both cases. -/
-- Helper: blockingServer depends only on objects[t.toObjId]?
-- (WS-SM SM5.F: de-privatised so the per-core PIP module can reuse it.)
theorem blockingServer_congr_objects (st₁ st₂ : SystemState) (t : ThreadId)
    (h : st₁.objects[t.toObjId]? = st₂.objects[t.toObjId]?) :
    blockingServer st₁ t = blockingServer st₂ t := by
  simp only [blockingServer, h]

-- Helper: blockingServer is determined by the ipcState of the looked-up TCB
-- (WS-SM SM5.F: de-privatised so the per-core PIP module can reuse it.)
theorem blockingServer_ipcState_congr (st₁ st₂ : SystemState) (t : ThreadId)
    (tcb₁ tcb₂ : TCB) (h₁ : st₁.objects[t.toObjId]? = some (.tcb tcb₁))
    (h₂ : st₂.objects[t.toObjId]? = some (.tcb tcb₂))
    (hIpc : tcb₁.ipcState = tcb₂.ipcState) :
    blockingServer st₁ t = blockingServer st₂ t := by
  simp only [blockingServer, h₁, h₂, hIpc]

theorem updatePipBoost_preserves_blockingServer (st : SystemState) (tid : ThreadId)
    (hObjInv : st.objects.invExt) (t : ThreadId) :
    blockingServer (updatePipBoost st tid) t = blockingServer st t := by
  by_cases hEq : t = tid
  · -- t = tid: ipcState preserved by { tcb with pipBoost := ... }
    rw [hEq]
    unfold updatePipBoost
    cases hTid : st.objects[tid.toObjId]? with
    | none => rfl
    | some obj =>
      cases obj with
      | tcb tcb =>
        simp only []
        split
        · rfl -- pipBoost unchanged
        · -- pipBoost changed: blockingServer reads only ipcState, which is
          -- unchanged by { tcb with pipBoost := ... }. Use ipcState congr lemma.
          refine blockingServer_ipcState_congr _ _ _
            { tcb with pipBoost := computeMaxWaiterPriority st tid } tcb ?_ hTid rfl
          -- Remaining goal: <result-state>.objects[tid.toObjId]? = some (.tcb { tcb with pipBoost := ... })
          -- All scheduler branches have .objects = st.objects.insert ..., so hSelf applies.
          have hSelf : (st.objects.insert tid.toObjId
              (.tcb { tcb with pipBoost := computeMaxWaiterPriority st tid }))[tid.toObjId]? =
              some (.tcb { tcb with pipBoost := computeMaxWaiterPriority st tid }) :=
            RHTable_get?_insert_self st.objects tid.toObjId _ hObjInv
          by_cases hRQ : tid ∈ (st.scheduler.runQueueOnCore bootCoreId)
          · simp only [hRQ, ite_true]; split <;> exact hSelf
          · simp only [hRQ, ite_false]; exact hSelf
      | _ => rfl
  · exact blockingServer_congr_objects _ _ _ (updatePipBoost_ipcState_frame st tid hObjInv t hEq)

-- ============================================================================
-- WS-SM SM5.F.2 / SM5.F.4: per-core priority-inheritance transitions
-- ============================================================================
--
-- Under SMP the boosted holder may live on a core *other* than the one running
-- the IPC operation, so two things become per-core: (1) the run-queue *bucket
-- migration* must happen on the holder's home core (not always `bootCoreId`),
-- and (2) if that core is remote, its scheduler must be poked with a
-- `.reschedule` SGI (the boosted holder may now outrank the remote core's
-- current thread).  The boost *value* stays GLOBAL — `computeMaxWaiterPriority`
-- (the max over ALL waiters regardless of core); using only a per-core slice
-- would under-boost and re-introduce priority inversion.  `updatePipBoostOnCore`
-- is therefore `updatePipBoost` with the bucket migration generalised from
-- `bootCoreId` to an explicit home core `c`; the single-core form is recovered
-- at `c = bootCoreId` (`updatePipBoost_eq_updatePipBoostOnCore_bootCore`, an
-- `rfl`, proved in the staged `PriorityInheritance.PerCore`).

/-- WS-SM SM5.F.2 (plan §3.6): per-core single-thread PIP boost update.

Identical to `updatePipBoost` except the run-queue *bucket migration* targets
the holder's home core `c` instead of `bootCoreId`.  The boost VALUE is the
GLOBAL `computeMaxWaiterPriority st tid` (max over every waiter, cross-core) —
the per-core parameter only controls *where* the bucket is re-positioned, never
the magnitude of the boost (under-boosting would reintroduce inversion).

`updatePipBoost st tid = updatePipBoostOnCore st bootCoreId tid` definitionally
(the only change is the literal core), so the existing single-core PIP proof base
is preserved verbatim and the per-core form generalises it. -/
def updatePipBoostOnCore (st : SystemState) (c : CoreId) (tid : ThreadId) : SystemState :=
  match st.objects[tid.toObjId]? with
  | some (KernelObject.tcb tcb) =>
    let newBoost := computeMaxWaiterPriority st tid
    -- Only update if pipBoost actually changed
    if tcb.pipBoost == newBoost then st
    else
      -- Update TCB with new (GLOBAL) pipBoost
      let tcb' := { tcb with pipBoost := newBoost }
      let st' := { st with objects := st.objects.insert tid.toObjId (KernelObject.tcb tcb') }
      -- Conditional run-queue bucket migration ON CORE c (the holder's home core)
      if tid ∈ (st.scheduler.runQueueOnCore c) then
        let oldPrio := (resolveEffectivePrioDeadline st tcb).1
        let newPrio := (resolveEffectivePrioDeadline st' tcb').1
        if oldPrio != newPrio then
          { st' with
            scheduler := st'.scheduler.setRunQueueOnCore c
              (((st'.scheduler.runQueueOnCore c).remove tid).insert tid newPrio)
          }
        else st'
      else st'
  | _ => st

/-- WS-RR RR2.6: `updatePipBoostOnCore` rewrites the boosted thread's TCB in
`pipBoost` **and nothing else** — including on the no-op arm, where the boost it
would write is the one already there.

Stated as "some `pipBoost`" rather than naming `computeMaxWaiterPriority` because
that is what the *readers* need: every conjunct of the IPC bundle reads fields
this update leaves alone, so the boost's value is irrelevant to them and naming
it would force each reader to case-split on the no-op arm. -/
theorem updatePipBoostOnCore_objects_at (st : SystemState) (c : CoreId) (tid : ThreadId)
    (tcb : TCB) (hTcb : st.getTcb? tid = some tcb)
    (hInv : st.objects.invExt) :
    ∃ p, (updatePipBoostOnCore st c tid).getTcb? tid
      = some { tcb with pipBoost := p } := by
  have hIns : ∀ t : KernelObject,
      (st.objects.insert tid.toObjId t).get? tid.toObjId = some t := fun t =>
    SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId t hInv
  simp only [SystemState.getTcb?_eq_some_iff]
  simp only [updatePipBoostOnCore, (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb]
  split
  · exact ⟨tcb.pipBoost, (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb⟩
  · split
    · split
      · exact ⟨computeMaxWaiterPriority st tid, hIns _⟩
      · exact ⟨computeMaxWaiterPriority st tid, hIns _⟩
    · exact ⟨computeMaxWaiterPriority st tid, hIns _⟩

/-- WS-RR RR2.6: `updatePipBoostOnCore` leaves every thread's run-queue
*membership* unchanged on every core.  Its bucket migration removes the boosted
thread and re-inserts it at the new effective priority — a re-keying, not a
deschedule — and fires only under the guard that the thread is already in that
queue. -/
theorem updatePipBoostOnCore_mem_runQueueOnCore (st : SystemState) (c c' : CoreId)
    (tid x : ThreadId) :
    x ∈ (updatePipBoostOnCore st c tid).scheduler.runQueueOnCore c'
      ↔ x ∈ st.scheduler.runQueueOnCore c' := by
  simp only [updatePipBoostOnCore]
  split
  · split
    · exact Iff.rfl
    · split
      · rename_i hIn
        split
        · by_cases hcc : c = c'
          · subst hcc
            rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
            rw [RunQueue.mem_insert, RunQueue.mem_remove]
            constructor
            · rintro (⟨hx, _⟩ | hxt)
              · exact hx
              · exact hxt ▸ hIn
            · intro hx
              by_cases hEq : x = tid
              · exact Or.inr hEq
              · exact Or.inl ⟨hx, hEq⟩
          · rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ c c' _ hcc]
        · exact Iff.rfl
      · exact Iff.rfl
  · exact Iff.rfl

/-- WS-SM SM5.F.2 (plan §3.6): cross-core PIP boost with wake.

Boost `tid` on its home core (`determineTargetCore`), then decide whether the
home core needs a cross-core `.reschedule` SGI:

* **local** (home = `executingCore`): no SGI — the executing core will pick up
  the re-bucketed holder on its next scheduling decision.
* **remote, not runnable on home** (the holder is not in its home core's run
  queue — it is itself blocked deeper in the chain, or currently running): no
  SGI.  Raising the `pipBoost` of a thread that is not competing for its home
  core's CPU has no immediate scheduling consequence — the new boost is consumed
  when the thread next becomes runnable there (via the wake that re-enqueues it,
  SM5.C `wakeThread` / SM5.F `restoreToReadyWithWake`).  Poking the home core now
  would be a spurious cross-core IPI (SM5.C.11 latency / WS-SM SM5.F.4 C9).
* **remote, runnable on home, material**: the boost changed the holder's
  *effective* run-queue bucket (`resolveEffectivePrioDeadline` rose) AND the holder is runnable on
  its home core, so that core's scheduler must re-evaluate — the boosted holder
  may now outrank that core's current thread.  Emit `(home, .reschedule)`.
* **remote, no-op** (boost unchanged ⇒ `updatePipBoostOnCore` returned `st`): no
  SGI — there is no scheduling consequence, so poking the remote core would be a
  spurious cross-core IPI.

The runnability gate `tid ∈ runQueueOnCore target` AND the effective-priority
materiality gate together align the SGI exactly with the run-queue *bucket
migration* in `updatePipBoostOnCore` (which is gated on the same membership AND the
same `oldPrio != newPrio` effective-priority change): an SGI is emitted only when
the boost actually migrates the holder's bucket, i.e. could change which thread the
home core should run next.

Mirrors `wakeThread` (state + optional SGI; the BaseIO form that fires the SGI
over the FFI is SM5.I's runtime dispatch).  The materiality guard reads the
holder's *effective* priority (`resolveEffectivePrioDeadline`) before/after,
exactly tracking the bucket-migration condition. -/
def pipBoostWithWake (st : SystemState) (tid : ThreadId) (executingCore : CoreId)
    : SystemState × Option (CoreId × SgiKind) :=
  let target := determineTargetCore st tid
  let st' := updatePipBoostOnCore st target tid
  let sgi : Option (CoreId × SgiKind) :=
    if target == executingCore then none
    else if tid ∈ (st.scheduler.runQueueOnCore target) then
      match st.getTcb? tid, st'.getTcb? tid with
      | some t, some t' =>
        -- Gate on the *effective* priority (the run-queue bucket key) changing,
        -- not the raw `pipBoost` — exactly the `oldPrio != newPrio` condition that
        -- governs the run-queue bucket migration in `updatePipBoostOnCore`.  A
        -- `pipBoost` rise that does not raise the effective priority (e.g. a holder
        -- whose base priority already dominates the new boost) migrates no bucket
        -- and has no scheduling consequence on the home core, so it must poke no
        -- remote core (a spurious cross-core IPI otherwise).
        if (resolveEffectivePrioDeadline st t).1 == (resolveEffectivePrioDeadline st' t').1
        then none else some (target, SgiKind.reschedule)
      | _, _ => none
    else none
  (st', sgi)

/-- WS-SM SM5.F.4 (plan §3.6, "donation chain across cores"): walk the blocking
chain upward from `startTid`, boosting each holder on **its own** home core and
collecting the cross-core `.reschedule` SGIs for the holders that live on a
remote core.

The blocking chain can cross cores (a client on core 0 blocked on a server on
core 1 blocked on a server on core 2); each link is boosted on its own home core
via `pipBoostWithWake`, and the SGIs accumulate so the runtime dispatch (SM5.I)
fires one `.reschedule` per distinct remote core touched.  As in
`propagatePriorityInheritance`, `blockingServer` is read from the *pre-mutation*
state (boost updates never touch `ipcState`, so the chain topology is fixed —
AF1-J).  Functionally identical for propagation and reversion (both recompute
from current `waitersOf`), matching `revert_eq_propagate`. -/
def propagatePipChainCrossCore (st : SystemState) (startTid : ThreadId)
    (executingCore : CoreId) (fuel : Nat := st.objectIndex.length)
    : SystemState × List (CoreId × SgiKind) :=
  match fuel with
  | 0 => (st, [])
  | fuel' + 1 =>
    let res := pipBoostWithWake st startTid executingCore
    let here : List (CoreId × SgiKind) := match res.2 with | some s => [s] | none => []
    match blockingServer st startTid with
    | some nextServer =>
      let tailRes := propagatePipChainCrossCore res.1 nextServer executingCore fuel'
      (tailRes.1, here ++ tailRes.2)
    | none => (res.1, here)

/-- WS-SM SM5.F.4: cross-core chain walk with zero fuel is identity (no boost, no SGI). -/
theorem propagatePipChainCrossCore_zero (st : SystemState) (tid : ThreadId) (ec : CoreId) :
    propagatePipChainCrossCore st tid ec 0 = (st, []) := rfl

/-- WS-SM SM5.F.4: one chain-walk step unfolding. -/
theorem propagatePipChainCrossCore_step (st : SystemState) (tid : ThreadId) (ec : CoreId)
    (n : Nat) :
    propagatePipChainCrossCore st tid ec (n + 1) =
      let res := pipBoostWithWake st tid ec
      let here : List (CoreId × SgiKind) := match res.2 with | some s => [s] | none => []
      match blockingServer st tid with
      | some nextServer =>
        let tailRes := propagatePipChainCrossCore res.1 nextServer ec n
        (tailRes.1, here ++ tailRes.2)
      | none => (res.1, here) := rfl

/-- WS-SM SM5.F.2: `updatePipBoostOnCore` preserves the object-store invariant —
the only object write is the holder's `pipBoost` `insert` (the per-core bucket
migration touches only the scheduler). -/
theorem updatePipBoostOnCore_preserves_objects_invExt (st : SystemState) (c : CoreId)
    (tid : ThreadId) (hInv : st.objects.invExt) :
    (updatePipBoostOnCore st c tid).objects.invExt := by
  simp only [updatePipBoostOnCore]
  split
  · rename_i tcb _
    split
    · exact hInv
    · split
      · split
        · exact RHTable_insert_preserves_invExt st.objects tid.toObjId _ hInv
        · exact RHTable_insert_preserves_invExt st.objects tid.toObjId _ hInv
      · exact RHTable_insert_preserves_invExt st.objects tid.toObjId _ hInv
  · exact hInv

/-- WS-SM SM5.F.2: `updatePipBoostOnCore` does not change `objects[oid]?` for any
`oid ≠ tid.toObjId`. -/
theorem updatePipBoostOnCore_objects_ne (st : SystemState) (c : CoreId) (tid : ThreadId)
    (oid : ObjId) (hNe : ¬(tid.toObjId == oid) = true) (hInv : st.objects.invExt) :
    (updatePipBoostOnCore st c tid).objects[oid]? = st.objects[oid]? := by
  simp only [updatePipBoostOnCore]
  split
  · split
    · rfl
    · split
      · split
        · show (st.objects.insert tid.toObjId _)[oid]? = _
          exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne st.objects tid.toObjId oid _ hNe hInv
        · exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne st.objects tid.toObjId oid _ hNe hInv
      · exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne st.objects tid.toObjId oid _ hNe hInv
  · rfl

/-- WS-SM SM5.F.2: `updatePipBoostOnCore` never writes any core's `current` slot. -/
theorem updatePipBoostOnCore_currentOnCore (st : SystemState) (c c' : CoreId)
    (tid : ThreadId) :
    (updatePipBoostOnCore st c tid).scheduler.currentOnCore c'
      = st.scheduler.currentOnCore c' := by
  simp only [updatePipBoostOnCore]
  split
  · rename_i tcb _
    split
    · rfl
    · split
      · split <;> rfl
      · rfl
  · rfl

/-- WS-SM SM5.F.2: `pipBoostWithWake`'s state component is the per-core boost on the
holder's home core. -/
@[simp] theorem pipBoostWithWake_state (st : SystemState) (tid : ThreadId) (ec : CoreId) :
    (pipBoostWithWake st tid ec).1 = updatePipBoostOnCore st (determineTargetCore st tid) tid := rfl

/-- WS-SM SM5.F.2: `pipBoostWithWake` preserves the object-store invariant. -/
theorem pipBoostWithWake_preserves_objects_invExt (st : SystemState) (tid : ThreadId)
    (ec : CoreId) (hInv : st.objects.invExt) :
    (pipBoostWithWake st tid ec).1.objects.invExt := by
  rw [pipBoostWithWake_state]
  exact updatePipBoostOnCore_preserves_objects_invExt st _ tid hInv

/-- WS-SM SM5.F.2: a PIP boost of a thread with no TCB is the identity — the def's
fallthrough arm returns `st`. -/
theorem updatePipBoostOnCore_eq_self_of_getTcb?_none (st : SystemState) (c : CoreId)
    (tid : ThreadId) (hNone : st.getTcb? tid = none) :
    updatePipBoostOnCore st c tid = st := by
  unfold updatePipBoostOnCore
  unfold SystemState.getTcb? at hNone
  split
  · rename_i tcb hMatch; rw [hMatch] at hNone; simp at hNone
  · rfl

/-- WS-SM SM5.F.4: the cross-core donation chain walk preserves the object-store
invariant — each link is a `pipBoostWithWake` boost (an `invExt`-preserving TCB
`insert`), folded along the chain.

(WS-RR RR2.17: moved here from the per-core layer, which sits above `Kernel.API`
in the import graph and so cannot be read by the cancellation surface that needs
it.  The induction runs on `propagatePipChainCrossCore_step` directly.) -/
theorem propagatePipChainCrossCore_preserves_objects_invExt (st : SystemState)
    (tid : ThreadId) (ec : CoreId) (fuel : Nat) (hInv : st.objects.invExt) :
    (propagatePipChainCrossCore st tid ec fuel).1.objects.invExt := by
  induction fuel generalizing st tid with
  | zero => rw [propagatePipChainCrossCore_zero]; exact hInv
  | succ n ih =>
    rw [propagatePipChainCrossCore_step]
    have hNext := pipBoostWithWake_preserves_objects_invExt st tid ec hInv
    cases blockingServer st tid with
    | none => exact hNext
    | some nextServer => exact ih _ nextServer hNext

/-- WS-RR RR2.17: `updatePipBoostOnCore`'s only object write stores a `.tcb`,
so every notification the post-state holds was already there.  This is the shape
`ipcInvariant` reads (it quantifies over notifications and nothing else), and it
is what lets the suspend path's priority-inheritance stage carry the invariant
without importing the IPC layer into the scheduler. -/
theorem updatePipBoostOnCore_notification_backward (st : SystemState) (c : CoreId)
    (tid : ThreadId) (hInv : st.objects.invExt)
    (oid : ObjId) (ntfn : Notification)
    (h : (updatePipBoostOnCore st c tid).objects[oid]? = some (.notification ntfn)) :
    st.objects[oid]? = some (.notification ntfn) := by
  cases hAt : st.objects[tid.toObjId]? with
  | none =>
      rw [updatePipBoostOnCore_eq_self_of_getTcb?_none st c tid
        (by unfold SystemState.getTcb?; rw [hAt])] at h
      exact h
  | some obj =>
    cases obj with
    | tcb tcb =>
        obtain ⟨p, hPost⟩ := updatePipBoostOnCore_objects_at st c tid tcb
          (by rw [SystemState.getTcb?_eq_some_iff]; exact hAt) hInv
        have hPostRaw := (SystemState.getTcb?_eq_some_iff _ tid _).mp hPost
        by_cases hEq : oid = tid.toObjId
        · rw [hEq, hPostRaw] at h; cases h
        · rw [updatePipBoostOnCore_objects_ne st c tid oid
            (by simpa using fun e => hEq e.symm) hInv] at h
          exact h
    | _ =>
        rw [updatePipBoostOnCore_eq_self_of_getTcb?_none st c tid
          (by unfold SystemState.getTcb?; rw [hAt])] at h
        exact h

/-- WS-RR RR2.17: the cross-core boost-with-wake inherits the frame — its state
component is `updatePipBoostOnCore` on the thread's home core. -/
theorem pipBoostWithWake_notification_backward (st : SystemState) (tid : ThreadId)
    (ec : CoreId) (hInv : st.objects.invExt) (oid : ObjId) (ntfn : Notification)
    (h : (pipBoostWithWake st tid ec).1.objects[oid]? = some (.notification ntfn)) :
    st.objects[oid]? = some (.notification ntfn) :=
  updatePipBoostOnCore_notification_backward st (determineTargetCore st tid) tid hInv oid ntfn h

/-- WS-RR RR2.17: the whole chain walk inherits it, by induction on the fuel. -/
theorem propagatePipChainCrossCore_notification_backward (st : SystemState) (tid : ThreadId)
    (ec : CoreId) (fuel : Nat) (hInv : st.objects.invExt) (oid : ObjId) (ntfn : Notification)
    (h : (propagatePipChainCrossCore st tid ec fuel).1.objects[oid]? = some (.notification ntfn)) :
    st.objects[oid]? = some (.notification ntfn) := by
  induction fuel generalizing st tid with
  | zero => rw [propagatePipChainCrossCore_zero] at h; exact h
  | succ n ih =>
    rw [propagatePipChainCrossCore_step] at h
    have hNext := pipBoostWithWake_preserves_objects_invExt st tid ec hInv
    revert h
    cases hB : blockingServer st tid with
    | none =>
        intro h
        exact pipBoostWithWake_notification_backward st tid ec hInv oid ntfn h
    | some nextServer =>
        intro h
        exact pipBoostWithWake_notification_backward st tid ec hInv oid ntfn
          (ih _ nextServer hNext h)

-- ============================================================================
-- WS-RR RR2.20 — the PIP chain walk is a frame for replenish-queue affinity
-- ============================================================================

/-- WS-RR RR2.20 (frame): a PIP boost never touches any core's **replenish**
queue.  Its only scheduler write is the boosted holder's run-queue bucket
migration, and `setRunQueueOnCore` leaves the replenish queue alone. -/
theorem updatePipBoostOnCore_replenishQueueOnCore (st : SystemState) (c c' : CoreId)
    (tid : ThreadId) :
    (updatePipBoostOnCore st c tid).scheduler.replenishQueueOnCore c'
      = st.scheduler.replenishQueueOnCore c' := by
  simp only [updatePipBoostOnCore]
  split
  · split
    · rfl
    · split
      · split
        · exact SchedulerState.setRunQueueOnCore_replenishQueueOnCore _ _ _ _
        · rfl
      · rfl
  · rfl

/-- WS-RR RR2.20 (frame): a PIP boost never changes any SchedContext.  Its only
object write stores a `.tcb` at the holder's slot — a slot that already held a
`.tcb`, since the write is guarded on reading one there — so `getSchedContext?`
answers `none` at that slot in both states and is untouched everywhere else. -/
theorem updatePipBoostOnCore_getSchedContext? (st : SystemState) (c : CoreId)
    (tid : ThreadId) (hInv : st.objects.invExt) (scId : SchedContextId) :
    (updatePipBoostOnCore st c tid).getSchedContext? scId = st.getSchedContext? scId := by
  by_cases hEq : (tid.toObjId == scId.toObjId) = true
  · have hId : tid.toObjId = scId.toObjId := by simpa using hEq
    cases hT : st.getTcb? tid with
    | none => rw [updatePipBoostOnCore_eq_self_of_getTcb?_none st c tid hT]
    | some tcb =>
      obtain ⟨p, hPost⟩ := updatePipBoostOnCore_objects_at st c tid tcb hT hInv
      rw [SystemState.getSchedContext?_none_of_tcb (updatePipBoostOnCore st c tid) scId _
            (hId ▸ (SystemState.getTcb?_eq_some_iff (updatePipBoostOnCore st c tid) tid _).mp hPost),
          SystemState.getSchedContext?_none_of_tcb st scId tcb
            (hId ▸ (SystemState.getTcb?_eq_some_iff st tid tcb).mp hT)]
  · unfold SystemState.getSchedContext?
    rw [updatePipBoostOnCore_objects_ne st c tid scId.toObjId hEq hInv]

/-- WS-RR RR2.20 (frame): a PIP boost never moves a thread's home core.  It
rewrites exactly one TCB and only in `pipBoost`, and `determineTargetCore` reads
only `cpuAffinity`. -/
theorem updatePipBoostOnCore_determineTargetCore (st : SystemState) (c : CoreId)
    (tid t : ThreadId) (hInv : st.objects.invExt) :
    determineTargetCore (updatePipBoostOnCore st c tid) t = determineTargetCore st t := by
  refine determineTargetCore_congr st (updatePipBoostOnCore st c tid) t ?_
  by_cases hEq : (tid.toObjId == t.toObjId) = true
  · have hId : tid.toObjId = t.toObjId := by simpa using hEq
    obtain rfl : tid = t := SeLe4n.ThreadId.toObjId_injective _ _ hId
    cases hT : st.getTcb? tid with
    | none => rw [updatePipBoostOnCore_eq_self_of_getTcb?_none st c tid hT, hT]
    | some tcb =>
      obtain ⟨p, hPost⟩ := updatePipBoostOnCore_objects_at st c tid tcb hT hInv
      rw [hPost]
      rfl
  · have hRaw := updatePipBoostOnCore_objects_ne st c tid t.toObjId hEq hInv
    have hTcb : (updatePipBoostOnCore st c tid).getTcb? t = st.getTcb? t := by
      unfold SystemState.getTcb?; rw [hRaw]
    rw [hTcb]

/-- WS-RR RR2.20: the whole cross-core chain walk is a frame for the three
readings `replenishQueueAffinityConsistentOnCore` makes — the replenish queue,
`getSchedContext?` and `determineTargetCore` — by induction on the fuel. -/
theorem propagatePipChainCrossCore_replenish_readings (st : SystemState) (tid : ThreadId)
    (ec : CoreId) (fuel : Nat) (hInv : st.objects.invExt) :
    (∀ c, (propagatePipChainCrossCore st tid ec fuel).1.scheduler.replenishQueueOnCore c
        = st.scheduler.replenishQueueOnCore c)
    ∧ (∀ scId, (propagatePipChainCrossCore st tid ec fuel).1.getSchedContext? scId
        = st.getSchedContext? scId)
    ∧ (∀ t, determineTargetCore (propagatePipChainCrossCore st tid ec fuel).1 t
        = determineTargetCore st t) := by
  induction fuel generalizing st tid with
  | zero => rw [propagatePipChainCrossCore_zero]; exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  | succ n ih =>
    rw [propagatePipChainCrossCore_step]
    have hStep : (pipBoostWithWake st tid ec).1
        = updatePipBoostOnCore st (determineTargetCore st tid) tid := rfl
    have hNext : (pipBoostWithWake st tid ec).1.objects.invExt :=
      pipBoostWithWake_preserves_objects_invExt st tid ec hInv
    have hHere : (∀ c, (pipBoostWithWake st tid ec).1.scheduler.replenishQueueOnCore c
          = st.scheduler.replenishQueueOnCore c)
        ∧ (∀ scId, (pipBoostWithWake st tid ec).1.getSchedContext? scId
          = st.getSchedContext? scId)
        ∧ (∀ t, determineTargetCore (pipBoostWithWake st tid ec).1 t
          = determineTargetCore st t) := by
      rw [hStep]
      exact ⟨fun c => updatePipBoostOnCore_replenishQueueOnCore st _ c tid,
             fun scId => updatePipBoostOnCore_getSchedContext? st _ tid hInv scId,
             fun t => updatePipBoostOnCore_determineTargetCore st _ tid t hInv⟩
    cases hB : blockingServer st tid with
    | none => exact hHere
    | some nextServer =>
        obtain ⟨hR, hS, hT⟩ := ih (pipBoostWithWake st tid ec).1 nextServer hNext
        exact ⟨fun c => (hR c).trans (hHere.1 c),
               fun scId => (hS scId).trans (hHere.2.1 scId),
               fun t => (hT t).trans (hHere.2.2 t)⟩

end SeLe4n.Kernel.PriorityInheritance
