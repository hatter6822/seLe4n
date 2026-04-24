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
      if tid ∈ st.scheduler.runQueue then
        let oldPrio := (resolveEffectivePrioDeadline st tcb).1
        let newPrio := (resolveEffectivePrioDeadline st' tcb').1
        if oldPrio != newPrio then
          { st' with
            scheduler := {
              st'.scheduler with
              runQueue := (st'.scheduler.runQueue.remove tid).insert tid newPrio
            }
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
  cases hTid : st.objects[tid.toObjId]? with
  | none => rfl
  | some obj =>
    cases obj with
    | tcb tcb =>
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
    | _ => rfl

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
    by_cases hRQ : tid ∈ st.scheduler.runQueue
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
private theorem blockingServer_congr_objects (st₁ st₂ : SystemState) (t : ThreadId)
    (h : st₁.objects[t.toObjId]? = st₂.objects[t.toObjId]?) :
    blockingServer st₁ t = blockingServer st₂ t := by
  simp only [blockingServer, h]

-- Helper: blockingServer is determined by the ipcState of the looked-up TCB
private theorem blockingServer_ipcState_congr (st₁ st₂ : SystemState) (t : ThreadId)
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
          by_cases hRQ : tid ∈ st.scheduler.runQueue
          · simp only [hRQ, ite_true]; split <;> exact hSelf
          · simp only [hRQ, ite_false]; exact hSelf
      | _ => rfl
  · exact blockingServer_congr_objects _ _ _ (updatePipBoost_ipcState_frame st tid hObjInv t hEq)

end SeLe4n.Kernel.PriorityInheritance
