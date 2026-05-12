-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.PriorityInheritance.BlockingGraph
import SeLe4n.Kernel.Scheduler.Operations.Selection

namespace SeLe4n.Kernel.PriorityInheritance

open SeLe4n.Model

-- ============================================================================
-- D4-F: computeMaxWaiterPriority
-- ============================================================================

/-- D4-F: Compute the maximum effective priority among all threads
directly blocked on `tid` via Reply IPC. Returns `none` if no waiters.

WS-RC R5.C (DEEP-SCH-02): uses the total `effectiveSchedParams` helper,
which falls back to the waiter's TCB priority/deadline/domain when SC
lookup fails (unreachable under `schedContextStoreConsistent`).  This is
part of R5.C's API-uniformity goal: callers no longer thread `Option`
propagation through the priority-inheritance fold.

WS-RC R5.C.1 (DEEP-SCH-02): The pre-R5 `effectivePriority` partial helper
that this site previously consumed has been RETIRED (see
`Selection.lean` Z4-B section). -/
def computeMaxWaiterPriority (st : SystemState) (tid : ThreadId)
    : Option Priority :=
  let waiters := waitersOf st tid
  waiters.foldl (fun acc waiterTid =>
    match st.objects[waiterTid.toObjId]? with
    | some (KernelObject.tcb waiterTcb) =>
      let (prio, _, _) := effectiveSchedParams st waiterTcb
      match acc with
      | none => some prio
      | some curMax => some ⟨Nat.max curMax.val prio.val⟩
    | _ => acc) none

/-- D4-F: computeMaxWaiterPriority of a thread with no waiters is none. -/
theorem computeMaxWaiterPriority_no_waiters (st : SystemState) (tid : ThreadId)
    (h : waitersOf st tid = []) :
    computeMaxWaiterPriority st tid = none := by
  simp [computeMaxWaiterPriority, h]

-- ============================================================================
-- WS-RC R5.B.2 / Phase P1: computeMaxWaiterPriority frame lemma
-- ============================================================================

/-- WS-RC R5.B.2 / Phase P1: `waitersOf` is invariant under an operation that
    preserves the object table and object index.  This is the
    `objects/objectIndex`-frame for the waiter list. -/
theorem waitersOf_frame
    (st st' : SystemState) (tid : ThreadId)
    (hObjects : st'.objects = st.objects)
    (hObjIdx : st'.objectIndex = st.objectIndex) :
    waitersOf st' tid = waitersOf st tid := by
  unfold waitersOf
  rw [hObjIdx, hObjects]

/-- WS-RC R5.B.2 / Phase P1: `getSchedContext?` is invariant under an
    operation that preserves the object table. -/
theorem getSchedContext?_frame
    (st st' : SystemState) (scId : SchedContextId)
    (hObjects : st'.objects = st.objects) :
    st'.getSchedContext? scId = st.getSchedContext? scId := by
  unfold SystemState.getSchedContext?
  rw [hObjects]

/-- WS-RC R5.B.2 / Phase P1: `effectiveSchedParams` is invariant under an
    operation that preserves the object table.  The helper reads only
    `tcb` fields (passed by value) and `st.getSchedContext?` which reads
    `st.objects` exclusively. -/
theorem effectiveSchedParams_frame
    (st st' : SystemState) (tcb : TCB)
    (hObjects : st'.objects = st.objects) :
    effectiveSchedParams st' tcb = effectiveSchedParams st tcb := by
  unfold effectiveSchedParams
  -- The two sides differ only at the `st'.getSchedContext?` / `st.getSchedContext?`
  -- read; for unbound the result is fully determined by tcb fields.
  split
  · rfl  -- unbound: no SC lookup
  · rename_i scId _
    rw [getSchedContext?_frame st st' scId hObjects]
  · rename_i scId _ _
    rw [getSchedContext?_frame st st' scId hObjects]

/-- Helper for `computeMaxWaiterPriority_frame`: a pointwise-equal closure
    produces equal folds.  Used after the waiter list is shown equal.

    We use a definitionally-equal closure that pins the accumulator type
    to `Option Priority`, avoiding type-inference failures in the
    inductive body. -/
private def cmwpFoldBody (st : SystemState)
    (acc : Option SeLe4n.Priority) (waiterTid : ThreadId)
    : Option SeLe4n.Priority :=
  match st.objects[waiterTid.toObjId]? with
  | some (KernelObject.tcb waiterTcb) =>
    let (prio, _, _) := effectiveSchedParams st waiterTcb
    match acc with
    | none => some prio
    | some curMax => some ⟨Nat.max curMax.val prio.val⟩
  | _ => acc

/-- Helper: `cmwpFoldBody st'` agrees with `cmwpFoldBody st` pointwise when
    `st'.objects = st.objects`. -/
private theorem cmwpFoldBody_frame
    (st st' : SystemState)
    (hObjects : st'.objects = st.objects)
    (acc : Option SeLe4n.Priority) (waiterTid : ThreadId) :
    cmwpFoldBody st' acc waiterTid = cmwpFoldBody st acc waiterTid := by
  unfold cmwpFoldBody
  rw [hObjects]
  cases hObj : st.objects[waiterTid.toObjId]? with
  | none => rfl
  | some obj =>
    cases obj with
    | tcb tc =>
      simp only [effectiveSchedParams_frame st st' tc hObjects]
    | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _
      | schedContext _ => rfl

private theorem computeMaxWaiterPriority_foldBody_frame
    (st st' : SystemState) (ws : List ThreadId)
    (hObjects : st'.objects = st.objects) :
    ∀ acc : Option SeLe4n.Priority,
      ws.foldl (cmwpFoldBody st') acc = ws.foldl (cmwpFoldBody st) acc := by
  induction ws with
  | nil => intro acc; rfl
  | cons head tail ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [cmwpFoldBody_frame st st' hObjects acc head]
    exact ih _

/-- Bridge: `computeMaxWaiterPriority` is the `cmwpFoldBody` fold. -/
private theorem computeMaxWaiterPriority_eq_cmwpFoldBody (st : SystemState) (tid : ThreadId) :
    computeMaxWaiterPriority st tid = (waitersOf st tid).foldl (cmwpFoldBody st) none := by
  rfl

/-- WS-RC R5.B.2 / Phase P1: `computeMaxWaiterPriority` is invariant under
    an operation that preserves the object table and object index.

    This is the simplest "full frame": when the objects table is unchanged,
    every read site of `computeMaxWaiterPriority` (waitersOf,
    effectiveSchedParams via `st.getSchedContext?`) returns identical
    results, so the fold collapses to the pre-state value.

    Used by `ensureRunnable_preserves_computeMaxWaiterPriority` and
    `schedule_preserves_computeMaxWaiterPriority` (Phase Q2), both of
    which only modify `scheduler.runQueue` or `machine.regs` /
    `tcb.registerContext` — fields not read by `computeMaxWaiterPriority`. -/
theorem computeMaxWaiterPriority_frame
    (st st' : SystemState) (tid : ThreadId)
    (hObjects : st'.objects = st.objects)
    (hObjIdx : st'.objectIndex = st.objectIndex) :
    computeMaxWaiterPriority st' tid = computeMaxWaiterPriority st tid := by
  -- Both reads (`waitersOf` and the fold body) only touch `st.objects` and
  -- `st.objectIndex`; if both fields agree across `st` and `st'`, the
  -- results agree.
  rw [computeMaxWaiterPriority_eq_cmwpFoldBody, computeMaxWaiterPriority_eq_cmwpFoldBody,
      waitersOf_frame st st' tid hObjects hObjIdx]
  exact computeMaxWaiterPriority_foldBody_frame st st' (waitersOf st tid) hObjects none

-- ============================================================================
-- WS-RC R5.B.2 / Phase P1: Per-field frame for computeMaxWaiterPriority
-- ============================================================================
--
-- `computeMaxWaiterPriority` reads from `objects` (and `objectIndex`).  The
-- fields it actually consumes from each TCB are:
--   * `ipcState` (via `waitersOf` for waiterhood and `effectiveSchedParams`
--     for the binding lookup site).
--   * `priority`, `deadline`, `domain`, `pipBoost`, `schedContextBinding`
--     (via `effectiveSchedParams` for the waiter's scheduling params).
-- And from each SchedContext (via `effectiveSchedParams`):
--   * `priority`, `deadline`, `domain`.
--
-- A finer-grained frame: if an operation rewrites one TCB at `oid` such
-- that the new TCB agrees with the old one on every field above, then
-- `computeMaxWaiterPriority` is invariant.  This is the framing used by
-- `schedule_preserves_computeMaxWaiterPriority` (Phase Q2), where the
-- only modification is to `registerContext`.

/-- WS-RC R5.B.2 / Phase P1: A TCB-only rewrite at `oid` that preserves
    every field read by `effectiveSchedParams`/`waitersOf` preserves
    `effectiveSchedParams` for any TCB.  Specifically: if the new TCB at
    `oid` shares `(priority, deadline, domain, pipBoost, schedContextBinding)`
    with the old one, and SCs are unchanged, then `effectiveSchedParams`
    on any TCB is invariant. -/
theorem effectiveSchedParams_frame_per_field
    (st st' : SystemState) (tcb : TCB)
    (hSc : ∀ scId, st'.getSchedContext? scId = st.getSchedContext? scId) :
    effectiveSchedParams st' tcb = effectiveSchedParams st tcb := by
  unfold effectiveSchedParams
  split
  · rfl
  · rename_i scId _
    rw [hSc scId]
  · rename_i scId _ _
    rw [hSc scId]

end SeLe4n.Kernel.PriorityInheritance
