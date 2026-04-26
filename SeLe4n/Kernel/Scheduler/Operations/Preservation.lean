-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.Core

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- Preservation theorems
-- WS-H12b: All proofs updated for dequeue-on-dispatch semantics.
-- ============================================================================

/-- WS-H12b: `setCurrentThread` preserves `queueCurrentConsistent` under
dequeue-on-dispatch: after removing `tid` from the run queue,
`setCurrentThread (some tid)` establishes `tid ∉ runnable`. -/
theorem setCurrentThread_preserves_queueCurrentConsistent
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (hNotMem : tid ∉ st.scheduler.runnable)
    (hStep : setCurrentThread (some tid) st = .ok ((), st')) :
    queueCurrentConsistent st'.scheduler := by
  simp [setCurrentThread] at hStep
  cases hStep
  simp [queueCurrentConsistent, hNotMem]

private theorem setCurrentThread_preserves_runQueueUnique
    (st st' : SystemState)
    (tid : Option SeLe4n.ThreadId)
    (hUnique : runQueueUnique st.scheduler)
    (hStep : setCurrentThread tid st = .ok ((), st')) :
    runQueueUnique st'.scheduler := by
  simp [setCurrentThread] at hStep
  cases hStep
  simpa [runQueueUnique] using hUnique

private theorem setCurrentThread_none_preserves_currentThreadValid
    (st st' : SystemState)
    (hStep : setCurrentThread none st = .ok ((), st')) :
    currentThreadValid st' := by
  simp [setCurrentThread] at hStep
  cases hStep
  simp [currentThreadValid]

theorem setCurrentThread_some_preserves_currentThreadValid
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (hObj : ∃ tcb : TCB, st.objects[tid.toObjId]? = some (.tcb tcb))
    (hStep : setCurrentThread (some tid) st = .ok ((), st')) :
    currentThreadValid st' := by
  simp [setCurrentThread] at hStep
  cases hStep
  simpa [currentThreadValid] using hObj

theorem chooseThread_preserves_state
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hStep : chooseThread st = .ok (next, st')) :
    st' = st := by
  unfold chooseThread at hStep
  cases hPick : chooseBestInBucket st.objects.get? st.scheduler.runQueue st.scheduler.activeDomain with
  | error e => simp [hPick] at hStep
  | ok best =>
      cases best with
      | none =>
          rcases (by simpa [hPick] using hStep : none = next ∧ st = st') with ⟨_, hSt⟩
          simpa using hSt.symm
      | some triple =>
          obtain ⟨tid, prio, dl⟩ := triple
          rcases (by simpa [hPick] using hStep : some tid = next ∧ st = st') with ⟨_, hSt⟩
          simpa using hSt.symm

/-- WS-H12b: `schedule` preserves `queueCurrentConsistent`.
After dequeue-on-dispatch, the selected thread is removed from the run queue
before being set as current, establishing `tid ∉ runnable`. -/
private theorem schedule_preserves_queueCurrentConsistent
    (st st' : SystemState)
    (hStep : schedule st = .ok ((), st')) :
    queueCurrentConsistent st'.scheduler := by
  unfold schedule at hStep
  cases hChoose : chooseThread st with
  | error e => simp [hChoose] at hStep
  | ok pick =>
      cases pick with
      | mk next stChoose =>
          cases next with
          | none =>
              simp only [hChoose] at hStep
              have hSet : setCurrentThread none (saveOutgoingContext stChoose) = .ok ((), st') := hStep
              simp [setCurrentThread] at hSet
              subst hSet
              simp [queueCurrentConsistent]
          | some tid =>
              cases hObj : stChoose.objects[tid.toObjId]? with
              | none => simp [hChoose, hObj] at hStep
              | some obj =>
                  cases obj with
                  | tcb tcb =>
                      by_cases hSchedOk : tid ∈ stChoose.scheduler.runQueue ∧ tcb.domain = stChoose.scheduler.activeDomain
                      · simp only [hChoose, hObj, hSchedOk] at hStep
                        have hSet := hStep
                        simp [setCurrentThread] at hSet
                        subst hSet
                        simp only [queueCurrentConsistent, SchedulerState.runnable]
                        exact RunQueue.not_mem_remove_toList stChoose.scheduler.runQueue tid
                      · have hSchedOk' : ¬(stChoose.scheduler.runQueue.contains tid = true ∧ tcb.domain = stChoose.scheduler.activeDomain) := by
                          simpa [RunQueue.mem_iff_contains] using hSchedOk
                        simp [hChoose, hObj, hSchedOk'] at hStep
                  | endpoint ep => simp [hChoose, hObj] at hStep
                  | notification ntfn => simp [hChoose, hObj] at hStep
                  | cnode cn => simp [hChoose, hObj] at hStep
                  | vspaceRoot root => simp [hChoose, hObj] at hStep
                  | untyped ut => simp [hChoose, hObj] at hStep
                  | schedContext _ => simp [hChoose, hObj] at hStep

/-- S3-G/U-M09: `schedule` preserves `RunQueue.wellFormed`.
    Uses `remove_preserves_wellFormed` for the dequeue path. -/
theorem schedule_preserves_runQueueWellFormed
    (st st' : SystemState)
    (hwf : RunQueue.wellFormed st.scheduler.runQueue)
    (hStep : schedule st = .ok ((), st')) :
    RunQueue.wellFormed st'.scheduler.runQueue := by
  unfold schedule at hStep
  cases hChoose : chooseThread st with
  | error e => simp [hChoose] at hStep
  | ok pick =>
      cases pick with
      | mk next stChoose =>
          have hChooseState : stChoose = st :=
            chooseThread_preserves_state st stChoose next hChoose
          have hwfChoose : RunQueue.wellFormed stChoose.scheduler.runQueue := by
            rw [hChooseState]; exact hwf
          cases next with
          | none =>
              simp only [hChoose] at hStep
              -- saveOutgoingContext doesn't change runQueue
              have hSaveRQ : (saveOutgoingContext stChoose).scheduler.runQueue = stChoose.scheduler.runQueue := by
                simp only [saveOutgoingContext]
                split
                · rfl
                · split <;> rfl
              unfold setCurrentThread at hStep
              simp at hStep; subst hStep
              exact hSaveRQ ▸ hwfChoose
          | some tid =>
              cases hObj : stChoose.objects[tid.toObjId]? with
              | none => simp [hChoose, hObj] at hStep
              | some obj =>
                  cases obj with
                  | tcb tcb =>
                      by_cases hSchedOk : tid ∈ stChoose.scheduler.runQueue ∧ tcb.domain = stChoose.scheduler.activeDomain
                      · simp only [hChoose, hObj, hSchedOk] at hStep
                        have : st'.scheduler.runQueue = stChoose.scheduler.runQueue.remove tid := by
                          simp [setCurrentThread] at hStep; cases hStep; rfl
                        rw [this]
                        exact RunQueue.remove_preserves_wellFormed _ hwfChoose _
                      · have hSchedOk' : ¬(stChoose.scheduler.runQueue.contains tid = true ∧ tcb.domain = stChoose.scheduler.activeDomain) := by
                          simpa [RunQueue.mem_iff_contains] using hSchedOk
                        simp [hChoose, hObj, hSchedOk'] at hStep
                  | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ =>
                      simp [hChoose, hObj] at hStep

/-- WS-H12b: `schedule` preserves `schedulerWellFormed`. -/
theorem schedule_preserves_wellFormed
    (st st' : SystemState)
    (hStep : schedule st = .ok ((), st')) :
    schedulerWellFormed st'.scheduler := by
  exact schedule_preserves_queueCurrentConsistent st st' hStep

private theorem chooseThread_preserves_queueCurrentConsistent
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hConsistent : queueCurrentConsistent st.scheduler)
    (hStep : chooseThread st = .ok (next, st')) :
    queueCurrentConsistent st'.scheduler := by
  rcases chooseThread_preserves_state st st' next hStep with rfl
  simpa using hConsistent

private theorem chooseThread_preserves_runQueueUnique
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hUnique : runQueueUnique st.scheduler)
    (hStep : chooseThread st = .ok (next, st')) :
    runQueueUnique st'.scheduler := by
  rcases chooseThread_preserves_state st st' next hStep with rfl
  simpa using hUnique

private theorem chooseThread_preserves_currentThreadValid
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hValid : currentThreadValid st)
    (hStep : chooseThread st = .ok (next, st')) :
    currentThreadValid st' := by
  rcases chooseThread_preserves_state st st' next hStep with rfl
  simpa using hValid

private theorem chooseThread_preserves_currentThreadInActiveDomain
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hInv : currentThreadInActiveDomain st)
    (hStep : chooseThread st = .ok (next, st')) :
    currentThreadInActiveDomain st' := by
  rcases chooseThread_preserves_state st st' next hStep with rfl
  simpa using hInv

/-- WS-H12b / AN5-B (SCH-M02): Helper — removing a thread from the run queue
preserves `Nodup`. This predicate is a `private` run-queue implementation
helper — NOT a public invariant-bundle component. Consumers of the
scheduler invariant bundle (`schedulerInvariantBundle`,
`schedulerInvariantBundleFull`) project `runQueueUnique`, not this
element-level lemma. -/
private theorem remove_preserves_nodup (rq : RunQueue) (tid : SeLe4n.ThreadId)
    (hNodup : rq.toList.Nodup) :
    (rq.remove tid).toList.Nodup := by
  simp only [RunQueue.toList]
  unfold RunQueue.remove
  exact hNodup.sublist List.filter_sublist

/-
AN5-B (SCH-M01) — TCB case-dispatch factoring.

The six primary operation preservation theorems below
(`schedule_preserves_runQueueUnique`,
 `schedule_preserves_currentThreadValid`,
 `schedule_preserves_currentThreadInActiveDomain`,
 `handleYield_preserves_runQueueUnique`,
 `handleYield_preserves_currentThreadValid`,
 `handleYield_preserves_currentThreadInActiveDomain`)
share the same non-TCB `cases obj` dispatch structure — each
non-TCB arm closes via `simp [hChoose, hObj] at hStep`. The
audit (SCH-M01) flagged this duplication as a ~80-LOC code
smell and a potential divergence vector.

The six sites remain as-is for now because:

1. The `hChoose` binding is lexically scoped per theorem (chooseThread
   vs the no-choose handleYield path) — a single shared helper would
   require threading the hypothesis through the abstraction.

2. The "else" branches in the TCB arm reference TCB-specific fields
   (`tcb.domain` vs `tcb.timeSlice` vs the context-bound `hObjInvChoose`).
   The factor-out is cleanest once the Preservation.lean file split
   (AN5-A, Theme 4.7) reorganises by operation family — each child
   module can define its own `tcbCasesPreservation` helper with the
   appropriate local context.

3. An earlier spike on this factoring required the introduction of a
   `schedule_tcb_branch_unit` scheme with 6+ hypothesis parameters per
   call site, which obscured the proof structure more than the
   duplication itself.

The plan's AN5-A sub-task will re-examine this factoring after the
child-module layout is settled, with a clear "single helper per
family" target.
-/
private theorem schedule_preserves_runQueueUnique
    (st st' : SystemState)
    (hUnique : runQueueUnique st.scheduler)
    (hStep : schedule st = .ok ((), st')) :
    runQueueUnique st'.scheduler := by
  unfold schedule at hStep
  cases hChoose : chooseThread st with
  | error e => simp [hChoose] at hStep
  | ok pick =>
      cases pick with
      | mk next stChoose =>
          have hChooseState : stChoose = st :=
            chooseThread_preserves_state st stChoose next hChoose
          have hUniqueChoose : runQueueUnique stChoose.scheduler := by
            simpa [hChooseState] using hUnique
          cases next with
          | none =>
              simp only [hChoose] at hStep
              have hSaveUnique : runQueueUnique (saveOutgoingContext stChoose).scheduler := by
                rw [saveOutgoingContext_scheduler]; exact hUniqueChoose
              exact setCurrentThread_preserves_runQueueUnique
                (saveOutgoingContext stChoose) st' none hSaveUnique hStep
          | some tid =>
              cases hObj : stChoose.objects[tid.toObjId]? with
              | none => simp [hChoose, hObj] at hStep
              | some obj =>
                  cases obj with
                  | tcb tcb =>
                      by_cases hSchedOk : tid ∈ stChoose.scheduler.runQueue ∧ tcb.domain = stChoose.scheduler.activeDomain
                      · simp only [hChoose, hObj, hSchedOk] at hStep
                        have hRemovedUnique : runQueueUnique { stChoose.scheduler with runQueue := stChoose.scheduler.runQueue.remove tid } := by
                          simp only [runQueueUnique, SchedulerState.runnable]
                          exact remove_preserves_nodup stChoose.scheduler.runQueue tid hUniqueChoose
                        have hSet := hStep
                        simp [setCurrentThread] at hSet
                        subst hSet
                        simp only [runQueueUnique] at hRemovedUnique ⊢
                        exact hRemovedUnique
                      · have hSchedOk' : ¬(stChoose.scheduler.runQueue.contains tid = true ∧ tcb.domain = stChoose.scheduler.activeDomain) := by
                          simpa [RunQueue.mem_iff_contains] using hSchedOk
                        simp [hChoose, hObj, hSchedOk'] at hStep
                  | endpoint ep => simp [hChoose, hObj] at hStep
                  | notification ntfn => simp [hChoose, hObj] at hStep
                  | cnode cn => simp [hChoose, hObj] at hStep
                  | vspaceRoot root => simp [hChoose, hObj] at hStep
                  | untyped ut => simp [hChoose, hObj] at hStep
                  | schedContext _ => simp [hChoose, hObj] at hStep

private theorem schedule_preserves_currentThreadValid
    (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : schedule st = .ok ((), st')) :
    currentThreadValid st' := by
  unfold schedule at hStep
  cases hChoose : chooseThread st with
  | error e => simp [hChoose] at hStep
  | ok pick =>
      cases pick with
      | mk next stChoose =>
          have hChooseState : stChoose = st :=
            chooseThread_preserves_state st stChoose next hChoose
          cases next with
          | none =>
              simp only [hChoose] at hStep
              exact setCurrentThread_none_preserves_currentThreadValid
                (saveOutgoingContext stChoose) st' hStep
          | some tid =>
              cases hObj : stChoose.objects[tid.toObjId]? with
              | none => simp [hChoose, hObj] at hStep
              | some obj =>
                  cases obj with
                  | tcb tcb =>
                      by_cases hSchedOk : tid ∈ stChoose.scheduler.runQueue ∧ tcb.domain = stChoose.scheduler.activeDomain
                      · simp only [hChoose, hObj, hSchedOk] at hStep
                        have hSet := hStep
                        simp [setCurrentThread] at hSet
                        subst hSet
                        show currentThreadValid _
                        simp only [currentThreadValid]
                        have hObjInvChoose : stChoose.objects.invExt := hChooseState ▸ hObjInv
                        exact saveOutgoingContext_preserves_tcb stChoose tid.toObjId tcb hObj hObjInvChoose
                      · have hSchedOk' : ¬(stChoose.scheduler.runQueue.contains tid = true ∧ tcb.domain = stChoose.scheduler.activeDomain) := by
                          simpa [RunQueue.mem_iff_contains] using hSchedOk
                        simp [hChoose, hObj, hSchedOk'] at hStep
                  | endpoint ep => simp [hChoose, hObj] at hStep
                  | notification ntfn => simp [hChoose, hObj] at hStep
                  | cnode cn => simp [hChoose, hObj] at hStep
                  | vspaceRoot root => simp [hChoose, hObj] at hStep
                  | untyped ut => simp [hChoose, hObj] at hStep
                  | schedContext _ => simp [hChoose, hObj] at hStep

private theorem schedule_preserves_currentThreadInActiveDomain
    (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : schedule st = .ok ((), st')) :
    currentThreadInActiveDomain st' := by
  unfold schedule at hStep
  cases hChoose : chooseThread st with
  | error e => simp [hChoose] at hStep
  | ok pick =>
      cases pick with
      | mk next stChoose =>
          have hChooseState : stChoose = st :=
            chooseThread_preserves_state st stChoose next hChoose
          cases next with
          | none =>
              simp only [hChoose] at hStep
              have hSet : setCurrentThread none (saveOutgoingContext stChoose) = .ok ((), st') := hStep
              simp [setCurrentThread] at hSet
              subst hSet
              simp [currentThreadInActiveDomain]
          | some tid =>
              cases hObj : stChoose.objects[tid.toObjId]? with
              | none => simp [hChoose, hObj] at hStep
              | some obj =>
                  cases obj with
                  | tcb tcb =>
                      by_cases hSchedOk : tid ∈ stChoose.scheduler.runQueue ∧ tcb.domain = stChoose.scheduler.activeDomain
                      · simp only [hChoose, hObj, hSchedOk] at hStep
                        have hSet := hStep
                        simp [setCurrentThread] at hSet
                        subst hSet
                        simp only [currentThreadInActiveDomain]
                        have hObjInvChoose : stChoose.objects.invExt := hChooseState ▸ hObjInv
                        obtain ⟨tcb', hTcb', hDomEq, _, _, _, _⟩ :=
                          saveOutgoingContext_tcb_fields stChoose tid.toObjId tcb hObj hObjInvChoose
                        simp only [hTcb', hDomEq]; exact hSchedOk.2
                      · have hSchedOk' : ¬(stChoose.scheduler.runQueue.contains tid = true ∧ tcb.domain = stChoose.scheduler.activeDomain) := by
                          simpa [RunQueue.mem_iff_contains] using hSchedOk
                        simp [hChoose, hObj, hSchedOk'] at hStep
                  | endpoint ep => simp [hChoose, hObj] at hStep
                  | notification ntfn => simp [hChoose, hObj] at hStep
                  | cnode cn => simp [hChoose, hObj] at hStep
                  | vspaceRoot root => simp [hChoose, hObj] at hStep
                  | untyped ut => simp [hChoose, hObj] at hStep
                  | schedContext _ => simp [hChoose, hObj] at hStep

/-- WS-H12b: `handleYield` preserves `queueCurrentConsistent`.
Re-enqueue + schedule re-establishes the invariant. -/
private theorem handleYield_preserves_queueCurrentConsistent
    (st st' : SystemState)
    (hStep : handleYield st = .ok ((), st')) :
    queueCurrentConsistent st'.scheduler := by
  unfold handleYield at hStep
  cases hCur : st.scheduler.current with
  | none =>
    -- V5-F: handleYield now returns .error .invalidArgument when current = none
    simp only [hCur] at hStep; cases hStep
  | some tid =>
    simp only [hCur] at hStep
    cases hObj : st.objects[tid.toObjId]? with
    | none => simp [hObj] at hStep
    | some obj =>
      cases obj with
      | tcb tcb =>
        simp only [hObj] at hStep
        exact schedule_preserves_queueCurrentConsistent _ st' hStep
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep

theorem handleYield_preserves_wellFormed
    (st st' : SystemState)
    (hStep : handleYield st = .ok ((), st')) :
    schedulerWellFormed st'.scheduler :=
  handleYield_preserves_queueCurrentConsistent st st' hStep

/-- WS-H12b / AN5-B (SCH-M02): Insert preserves `Nodup` when the element was
not present. Like `remove_preserves_nodup`, this is a `private` run-queue
implementation helper — NOT a public invariant-bundle component. -/
private theorem insert_preserves_nodup (rq : RunQueue) (tid : SeLe4n.ThreadId) (prio : SeLe4n.Priority)
    (hNodup : rq.toList.Nodup) (hNotMem : tid ∉ rq) :
    (rq.insert tid prio).toList.Nodup := by
  rw [RunQueue.toList_insert_not_mem rq tid prio hNotMem]
  exact List.nodup_append.2 ⟨hNodup, List.pairwise_singleton _ _,
    fun x hx y hy => by
      have : y = tid := by simpa using hy
      subst this; intro hEq; subst hEq
      exact hNotMem ((RunQueue.mem_toList_iff_mem rq x).mp hx)⟩

private theorem handleYield_preserves_runQueueUnique
    (st st' : SystemState)
    (hUnique : runQueueUnique st.scheduler)
    (hQCC : queueCurrentConsistent st.scheduler)
    (hStep : handleYield st = .ok ((), st')) :
    runQueueUnique st'.scheduler := by
  unfold handleYield at hStep
  cases hCur : st.scheduler.current with
  | none =>
    -- V5-F: handleYield now returns .error .invalidArgument when current = none
    simp only [hCur] at hStep; cases hStep
  | some tid =>
    simp only [hCur] at hStep
    cases hObj : st.objects[tid.toObjId]? with
    | none => simp [hObj] at hStep
    | some obj =>
      cases obj with
      | tcb tcb =>
        simp only [hObj] at hStep
        have hNotMem : tid ∉ st.scheduler.runQueue := by
          have := hQCC; simp [queueCurrentConsistent, hCur] at this
          intro h; exact this ((RunQueue.mem_toList_iff_mem st.scheduler.runQueue tid).2 h)
        have hInsertNodup : (st.scheduler.runQueue.insert tid (effectiveRunQueuePriority tcb)).toList.Nodup :=
          insert_preserves_nodup st.scheduler.runQueue tid (effectiveRunQueuePriority tcb) hUnique hNotMem
        have hInsertMem : tid ∈ st.scheduler.runQueue.insert tid (effectiveRunQueuePriority tcb) := by
          rw [RunQueue.mem_insert]; exact Or.inr rfl
        have hRotatedNodup : ((st.scheduler.runQueue.insert tid (effectiveRunQueuePriority tcb)).rotateToBack tid).toList.Nodup :=
          RunQueue.toList_rotateToBack_nodup _ tid hInsertNodup hInsertMem
        exact schedule_preserves_runQueueUnique _ st' (by
          simp only [runQueueUnique, SchedulerState.runnable]; exact hRotatedNodup) hStep
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep

private theorem handleYield_preserves_currentThreadValid
    (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : handleYield st = .ok ((), st')) :
    currentThreadValid st' := by
  unfold handleYield at hStep
  cases hCur : st.scheduler.current with
  | none =>
    -- V5-F: handleYield now returns .error .invalidArgument when current = none
    simp only [hCur] at hStep; cases hStep
  | some tid =>
    simp only [hCur] at hStep
    cases hObj : st.objects[tid.toObjId]? with
    | none => simp [hObj] at hStep
    | some obj =>
      cases obj with
      | tcb tcb =>
        simp only [hObj] at hStep
        -- The intermediate state has st.objects unchanged (only scheduler changes)
        apply schedule_preserves_currentThreadValid _ st' _ hStep
        exact hObjInv
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep

private theorem handleYield_preserves_currentThreadInActiveDomain
    (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : handleYield st = .ok ((), st')) :
    currentThreadInActiveDomain st' := by
  unfold handleYield at hStep
  cases hCur : st.scheduler.current with
  | none =>
    -- V5-F: handleYield now returns .error .invalidArgument when current = none
    simp only [hCur] at hStep; cases hStep
  | some tid =>
    simp only [hCur] at hStep
    cases hObj : st.objects[tid.toObjId]? with
    | none => simp [hObj] at hStep
    | some obj =>
      cases obj with
      | tcb tcb =>
        simp only [hObj] at hStep
        apply schedule_preserves_currentThreadInActiveDomain _ st' _ hStep
        exact hObjInv
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep

theorem chooseThread_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hStep : chooseThread st = .ok (next, st')) :
    schedulerInvariantBundle st' := by
  exact ⟨
    chooseThread_preserves_queueCurrentConsistent st st' next hInv.1 hStep,
    chooseThread_preserves_runQueueUnique st st' next hInv.2.1 hStep,
    chooseThread_preserves_currentThreadValid st st' next hInv.2.2 hStep
  ⟩

theorem schedule_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (hInv : schedulerInvariantBundle st)
    (hObjInv : st.objects.invExt)
    (hStep : schedule st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  exact ⟨
    schedule_preserves_queueCurrentConsistent st st' hStep,
    schedule_preserves_runQueueUnique st st' hInv.2.1 hStep,
    schedule_preserves_currentThreadValid st st' hObjInv hStep
  ⟩

theorem handleYield_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (hInv : schedulerInvariantBundle st)
    (hObjInv : st.objects.invExt)
    (hStep : handleYield st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  exact ⟨
    handleYield_preserves_queueCurrentConsistent st st' hStep,
    handleYield_preserves_runQueueUnique st st' hInv.2.1 hInv.1 hStep,
    handleYield_preserves_currentThreadValid st st' hObjInv hStep
  ⟩

-- ============================================================================
-- M-05/WS-E6: switchDomain preserves scheduler invariant bundle
-- WS-H12b: Updated for re-enqueue before domain switch.
-- ============================================================================

/-- WS-H12b: `switchDomain` preserves the scheduler invariant bundle.
Re-enqueues the current thread before advancing the domain schedule. -/
private theorem switchDomain_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (hInv : schedulerInvariantBundle st)
    (hStep : switchDomain st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  rcases hInv with ⟨hQCC, hRQU, hCTV⟩
  unfold switchDomain at hStep
  cases hSched : st.scheduler.domainSchedule with
  | nil =>
      simp [hSched] at hStep
      cases hStep; exact ⟨hQCC, hRQU, hCTV⟩
  | cons entry rest =>
      simp [hSched] at hStep
      split at hStep
      · -- AK2-I: fallback now emits `.error`; the Except contradiction is
        -- already discharged by `simp at hStep` during the split.
        cases hStep
      · rename_i _ hGet
        simp at hStep
        cases hStep
        refine ⟨?_, ?_, ?_⟩
        · simp [queueCurrentConsistent]
        · -- runQueueUnique: need to show the potentially-expanded runQueue is still Nodup
          simp only [runQueueUnique, SchedulerState.runnable]
          -- Case-split on current to reduce the match computing rq'
          cases hCur : st.scheduler.current with
          | none => exact hRQU
          | some curTid =>
            simp only []
            cases hObj : st.objects[curTid.toObjId]? with
            | none => exact hRQU
            | some obj =>
              cases obj with
              | tcb curTcb =>
                have hNotMem : curTid ∉ st.scheduler.runQueue := by
                  have hqcc := hQCC
                  simp [queueCurrentConsistent, hCur] at hqcc
                  intro h; exact hqcc ((RunQueue.mem_toList_iff_mem st.scheduler.runQueue curTid).2 h)
                exact insert_preserves_nodup st.scheduler.runQueue curTid (effectiveRunQueuePriority curTcb) hRQU hNotMem
              | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ => exact hRQU
        · simp [currentThreadValid]

/-- M-05/WS-E6: `scheduleDomain` preserves the active-domain current-thread
obligation when it holds in the pre-state. -/
theorem scheduleDomain_preserves_currentThreadInActiveDomain
    (st st' : SystemState)
    (hInv : currentThreadInActiveDomain st)
    (hObjInv : st.objects.invExt)
    (hStep : scheduleDomain st = .ok ((), st')) :
    currentThreadInActiveDomain st' := by
  unfold scheduleDomain at hStep
  by_cases hExpire : st.scheduler.domainTimeRemaining ≤ 1
  · simp [hExpire] at hStep
    cases hSw : switchDomain st with
    | error e => simp [hSw] at hStep
    | ok pair =>
        cases pair with
        | mk _ stSw =>
            have hSched : schedule stSw = .ok ((), st') := by simpa [hSw] using hStep
            have hSwObjInv : stSw.objects.invExt :=
              switchDomain_preserves_objects_invExt st stSw hObjInv (by simp [hSw])
            exact schedule_preserves_currentThreadInActiveDomain stSw st' hSwObjInv hSched
  · simp [hExpire] at hStep
    cases hStep
    simpa [currentThreadInActiveDomain] using hInv

/-- M-05/WS-E6: `scheduleDomain` preserves the scheduler invariant bundle. -/
theorem scheduleDomain_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (hInv : schedulerInvariantBundle st)
    (hObjInv : st.objects.invExt)
    (hStep : scheduleDomain st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  unfold scheduleDomain at hStep
  by_cases hExpire : st.scheduler.domainTimeRemaining ≤ 1
  · simp [hExpire] at hStep
    cases hSw : switchDomain st with
    | error e => simp [hSw] at hStep
    | ok pair =>
        cases pair with
        | mk _ stSw =>
            have hSched : schedule stSw = .ok ((), st') := by simpa [hSw] using hStep
            have hSwInv : schedulerInvariantBundle stSw :=
              switchDomain_preserves_schedulerInvariantBundle st stSw hInv (by simp [hSw])
            have hSwObjInv : stSw.objects.invExt :=
              switchDomain_preserves_objects_invExt st stSw hObjInv (by simp [hSw])
            exact schedule_preserves_schedulerInvariantBundle stSw st' hSwInv hSwObjInv hSched
  · simp [hExpire] at hStep
    cases hStep
    exact hInv

/-- M-05/WS-E6: `chooseThreadInDomain` is a pure read — it does not modify state. -/
theorem chooseThreadInDomain_preserves_state
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hStep : chooseThreadInDomain st = .ok (next, st')) :
    st' = st := by
  unfold chooseThreadInDomain at hStep
  exact chooseThread_preserves_state st st' next hStep

-- ============================================================================
-- WS-F4/F-03: timerTick preservation theorems
-- WS-H12b: Updated for re-enqueue on preemption.
-- ============================================================================

/-- WS-H12b: `timerTick` preserves `schedulerInvariantBundle`.
In the expired path, the intermediate state (after insert, before schedule)
violates QCC, so individual preservation theorems are composed directly
rather than using `schedule_preserves_schedulerInvariantBundle`. -/
theorem timerTick_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (hInv : schedulerInvariantBundle st)
    (hObjInv : st.objects.invExt)
    (hStep : timerTick st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  rcases hInv with ⟨hQCC, hRQU, hCTV⟩
  unfold timerTick at hStep
  cases hCur : st.scheduler.current with
  | none =>
    simp [hCur] at hStep; cases hStep; exact ⟨hQCC, hRQU, hCTV⟩
  | some tid =>
    simp only [hCur] at hStep
    cases hObj : st.objects[tid.toObjId]? with
    | none => simp [hObj] at hStep
    | some obj =>
      cases obj with
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
      | tcb tcb =>
        simp only [hObj] at hStep
        by_cases hExpire : tcb.timeSlice ≤ 1
        · -- Time-slice expired: re-enqueue + reschedule
          rw [if_pos hExpire] at hStep
          have hNotMem : tid ∉ st.scheduler.runQueue := by
            have := hQCC; simp [queueCurrentConsistent, hCur] at this
            intro h; exact this ((RunQueue.mem_toList_iff_mem st.scheduler.runQueue tid).2 h)
          have hInsertNodup : (st.scheduler.runQueue.insert tid (effectiveRunQueuePriority tcb)).toList.Nodup :=
            insert_preserves_nodup st.scheduler.runQueue tid (effectiveRunQueuePriority tcb) hRQU hNotMem
          -- The intermediate state has (st.objects.insert ...).invExt
          have hObjInv' : (st.objects.insert tid.toObjId (KernelObject.tcb { tcb with timeSlice := st.scheduler.configDefaultTimeSlice })).invExt :=
            RHTable_insert_preserves_invExt st.objects tid.toObjId _ hObjInv
          -- Compose individual preservation theorems (intermediate state violates QCC)
          exact ⟨
            schedule_preserves_queueCurrentConsistent _ st' hStep,
            schedule_preserves_runQueueUnique _ st' (by
              simp only [runQueueUnique, SchedulerState.runnable]; exact hInsertNodup) hStep,
            schedule_preserves_currentThreadValid _ st' hObjInv' hStep⟩
        · -- Time-slice not expired: scheduler unchanged
          rw [if_neg hExpire] at hStep
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, rfl⟩ := hStep
          refine ⟨hQCC, hRQU, ?_⟩
          unfold currentThreadValid; simp only [hCur]
          simp only [RHTable_getElem?_eq_get?]
          rw [RHTable_getElem?_insert st.objects tid.toObjId _ hObjInv]
          simp

-- ============================================================================
-- WS-H6: Bucket-first scheduling helpers
-- ============================================================================

private theorem isBetterCandidate_not_better_trans
    (p1 p2 p3 : SeLe4n.Priority) (d1 d2 d3 : SeLe4n.Deadline)
    (h12 : isBetterCandidate p2 d2 p1 d1 = false)
    (h23 : isBetterCandidate p3 d3 p2 d2 = false) :
    isBetterCandidate p3 d3 p1 d1 = false := by
  unfold isBetterCandidate at *
  have hp12 : ¬(p1.toNat > p2.toNat) := fun h => by simp [h] at h12
  have hp23 : ¬(p2.toNat > p3.toNat) := fun h => by simp [h] at h23
  have hp13 : ¬(p1.toNat > p3.toNat) := fun h => by omega
  simp only [hp13, ↓reduceIte]
  by_cases h1lt3 : p1.toNat < p3.toNat
  · simp [h1lt3]
  · simp only [h1lt3, ↓reduceIte]
    simp only [show ¬(p1.toNat > p2.toNat) from hp12,
               show ¬(p1.toNat < p2.toNat) from by omega, ↓reduceIte] at h12
    simp only [show ¬(p2.toNat > p3.toNat) from hp23,
               show ¬(p2.toNat < p3.toNat) from by omega, ↓reduceIte] at h23
    revert h12 h23
    cases d1.toNat <;> cases d2.toNat <;> cases d3.toNat <;> simp_all <;> omega

/-- WS-H6: Combined optimality for `chooseBestRunnableBy`. -/
private theorem chooseBestRunnableBy_optimal_combined
    (objects : SeLe4n.ObjId → Option KernelObject)
    (eligible : TCB → Bool)
    (runnable : List SeLe4n.ThreadId)
    (init : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline))
    (resTid : SeLe4n.ThreadId) (resPrio : SeLe4n.Priority) (resDl : SeLe4n.Deadline)
    (hOk : chooseBestRunnableBy objects eligible runnable init =
           .ok (some (resTid, resPrio, resDl)))
    (hAllTcb : ∀ t, t ∈ runnable → ∃ tcb, objects t.toObjId = some (.tcb tcb)) :
    (∀ t, t ∈ runnable →
      ∀ tcb, objects t.toObjId = some (.tcb tcb) →
        eligible tcb = true →
          isBetterCandidate resPrio resDl tcb.priority tcb.deadline = false) ∧
    (∀ initTid ip id, init = some (initTid, ip, id) →
       isBetterCandidate resPrio resDl ip id = false) := by
  induction runnable generalizing init with
  | nil =>
    simp [chooseBestRunnableBy] at hOk
    constructor
    · intro t hMem; simp at hMem
    · intro initTid ip id hInit; subst hOk; cases hInit
      exact isBetterCandidate_irrefl resPrio resDl
  | cons hd tl ih =>
    unfold chooseBestRunnableBy at hOk
    have hAllTl : ∀ t, t ∈ tl → ∃ tcb, objects t.toObjId = some (.tcb tcb) :=
      fun t hMem => hAllTcb t (List.mem_cons.mpr (Or.inr hMem))
    have hHdMem := hAllTcb hd (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨hdTcb, hHdObj⟩ := hHdMem
    simp only [hHdObj] at hOk
    cases hEligB : eligible hdTcb with
    | false =>
      simp only [hEligB] at hOk
      have ⟨ihP1, ihP2⟩ := ih init hOk hAllTl
      constructor
      · intro t hMem tcb hObj hE
        simp only [List.mem_cons] at hMem
        rcases hMem with h_eq | hTl
        · have h1 : objects hd.toObjId = some (.tcb tcb) := h_eq ▸ hObj
          rw [hHdObj] at h1; cases h1; simp [hE] at hEligB
        · exact ihP1 t hTl tcb hObj hE
      · exact ihP2
    | true =>
      simp only [hEligB, ↓reduceIte] at hOk
      cases init with
      | none =>
        have ⟨ihP1, ihP2⟩ := ih (some (hd, hdTcb.priority, hdTcb.deadline)) hOk hAllTl
        constructor
        · intro t hMem tcb hObj hE
          simp only [List.mem_cons] at hMem
          rcases hMem with h_eq | hTl
          · have hFlds : tcb.priority = hdTcb.priority ∧ tcb.deadline = hdTcb.deadline := by
              have h1 : objects hd.toObjId = some (.tcb tcb) := h_eq ▸ hObj
              rw [hHdObj] at h1; cases h1; exact ⟨rfl, rfl⟩
            rw [hFlds.1, hFlds.2]
            exact ihP2 hd hdTcb.priority hdTcb.deadline rfl
          · exact ihP1 t hTl tcb hObj hE
        · intro _ ip id hNone; cases hNone
      | some triple =>
        obtain ⟨initTid, initPrio, initDl⟩ := triple
        dsimp only at hOk
        cases hBeatB : isBetterCandidate initPrio initDl hdTcb.priority hdTcb.deadline with
        | true =>
          simp only [hBeatB, ite_true] at hOk
          have ⟨ihP1, ihP2⟩ := ih (some (hd, hdTcb.priority, hdTcb.deadline)) hOk hAllTl
          constructor
          · intro t hMem tcb hObj hE
            simp only [List.mem_cons] at hMem
            rcases hMem with h_eq | hTl
            · have hFlds : tcb.priority = hdTcb.priority ∧ tcb.deadline = hdTcb.deadline := by
                have h1 : objects hd.toObjId = some (.tcb tcb) := h_eq ▸ hObj
                rw [hHdObj] at h1; cases h1; exact ⟨rfl, rfl⟩
              rw [hFlds.1, hFlds.2]
              exact ihP2 hd hdTcb.priority hdTcb.deadline rfl
            · exact ihP1 t hTl tcb hObj hE
          · intro _ ip id hSome; cases hSome
            have hHdNoBetter := ihP2 hd hdTcb.priority hdTcb.deadline rfl
            cases hResVsInit : isBetterCandidate resPrio resDl initPrio initDl with
            | false => rfl
            | true =>
              exact absurd (isBetterCandidate_transitive resPrio initPrio hdTcb.priority
                        resDl initDl hdTcb.deadline hResVsInit hBeatB) (by rw [hHdNoBetter]; decide)
        | false =>
          simp only [hBeatB] at hOk
          have ⟨ihP1, ihP2⟩ := ih (some (initTid, initPrio, initDl)) hOk hAllTl
          constructor
          · intro t hMem tcb hObj hE
            simp only [List.mem_cons] at hMem
            rcases hMem with h_eq | hTl
            · have hFlds : tcb.priority = hdTcb.priority ∧ tcb.deadline = hdTcb.deadline := by
                have h1 : objects hd.toObjId = some (.tcb tcb) := h_eq ▸ hObj
                rw [hHdObj] at h1; cases h1; exact ⟨rfl, rfl⟩
              rw [hFlds.1, hFlds.2]
              exact isBetterCandidate_not_better_trans hdTcb.priority initPrio resPrio
                hdTcb.deadline initDl resDl hBeatB (ihP2 initTid initPrio initDl rfl)
            · exact ihP1 t hTl tcb hObj hE
          · exact ihP2

/-- WS-H6: Specialized optimality for init = none. -/
private theorem chooseBestRunnableBy_optimal
    (objects : SeLe4n.ObjId → Option KernelObject)
    (eligible : TCB → Bool)
    (runnable : List SeLe4n.ThreadId)
    (resTid : SeLe4n.ThreadId) (resPrio : SeLe4n.Priority) (resDl : SeLe4n.Deadline)
    (hOk : chooseBestRunnableBy objects eligible runnable none = .ok (some (resTid, resPrio, resDl)))
    (hAllTcb : ∀ t, t ∈ runnable → ∃ tcb, objects t.toObjId = some (.tcb tcb)) :
    ∀ t, t ∈ runnable →
      ∀ tcb, objects t.toObjId = some (.tcb tcb) →
        eligible tcb = true →
          isBetterCandidate resPrio resDl tcb.priority tcb.deadline = false :=
  (chooseBestRunnableBy_optimal_combined objects eligible runnable none
    resTid resPrio resDl hOk hAllTcb).1

/-- WS-H6: Connection from `isBetterCandidate` optimality to the EDF predicate.
If a thread t doesn't beat the result at equal priority, the EDF condition holds. -/
private theorem noBetter_implies_edf
    (resDl tDl : SeLe4n.Deadline)
    (prio : SeLe4n.Priority)
    (hNoBetter : isBetterCandidate prio resDl prio tDl = false) :
    resDl.toNat = 0 ∨ (tDl.toNat = 0 ∨ resDl.toNat ≤ tDl.toNat) := by
  unfold isBetterCandidate at hNoBetter
  simp [show ¬(prio.toNat > prio.toNat) from by omega] at hNoBetter
  revert hNoBetter
  cases hd1 : resDl.toNat <;> cases hd2 : tDl.toNat <;> simp_all <;> omega

-- ============================================================================
-- WS-H6: timeSlicePositive preservation
-- WS-H12b: Updated for dequeue-on-dispatch re-enqueue semantics.
-- ============================================================================

/-- WS-H6: `setCurrentThread` preserves `timeSlicePositive` — only `current` changes. -/
private theorem setCurrentThread_preserves_timeSlicePositive
    (st st' : SystemState)
    (tid : Option SeLe4n.ThreadId)
    (hInv : timeSlicePositive st)
    (hStep : setCurrentThread tid st = .ok ((), st')) :
    timeSlicePositive st' := by
  simp [setCurrentThread] at hStep; cases hStep; exact hInv

/-- WS-H6: `chooseThread` preserves `timeSlicePositive` — state unchanged. -/
theorem chooseThread_preserves_timeSlicePositive
    (st st' : SystemState)
    (next : Option SeLe4n.ThreadId)
    (hInv : timeSlicePositive st)
    (hStep : chooseThread st = .ok (next, st')) :
    timeSlicePositive st' := by
  rcases chooseThread_preserves_state st st' next hStep with rfl; exact hInv

/-- WS-H12b: Removing a thread from the run queue preserves `timeSlicePositive` —
the surviving runnable threads are a subset of the original, and their objects are unchanged. -/
private theorem remove_preserves_timeSlicePositive
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : timeSlicePositive st) :
    timeSlicePositive { st with scheduler := { st.scheduler with runQueue := st.scheduler.runQueue.remove tid } } := by
  intro t hMem
  simp only [SchedulerState.runnable] at hMem
  have hMemOrig : t ∈ st.scheduler.runnable := by
    simp only [SchedulerState.runnable]
    exact (RunQueue.mem_toList_iff_mem _ t).mpr
      ((RunQueue.mem_remove st.scheduler.runQueue tid t).mp
        ((RunQueue.mem_toList_iff_mem _ t).mp hMem)).1
  exact hInv t hMemOrig

/-- WS-H6/WS-H12b: `schedule` preserves `timeSlicePositive`.
Updated for dequeue-on-dispatch: the dequeued state's `timeSlicePositive`
follows from removal being a subset of the original runnable set. -/
private theorem schedule_preserves_timeSlicePositive
    (st st' : SystemState)
    (hInv : timeSlicePositive st)
    (hObjInv : st.objects.invExt)
    (hStep : schedule st = .ok ((), st')) :
    timeSlicePositive st' := by
  unfold schedule at hStep
  cases hChoose : chooseThread st with
  | error e => simp [hChoose] at hStep
  | ok pick =>
      cases pick with
      | mk next stChoose =>
          have hState : stChoose = st := chooseThread_preserves_state st stChoose next hChoose
          have hInvC : timeSlicePositive stChoose := by rw [hState]; exact hInv
          have hObjInvC : stChoose.objects.invExt := hState ▸ hObjInv
          cases next with
          | none =>
              simp only [hChoose] at hStep
              have hInvSave := saveOutgoingContext_preserves_timeSlicePositive stChoose hInvC hObjInvC
              exact setCurrentThread_preserves_timeSlicePositive
                (saveOutgoingContext stChoose) st' none hInvSave hStep
          | some tid =>
              cases hObj : stChoose.objects[tid.toObjId]? with
              | none => simp [hChoose, hObj] at hStep
              | some obj =>
                  cases obj with
                  | tcb tcb =>
                      by_cases hOk : tid ∈ stChoose.scheduler.runQueue ∧
                          tcb.domain = stChoose.scheduler.activeDomain
                      · simp only [hChoose, hObj, hOk] at hStep
                        have hSet := hStep
                        simp [setCurrentThread] at hSet
                        subst hSet
                        have hInvSave := saveOutgoingContext_preserves_timeSlicePositive stChoose hInvC hObjInvC
                        have hInvDq := remove_preserves_timeSlicePositive (saveOutgoingContext stChoose) tid hInvSave
                        intro t hMem
                        simp only [SchedulerState.runnable] at hMem ⊢
                        exact hInvDq t (by simpa [SchedulerState.runnable,
                          saveOutgoingContext_scheduler] using hMem)
                      · have hOk' : ¬(stChoose.scheduler.runQueue.contains tid = true ∧
                            tcb.domain = stChoose.scheduler.activeDomain) := by
                          simpa [RunQueue.mem_iff_contains] using hOk
                        simp [hChoose, hObj, hOk'] at hStep
                  | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ =>
                      simp [hChoose, hObj] at hStep

/-- WS-H6/WS-H12b: `handleYield` preserves `timeSlicePositive`.
Under dequeue-on-dispatch, the current thread is NOT in the run queue.
After insert+rotateToBack, `timeSlicePositive` holds because the current
thread's TCB (with positive time slice via `hCurTS`) is now in the queue,
and all previously-runnable threads retain their positive time slices. -/
private theorem handleYield_preserves_timeSlicePositive
    (st st' : SystemState)
    (hInv : timeSlicePositive st)
    (hCurTS : currentTimeSlicePositive st)
    (hObjInv : st.objects.invExt)
    (hStep : handleYield st = .ok ((), st')) :
    timeSlicePositive st' := by
  unfold handleYield at hStep
  cases hCur : st.scheduler.current with
  | none =>
    -- V5-F: handleYield now returns .error .invalidArgument when current = none
    simp only [hCur] at hStep; cases hStep
  | some tid =>
    simp only [hCur] at hStep
    cases hObj : st.objects[tid.toObjId]? with
    | none => simp [hObj] at hStep
    | some obj =>
      cases obj with
      | tcb tcb =>
        simp only [hObj] at hStep
        -- Build timeSlicePositive for the intermediate state with insert+rotateToBack
        have hInvMid : timeSlicePositive
            { st with scheduler := { st.scheduler with
                runQueue := (st.scheduler.runQueue.insert tid (effectiveRunQueuePriority tcb)).rotateToBack tid } } := by
          intro t hMemRot
          simp only [SchedulerState.runnable] at hMemRot
          -- t is in the rotated queue → t is in the inserted queue
          have hMemInsert : t ∈ st.scheduler.runQueue.insert tid (effectiveRunQueuePriority tcb) := by
            exact (RunQueue.mem_rotateToBack _ tid t).mp
              ((RunQueue.mem_toList_iff_mem _ t).mp hMemRot)
          -- Either t was already in rq, or t = tid
          rw [RunQueue.mem_insert] at hMemInsert
          cases hMemInsert with
          | inl hOld =>
            exact hInv t (by simp only [SchedulerState.runnable]; exact (RunQueue.mem_toList_iff_mem _ t).mpr hOld)
          | inr hEq =>
            subst hEq
            -- t = tid: use currentTimeSlicePositive
            simp [currentTimeSlicePositive, hCur, hObj] at hCurTS
            simp [hObj]; exact hCurTS
        rw [← hCur] at hStep
        let stMid : SystemState := { st with scheduler := { st.scheduler with
            runQueue := (st.scheduler.runQueue.insert tid (effectiveRunQueuePriority tcb)).rotateToBack tid } }
        have hObjInvMid : stMid.objects.invExt := hObjInv
        exact schedule_preserves_timeSlicePositive stMid st' hInvMid hObjInvMid hStep
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep

/-- WS-H6/WS-H12b: `switchDomain` preserves `timeSlicePositive`.
Re-enqueues the current thread (if any) before switching domains. -/
private theorem switchDomain_preserves_timeSlicePositive
    (st st' : SystemState)
    (hInv : timeSlicePositive st)
    (hCurTS : currentTimeSlicePositive st)
    (hObjInv : st.objects.invExt)
    (hStep : switchDomain st = .ok ((), st')) :
    timeSlicePositive st' := by
  unfold switchDomain at hStep
  cases hSched : st.scheduler.domainSchedule with
  | nil => simp [hSched] at hStep; cases hStep; exact hInv
  | cons entry rest =>
      simp [hSched] at hStep
      split at hStep
      · -- AK2-I: `.error` fallback; contradiction discharged during split.
        cases hStep
      · simp at hStep; cases hStep
        -- Objects are now (saveOutgoingContext st).objects; bridge via existing lemma
        have hSaveTS : timeSlicePositive (saveOutgoingContext st) :=
          saveOutgoingContext_preserves_timeSlicePositive st hInv hObjInv
        simp only [timeSlicePositive, SchedulerState.runnable]
        intro t hMem
        cases hCur : st.scheduler.current with
        | none =>
          simp only [hCur] at hMem
          exact hSaveTS t (by simp [SchedulerState.runnable]; exact hMem)
        | some curTid =>
          simp only [hCur] at hMem
          cases hObj : st.objects[curTid.toObjId]? with
          | none =>
            simp only [hObj] at hMem
            exact hSaveTS t (by simp [SchedulerState.runnable]; exact hMem)
          | some obj =>
            simp only [hObj] at hMem
            cases obj with
            | tcb curTcb =>
              have hMemInsert : t ∈ st.scheduler.runQueue.insert curTid (effectiveRunQueuePriority curTcb) :=
                (RunQueue.mem_toList_iff_mem _ t).mp hMem
              rw [RunQueue.mem_insert] at hMemInsert
              cases hMemInsert with
              | inl hOld =>
                exact hSaveTS t (by simp [SchedulerState.runnable]; exact (RunQueue.mem_toList_iff_mem _ t).mpr hOld)
              | inr hEq =>
                -- hEq : t = curTid; subst replaces curTid with t
                subst hEq
                simp only [currentTimeSlicePositive, hCur, hObj] at hCurTS
                obtain ⟨tcb', hTcb', _, _, _, hTSlice, _⟩ :=
                  saveOutgoingContext_tcb_fields st t.toObjId curTcb hObj hObjInv
                cases hLook : (saveOutgoingContext st).objects[t.toObjId]? with
                | none => rw [hTcb'] at hLook; exact absurd hLook (by simp)
                | some obj' =>
                  rw [hTcb'] at hLook; cases hLook; dsimp only
                  rw [hTSlice]; exact hCurTS
            | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ =>
              exact hSaveTS t (by simp [SchedulerState.runnable]; exact hMem)

/-- WS-H6: If two ThreadIds are not equal, their ObjIds are BEq-false.
Extracted to deduplicate the recurring inequality proof in object-store updates. -/
private theorem threadId_ne_objId_beq_false
    (tid t : SeLe4n.ThreadId) (hNe : t ≠ tid) :
    (tid.toObjId == t.toObjId) = false := by
  cases hb : (tid.toObjId == t.toObjId)
  · rfl
  · exfalso; apply hNe
    have : tid.toObjId = t.toObjId := by
      exact of_decide_eq_true (by rwa [ThreadId.toObjId, ThreadId.toObjId] at hb)
    cases tid; cases t; simp_all [ThreadId.toObjId, ObjId.ofNat, ThreadId.toNat]

/-- WS-H6/WS-H12b: `timerTick` preserves `timeSlicePositive`.
Expired case: resets to `configDefaultTimeSlice` (> 0 by `hConfigTS`), inserts into queue, then schedule.
Not-expired case: decrements, and since `timeSlice > 1`, the result is still > 0. -/
private theorem timerTick_preserves_timeSlicePositive
    (st st' : SystemState)
    (hInv : timeSlicePositive st)
    (hObjInv : st.objects.invExt)
    (hConfigTS : st.scheduler.configDefaultTimeSlice > 0)
    (hStep : timerTick st = .ok ((), st')) :
    timeSlicePositive st' := by
  unfold timerTick at hStep
  cases hCur : st.scheduler.current with
  | none =>
    simp [hCur] at hStep; cases hStep; exact hInv
  | some tid =>
    simp only [hCur] at hStep
    cases hObj : st.objects[tid.toObjId]? with
    | none => simp [hObj] at hStep
    | some obj =>
      cases obj with
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
      | tcb tcb =>
        simp only [hObj] at hStep
        by_cases hExpire : tcb.timeSlice ≤ 1
        · -- Time-slice expired: reset to configDefaultTimeSlice, insert, reschedule
          rw [if_pos hExpire] at hStep
          have hObjInv' := RHTable_insert_preserves_invExt st.objects tid.toObjId (KernelObject.tcb { tcb with timeSlice := st.scheduler.configDefaultTimeSlice }) hObjInv
          have hInvMid : timeSlicePositive
              { st with
                objects := st.objects.insert tid.toObjId (.tcb { tcb with timeSlice := st.scheduler.configDefaultTimeSlice })
                machine := tick st.machine
                scheduler := { st.scheduler with
                  runQueue := st.scheduler.runQueue.insert tid (effectiveRunQueuePriority tcb) } } := by
            intro t hMem
            simp only [SchedulerState.runnable] at hMem
            have hMemInsert : t ∈ st.scheduler.runQueue.insert tid (effectiveRunQueuePriority tcb) :=
              (RunQueue.mem_toList_iff_mem _ t).mp hMem
            rw [RunQueue.mem_insert] at hMemInsert
            cases hMemInsert with
            | inl hOld =>
              by_cases hEq : t = tid
              · subst hEq
                simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]; simp; exact hConfigTS
              · simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv, threadId_ne_objId_beq_false tid t hEq]
                exact hInv t (by simp only [SchedulerState.runnable]; exact (RunQueue.mem_toList_iff_mem _ t).mpr hOld)
            | inr hEq =>
              subst hEq
              simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]; simp; exact hConfigTS
          rw [← hCur] at hStep
          exact schedule_preserves_timeSlicePositive _ st' hInvMid hObjInv' hStep
        · -- Time-slice not expired: decrement, timeSlice - 1 > 0
          rw [if_neg hExpire] at hStep
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, rfl⟩ := hStep
          intro t hMem
          by_cases hEq : t = tid
          · subst hEq
            simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]; simp; omega
          · simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv, threadId_ne_objId_beq_false tid t hEq]
            exact hInv t hMem

-- ============================================================================
-- WS-H6/WS-H12b: currentTimeSlicePositive preservation
-- ============================================================================

/-- WS-H12b: `setCurrentThread none` trivially preserves `currentTimeSlicePositive`. -/
private theorem setCurrentThread_none_preserves_currentTimeSlicePositive
    (st st' : SystemState)
    (hStep : setCurrentThread none st = .ok ((), st')) :
    currentTimeSlicePositive st' := by
  simp [setCurrentThread] at hStep; cases hStep
  simp [currentTimeSlicePositive]

/-- WS-H12b: `setCurrentThread (some tid)` preserves `currentTimeSlicePositive`
when the thread has a positive time slice. -/
theorem setCurrentThread_some_preserves_currentTimeSlicePositive
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (hTS : match st.objects[tid.toObjId]? with
      | some (.tcb tcb) => tcb.timeSlice > 0
      | _ => True)
    (hStep : setCurrentThread (some tid) st = .ok ((), st')) :
    currentTimeSlicePositive st' := by
  simp [setCurrentThread] at hStep; cases hStep
  unfold currentTimeSlicePositive; dsimp; exact hTS

/-- WS-H12b: `schedule` preserves `currentTimeSlicePositive`.
When schedule selects a thread from the runnable queue, its `timeSlice > 0`
follows from `timeSlicePositive`. -/
private theorem schedule_preserves_currentTimeSlicePositive
    (st st' : SystemState)
    (hTS : timeSlicePositive st)
    (hObjInv : st.objects.invExt)
    (hStep : schedule st = .ok ((), st')) :
    currentTimeSlicePositive st' := by
  unfold schedule at hStep
  cases hChoose : chooseThread st with
  | error e => simp [hChoose] at hStep
  | ok pick =>
      cases pick with
      | mk next stChoose =>
          have hState : stChoose = st := chooseThread_preserves_state st stChoose next hChoose
          have hObjInvC : stChoose.objects.invExt := hState ▸ hObjInv
          cases next with
          | none =>
              simp only [hChoose] at hStep
              exact setCurrentThread_none_preserves_currentTimeSlicePositive
                (saveOutgoingContext stChoose) st' hStep
          | some tid =>
              cases hObj : stChoose.objects[tid.toObjId]? with
              | none => simp [hChoose, hObj] at hStep
              | some obj =>
                  cases obj with
                  | tcb tcb =>
                      by_cases hOk : tid ∈ stChoose.scheduler.runQueue ∧
                          tcb.domain = stChoose.scheduler.activeDomain
                      · -- tid was runnable → timeSlicePositive gives us tcb.timeSlice > 0
                        have hTidTS : tcb.timeSlice > 0 := by
                          have hMemRunnable : tid ∈ stChoose.scheduler.runnable := by
                            simpa [SchedulerState.runnable] using (RunQueue.mem_toList_iff_mem _ tid).mpr hOk.1
                          have hInvC := hTS; rw [← hState] at hInvC
                          have := hInvC tid hMemRunnable
                          simp [hObj] at this; exact this
                        simp only [hChoose, hObj, hOk] at hStep
                        have hSet := hStep
                        simp [setCurrentThread] at hSet
                        subst hSet
                        simp only [currentTimeSlicePositive]
                        obtain ⟨tcb', hTcb', _, _, _, hTSEq, _hPipEq⟩ :=
                          saveOutgoingContext_tcb_fields stChoose tid.toObjId tcb hObj hObjInvC
                        simp only [hTcb']; rw [hTSEq]; exact hTidTS
                      · have hOk' : ¬(stChoose.scheduler.runQueue.contains tid = true ∧
                            tcb.domain = stChoose.scheduler.activeDomain) := by
                          simpa [RunQueue.mem_iff_contains] using hOk
                        simp [hChoose, hObj, hOk'] at hStep
                  | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ =>
                      simp [hChoose, hObj] at hStep

/-- WS-H12b: `handleYield` preserves `currentTimeSlicePositive`. -/
private theorem handleYield_preserves_currentTimeSlicePositive
    (st st' : SystemState)
    (hTS : timeSlicePositive st)
    (hCurTS : currentTimeSlicePositive st)
    (hObjInv : st.objects.invExt)
    (hStep : handleYield st = .ok ((), st')) :
    currentTimeSlicePositive st' := by
  unfold handleYield at hStep
  cases hCur : st.scheduler.current with
  | none =>
    -- V5-F: handleYield now returns .error .invalidArgument when current = none
    simp only [hCur] at hStep; cases hStep
  | some tid =>
    simp only [hCur] at hStep
    cases hObj : st.objects[tid.toObjId]? with
    | none => simp [hObj] at hStep
    | some obj =>
      cases obj with
      | tcb tcb =>
        simp only [hObj] at hStep
        -- After insert+rotateToBack, the intermediate state's timeSlicePositive
        -- covers the inserted tid (via hCurTS). schedule then preserves it.
        have hInvMid : timeSlicePositive
            { st with scheduler := { st.scheduler with
                runQueue := (st.scheduler.runQueue.insert tid (effectiveRunQueuePriority tcb)).rotateToBack tid } } := by
          intro t hMemRot
          simp only [SchedulerState.runnable] at hMemRot
          have hMemInsert : t ∈ st.scheduler.runQueue.insert tid (effectiveRunQueuePriority tcb) :=
            (RunQueue.mem_rotateToBack _ tid t).mp
              ((RunQueue.mem_toList_iff_mem _ t).mp hMemRot)
          rw [RunQueue.mem_insert] at hMemInsert
          cases hMemInsert with
          | inl hOld =>
            exact hTS t (by simp only [SchedulerState.runnable]; exact (RunQueue.mem_toList_iff_mem _ t).mpr hOld)
          | inr hEq =>
            subst hEq
            simp [currentTimeSlicePositive, hCur, hObj] at hCurTS
            simp [hObj]; exact hCurTS
        rw [← hCur] at hStep
        let stMid : SystemState := { st with scheduler := { st.scheduler with
            runQueue := (st.scheduler.runQueue.insert tid (effectiveRunQueuePriority tcb)).rotateToBack tid } }
        have hObjInvMid : stMid.objects.invExt := hObjInv
        exact schedule_preserves_currentTimeSlicePositive stMid st' hInvMid hObjInvMid hStep
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep

/-- WS-H12b: `switchDomain` preserves `currentTimeSlicePositive`.
Domain switch sets `current := none`, so the predicate is trivially True. -/
private theorem switchDomain_preserves_currentTimeSlicePositive
    (st st' : SystemState)
    (hCurTS : currentTimeSlicePositive st)
    (hStep : switchDomain st = .ok ((), st')) :
    currentTimeSlicePositive st' := by
  unfold switchDomain at hStep
  cases hSched : st.scheduler.domainSchedule with
  | nil => simp [hSched] at hStep; cases hStep; exact hCurTS
  | cons entry rest =>
      simp [hSched] at hStep
      split at hStep
      · -- AK2-I: `.error` fallback; contradiction discharged during split.
        cases hStep
      · simp at hStep; cases hStep; simp [currentTimeSlicePositive]

/-- WS-H12b: `timerTick` preserves `currentTimeSlicePositive`. -/
private theorem timerTick_preserves_currentTimeSlicePositive
    (st st' : SystemState)
    (hTS : timeSlicePositive st)
    (_ : currentTimeSlicePositive st)
    (hObjInv : st.objects.invExt)
    (hConfigTS : st.scheduler.configDefaultTimeSlice > 0)
    (hStep : timerTick st = .ok ((), st')) :
    currentTimeSlicePositive st' := by
  unfold timerTick at hStep
  cases hCur : st.scheduler.current with
  | none =>
    simp [hCur] at hStep; cases hStep
    simp [currentTimeSlicePositive, hCur]
  | some tid =>
    simp only [hCur] at hStep
    cases hObj : st.objects[tid.toObjId]? with
    | none => simp [hObj] at hStep
    | some obj =>
      cases obj with
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
      | tcb tcb =>
        simp only [hObj] at hStep
        by_cases hExpire : tcb.timeSlice ≤ 1
        · -- Expired: insert + schedule. schedule selects from runnable (timeSlicePositive covers it)
          rw [if_pos hExpire] at hStep
          have hInvMid : timeSlicePositive
              { st with
                objects := st.objects.insert tid.toObjId (.tcb { tcb with timeSlice := st.scheduler.configDefaultTimeSlice })
                machine := tick st.machine
                scheduler := { st.scheduler with
                  runQueue := st.scheduler.runQueue.insert tid (effectiveRunQueuePriority tcb) } } := by
            intro t hMem
            simp only [SchedulerState.runnable] at hMem
            have hMemInsert : t ∈ st.scheduler.runQueue.insert tid (effectiveRunQueuePriority tcb) :=
              (RunQueue.mem_toList_iff_mem _ t).mp hMem
            rw [RunQueue.mem_insert] at hMemInsert
            cases hMemInsert with
            | inl hOld =>
              by_cases hEq : t = tid
              · subst hEq; simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]; simp; exact hConfigTS
              · simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv, threadId_ne_objId_beq_false tid t hEq]
                exact hTS t (by simp only [SchedulerState.runnable]; exact (RunQueue.mem_toList_iff_mem _ t).mpr hOld)
            | inr hEq =>
              subst hEq; simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]; simp; exact hConfigTS
          have hObjInv' := RHTable_insert_preserves_invExt st.objects tid.toObjId (KernelObject.tcb { tcb with timeSlice := st.scheduler.configDefaultTimeSlice }) hObjInv
          rw [← hCur] at hStep
          exact schedule_preserves_currentTimeSlicePositive _ st' hInvMid hObjInv' hStep
        · -- Not expired: decrement, current stays as tid
          rw [if_neg hExpire] at hStep
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, rfl⟩ := hStep
          unfold currentTimeSlicePositive; simp only [hCur]
          simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
          simp; omega

-- ============================================================================
-- WS-H6: EDF invariant preservation
-- WS-H12b: Updated for dequeue-on-dispatch (runnable set is post-dequeue).
-- ============================================================================

/-- WS-H6: `setCurrentThread none` trivially preserves EDF — no current thread. -/
private theorem setCurrentThread_none_preserves_edfCurrentHasEarliestDeadline
    (st st' : SystemState)
    (hStep : setCurrentThread none st = .ok ((), st')) :
    edfCurrentHasEarliestDeadline st' := by
  unfold setCurrentThread at hStep
  cases hStep
  simp [edfCurrentHasEarliestDeadline]

/-- WS-H6: `switchDomain` preserves `edfCurrentHasEarliestDeadline`.
Domain switch sets `current := none` in the transition case. -/
private theorem switchDomain_preserves_edfCurrentHasEarliestDeadline
    (st st' : SystemState)
    (hInv : edfCurrentHasEarliestDeadline st)
    (hStep : switchDomain st = .ok ((), st')) :
    edfCurrentHasEarliestDeadline st' := by
  unfold switchDomain at hStep
  cases hSched : st.scheduler.domainSchedule with
  | nil => simp [hSched] at hStep; cases hStep; exact hInv
  | cons entry rest =>
      simp [hSched] at hStep
      split at hStep
      · -- AK2-I: `.error` fallback; contradiction discharged during split.
        cases hStep
      · simp at hStep; cases hStep
        simp [edfCurrentHasEarliestDeadline]

-- ============================================================================
-- WS-H6: schedulerInvariantBundleFull composition
-- WS-H12b: Updated bundle includes currentTimeSlicePositive.
-- ============================================================================

/-- WS-H12e: `switchDomain` preserves `contextMatchesCurrent`.
In the no-op case (empty schedule), state is unchanged.
In the active case, `current = none`, so the invariant holds vacuously. -/
theorem switchDomain_preserves_contextMatchesCurrent
    (st st' : SystemState)
    (hInv : contextMatchesCurrent st)
    (hStep : switchDomain st = .ok ((), st')) :
    contextMatchesCurrent st' := by
  unfold switchDomain at hStep
  cases hSched : st.scheduler.domainSchedule with
  | nil =>
    rw [hSched] at hStep
    simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
    obtain ⟨_, hStEq⟩ := hStep; subst hStEq; exact hInv
  | cons hd tl =>
    rw [hSched] at hStep; simp only at hStep
    cases hIdx : (hd :: tl)[((st.scheduler.domainScheduleIndex + 1) % (hd :: tl).length)]? with
    | none =>
      -- AK2-I: fallback now emits `.error`; the Except contradiction is discharged.
      rw [hIdx] at hStep
      simp at hStep
    | some entry =>
      rw [hIdx] at hStep
      simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
      obtain ⟨_, hStEq⟩ := hStep; subst hStEq
      simp [contextMatchesCurrent]

-- ============================================================================
-- WS-F6/D3: runnableThreadsAreTCBs preservation per scheduler operation
-- ============================================================================

/-- WS-F6/D3: `switchDomain` preserves `runnableThreadsAreTCBs`.
`switchDomain` may re-enqueue the current thread; its TCB status follows from
`currentThreadValid` (which is part of the full bundle).
TPI-D12: Requires saveOutgoingContext + RunQueue.insert TCB-existence helper. -/
theorem switchDomain_preserves_runnableThreadsAreTCBs
    (st st' : SystemState)
    (hInv : runnableThreadsAreTCBs st)
    (hObjInv : st.objects.invExt)
    (hStep : switchDomain st = .ok ((), st')) :
    runnableThreadsAreTCBs st' := by
  unfold switchDomain at hStep
  cases hSched : st.scheduler.domainSchedule with
  | nil =>
      simp [hSched] at hStep; cases hStep; exact hInv
  | cons entry rest =>
      simp [hSched] at hStep
      split at hStep
      · -- AK2-I: `.error` fallback; contradiction discharged during split.
        cases hStep
      · rename_i _ hGet
        simp at hStep; cases hStep
        intro tid hMem
        simp only [SchedulerState.runnable] at hMem
        -- Helper: bridge TCB existence from st.objects to (saveOutgoingContext st).objects
        have bridge : ∀ (t : SeLe4n.ThreadId), (∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb)) →
            ∃ tcb', (saveOutgoingContext st).objects[t.toObjId]? = some (.tcb tcb') :=
          fun t ⟨tcb, h⟩ => saveOutgoingContext_preserves_tcb st t.toObjId tcb h hObjInv
        cases hCur : st.scheduler.current with
        | none =>
            simp [hCur] at hMem
            exact bridge tid (hInv tid (by simp [SchedulerState.runnable]; exact hMem))
        | some curTid =>
            cases hObj : st.objects[curTid.toObjId]? with
            | none =>
                simp [hCur, hObj] at hMem
                exact bridge tid (hInv tid (by simp [SchedulerState.runnable]; exact hMem))
            | some obj =>
                cases obj with
                | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ =>
                    simp [hCur, hObj] at hMem
                    exact bridge tid (hInv tid (by simp [SchedulerState.runnable]; exact hMem))
                | tcb tcb =>
                    simp [hCur, hObj] at hMem
                    rw [RunQueue.mem_toList_iff_mem] at hMem
                    rw [RunQueue.mem_insert] at hMem
                    cases hMem with
                    | inl hOld =>
                        rw [← RunQueue.mem_toList_iff_mem] at hOld
                        exact bridge tid (hInv tid (by simp [SchedulerState.runnable]; exact hOld))
                    | inr hEq =>
                        subst hEq
                        exact saveOutgoingContext_preserves_tcb st tid.toObjId tcb hObj hObjInv

/-- WS-F6/D3: `schedule` preserves `runnableThreadsAreTCBs`.
`schedule` removes a thread from the runnable queue (subset relation); TCB existence
is preserved through saveOutgoingContext (only modifies registerContext).
TPI-D12: Requires RunQueue.remove subset + saveOutgoingContext TCB-existence helper. -/
theorem schedule_preserves_runnableThreadsAreTCBs
    (st st' : SystemState)
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStep : schedule st = .ok ((), st')) :
    runnableThreadsAreTCBs st' := by
  unfold schedule at hStep
  cases hChoose : chooseThread st with
  | error e => simp [hChoose] at hStep
  | ok pick =>
      cases pick with
      | mk next stChoose =>
          have hStEqBase := chooseThread_preserves_state st stChoose next (by rw [hChoose])
          have hObjInvC : stChoose.objects.invExt := hStEqBase ▸ hObjInv
          cases next with
          | none =>
              simp only [hChoose] at hStep
              -- Derive st' facts
              have hObjSt' : st'.objects = (saveOutgoingContext stChoose).objects := by
                simp only [setCurrentThread] at hStep
                simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, rfl⟩ := hStep; rfl
              have hSchedSt' : st'.scheduler.runQueue = (saveOutgoingContext stChoose).scheduler.runQueue := by
                simp only [setCurrentThread] at hStep
                simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, rfl⟩ := hStep; rfl
              intro tid hMem
              simp only [SchedulerState.runnable] at hMem
              rw [hSchedSt', saveOutgoingContext_scheduler] at hMem
              have hMemOrig : tid ∈ st.scheduler.runnable := by
                rw [← hStEqBase]; simp [SchedulerState.runnable]; exact hMem
              obtain ⟨tcb, hTcb⟩ := hAllTcb tid hMemOrig
              rw [← hStEqBase] at hTcb
              rw [hObjSt']
              exact saveOutgoingContext_preserves_tcb stChoose tid.toObjId tcb hTcb hObjInvC
          | some tid =>
              simp only [hChoose] at hStep
              have hStEq := hStEqBase
              cases hObj : stChoose.objects[tid.toObjId]? with
              | none => simp [hObj] at hStep
              | some obj =>
                  cases obj with
                  | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ =>
                      simp [hObj] at hStep
                  | tcb tcb =>
                      simp only [hObj] at hStep
                      by_cases hSchedOk : tid ∈ stChoose.scheduler.runQueue ∧ tcb.domain = stChoose.scheduler.activeDomain
                      · rw [if_pos hSchedOk] at hStep
                        -- Extract st' properties without full substitution
                        have hObjSt' : st'.objects = (saveOutgoingContext stChoose).objects := by
                          simp only [setCurrentThread] at hStep
                          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                          obtain ⟨_, rfl⟩ := hStep
                          simp [restoreIncomingContext_objects]
                        have hSchedSt' : st'.scheduler.runQueue = stChoose.scheduler.runQueue.remove tid := by
                          simp only [setCurrentThread] at hStep
                          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                          obtain ⟨_, rfl⟩ := hStep
                          simp [restoreIncomingContext_scheduler, saveOutgoingContext_scheduler]
                        intro t hMem
                        simp only [SchedulerState.runnable] at hMem
                        rw [hSchedSt', RunQueue.mem_toList_iff_mem, RunQueue.mem_remove] at hMem
                        obtain ⟨hMemOrig, _⟩ := hMem
                        rw [← RunQueue.mem_toList_iff_mem] at hMemOrig
                        have hMemOrig' : t ∈ st.scheduler.runnable := by
                          rw [← hStEq]; simp [SchedulerState.runnable]; exact hMemOrig
                        obtain ⟨tcb', hTcb'⟩ := hAllTcb t hMemOrig'
                        rw [← hStEq] at hTcb'
                        rw [hObjSt']
                        exact saveOutgoingContext_preserves_tcb stChoose t.toObjId tcb' hTcb' hObjInvC
                      · have hSchedOk' : ¬(stChoose.scheduler.runQueue.contains tid = true ∧ tcb.domain = stChoose.scheduler.activeDomain) := by
                          simpa [RunQueue.mem_iff_contains] using hSchedOk
                        simp [hSchedOk'] at hStep

/-- WS-F6/D3: `handleYield` preserves `runnableThreadsAreTCBs`.
`handleYield` re-enqueues the current thread then calls `schedule`. Objects are
unchanged, and the re-enqueued thread is a TCB via `currentThreadValid`.
TPI-D12: Composition of schedule preservation + re-enqueue TCB-existence. -/
theorem handleYield_preserves_runnableThreadsAreTCBs
    (st st' : SystemState)
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStep : handleYield st = .ok ((), st')) :
    runnableThreadsAreTCBs st' := by
  unfold handleYield at hStep
  cases hCur : st.scheduler.current with
  | none =>
      -- V5-F: handleYield now returns .error .invalidArgument when current = none
      simp [hCur] at hStep
  | some tid =>
      cases hObj : st.objects[tid.toObjId]? with
      | none => simp [hCur, hObj] at hStep
      | some obj =>
          cases obj with
          | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ =>
              simp [hCur, hObj] at hStep
          | tcb tcb =>
              simp only [hCur, hObj] at hStep
              apply schedule_preserves_runnableThreadsAreTCBs _ st' _ (by exact hObjInv) hStep
              intro t hMem
              simp only [SchedulerState.runnable] at hMem
              rw [RunQueue.mem_toList_iff_mem] at hMem
              rw [RunQueue.mem_rotateToBack] at hMem
              rw [RunQueue.mem_insert] at hMem
              cases hMem with
              | inl hOld =>
                  rw [← RunQueue.mem_toList_iff_mem] at hOld
                  exact hAllTcb t (by simp [SchedulerState.runnable]; exact hOld)
              | inr hEq =>
                  subst hEq
                  exact ⟨tcb, hObj⟩

/-- WS-F6/D3: `timerTick` preserves `runnableThreadsAreTCBs`.
`timerTick` may call `schedule` when the time-slice expires. Objects are unchanged.
TPI-D12: Composition via schedule_preserves_runnableThreadsAreTCBs. -/
theorem timerTick_preserves_runnableThreadsAreTCBs
    (st st' : SystemState)
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStep : timerTick st = .ok ((), st')) :
    runnableThreadsAreTCBs st' := by
  unfold timerTick at hStep
  cases hCur : st.scheduler.current with
  | none =>
      -- No current thread: only machine timer advances
      simp [hCur] at hStep; cases hStep
      intro tid hMem
      exact hAllTcb tid hMem
  | some curTid =>
      simp only [hCur] at hStep
      cases hObj : st.objects[curTid.toObjId]? with
      | none => simp [hObj] at hStep
      | some obj =>
          cases obj with
          | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ =>
              simp [hObj] at hStep
          | tcb tcb =>
              simp only [hObj] at hStep
              by_cases hExp : tcb.timeSlice ≤ 1
              · -- Time-slice expired: reset TCB, re-enqueue, schedule
                rw [if_pos hExp] at hStep
                have hObjInv' := RHTable_insert_preserves_invExt st.objects curTid.toObjId (KernelObject.tcb { tcb with timeSlice := st.scheduler.configDefaultTimeSlice }) hObjInv
                apply schedule_preserves_runnableThreadsAreTCBs _ st' _ hObjInv' hStep
                intro t hMem
                simp only [SchedulerState.runnable] at hMem
                rw [RunQueue.mem_toList_iff_mem] at hMem
                rw [RunQueue.mem_insert] at hMem
                cases hMem with
                | inl hOld =>
                    rw [← RunQueue.mem_toList_iff_mem] at hOld
                    have hMemOrig : t ∈ st.scheduler.runnable := by
                      simp [SchedulerState.runnable]; exact hOld
                    obtain ⟨tcbT, hTcbT⟩ := hAllTcb t hMemOrig
                    simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
                    by_cases hEq : curTid.toObjId == t.toObjId
                    · simp [hEq]
                    · simp [hEq]; exact ⟨tcbT, hTcbT⟩
                | inr hEq =>
                    subst hEq
                    simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
                    simp [BEq.beq]
              · -- Time-slice not expired: decrement, no schedule call
                rw [if_neg hExp] at hStep
                simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, rfl⟩ := hStep
                intro tid hMem
                obtain ⟨tcbT, hTcbT⟩ := hAllTcb tid hMem
                simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
                by_cases hEqId : curTid.toObjId == tid.toObjId
                · simp [hEqId]
                · simp [hEqId]; exact ⟨tcbT, hTcbT⟩

/-- AK2-B helper: `saveOutgoingContext` modifies only ONE object at
`outTid.toObjId` (updating its registerContext field). For any other ObjId,
the lookup is literally unchanged. -/
private theorem saveOutgoingContext_preserves_lookup_of_ne
    (st : SystemState) (oid : SeLe4n.ObjId)
    (hNe : ∀ outTid, st.scheduler.current = some outTid → outTid.toObjId ≠ oid)
    (hObjInv : st.objects.invExt) :
    (saveOutgoingContext st).objects[oid]? = st.objects[oid]? := by
  unfold saveOutgoingContext
  cases hCur : st.scheduler.current with
  | none => rfl
  | some outTid =>
      dsimp only
      cases hOut : st.objects[outTid.toObjId]? with
      | none => rfl
      | some outObj =>
          cases outObj with
          | tcb outTcb =>
              dsimp only
              simp only [RHTable_getElem?_eq_get?]
              rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
              have hNeq : outTid.toObjId ≠ oid := hNe outTid hCur
              have hBEq : (outTid.toObjId == oid) = false := by
                cases hE : (outTid.toObjId == oid) with
                | false => rfl
                | true => exact absurd (beq_iff_eq.mp hE) hNeq
              simp [hBEq]
          | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ => rfl

/-- AK2-B helper: `saveOutgoingContext` preserves SchedContext lookups.
Used to discharge the SchedContext arm of the weak frame lemma. -/
private theorem saveOutgoingContext_preserves_schedContext_lookup
    (st : SystemState) (scId : SchedContextId) (sc : SchedContext)
    (hSc : st.objects[scId.toObjId]? = some (.schedContext sc))
    (hObjInv : st.objects.invExt) :
    (saveOutgoingContext st).objects[scId.toObjId]? = some (.schedContext sc) := by
  unfold saveOutgoingContext
  cases hCur : st.scheduler.current with
  | none => exact hSc
  | some outTid =>
      dsimp only
      cases hOut : st.objects[outTid.toObjId]? with
      | none => exact hSc
      | some outObj =>
          cases outObj with
          | tcb outTcb =>
              dsimp only
              simp only [RHTable_getElem?_eq_get?]
              rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
              by_cases hEq : outTid.toObjId == scId.toObjId
              · exfalso
                have hEq' := beq_iff_eq.mp hEq
                rw [hEq'] at hOut
                rw [hOut] at hSc; exact absurd hSc (by simp)
              · simp [hEq]
                simp only [RHTable_getElem?_eq_get?] at hSc
                exact hSc
          | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ =>
              exact hSc

/-- AK2-B: `saveOutgoingContext` preserves `effectiveBucketPriority` for any
TCB — it only modifies the outgoing TCB's registerContext, which
`effectiveBucketPriority` doesn't inspect. -/
private theorem saveOutgoingContext_effectiveBucketPriority_eq
    (st : SystemState) (tcb : TCB) (hObjInv : st.objects.invExt) :
    effectiveBucketPriority (saveOutgoingContext st) tcb
      = effectiveBucketPriority st tcb := by
  apply effectiveBucketPriority_frame_weak
  intros scId _
  by_cases hLook : ∃ sc, st.objects[scId.toObjId]? = some (.schedContext sc)
  · left
    obtain ⟨sc, hSc⟩ := hLook
    exact ⟨sc, hSc, saveOutgoingContext_preserves_schedContext_lookup st scId sc hSc hObjInv⟩
  · right
    have hLookN : ∀ sc, st.objects[scId.toObjId]? ≠ some (.schedContext sc) := by
      intro sc hE; exact hLook ⟨sc, hE⟩
    refine ⟨hLookN, ?_⟩
    -- Post-state: if saveOut produced a `.schedContext` at scId.toObjId, the
    -- input must also have had one — contradiction.
    intro sc hE
    by_cases hNe : ∀ outTid, st.scheduler.current = some outTid → outTid.toObjId ≠ scId.toObjId
    · have hPreserved : (saveOutgoingContext st).objects[scId.toObjId]? = st.objects[scId.toObjId]? :=
        saveOutgoingContext_preserves_lookup_of_ne st scId.toObjId hNe hObjInv
      rw [hPreserved] at hE
      exact hLookN sc hE
    · -- At scId.toObjId = outTid.toObjId, the post-state holds a .tcb (not
      -- a .schedContext). Contradict with hE.
      have hWitness : ∃ outTid, st.scheduler.current = some outTid ∧
          outTid.toObjId = scId.toObjId :=
        Classical.byContradiction fun h =>
          hNe fun outTid hCurX hEqX => h ⟨outTid, hCurX, hEqX⟩
      obtain ⟨outTid, hCur, hEq⟩ := hWitness
      -- The outgoing TCB's ObjId IS scId.toObjId. `st.objects[outTid.toObjId]?`
      -- must hold a TCB (currentThreadValid would tell us but we don't have
      -- that here; however if it holds any non-TCB, saveOut is a no-op there,
      -- and then hE says `some (.schedContext sc) = st.objects[scId.toObjId]?`
      -- which contradicts hLookN). Split cases:
      rw [← hEq] at hE
      -- hE now: (saveOut st).objects[outTid.toObjId]? = some (.schedContext sc)
      cases hOut : st.objects[outTid.toObjId]? with
      | none =>
        -- saveOut is no-op when outgoing TCB is missing
        have : (saveOutgoingContext st).objects[outTid.toObjId]? = none := by
          unfold saveOutgoingContext; rw [hCur]; simp [hOut]
        rw [this] at hE; exact absurd hE (by simp)
      | some outObj =>
        cases outObj with
        | tcb outTcb =>
          -- saveOut inserts .tcb at outTid.toObjId, hE says .schedContext
          have : (saveOutgoingContext st).objects[outTid.toObjId]?
              = some (.tcb { outTcb with registerContext := st.machine.regs }) := by
            unfold saveOutgoingContext
            rw [hCur]; dsimp only
            rw [hOut]; dsimp only
            simp only [RHTable_getElem?_eq_get?]
            rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
            simp
          rw [this] at hE; exact absurd hE (by simp)
        | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ =>
          -- saveOut is no-op when outgoing isn't a TCB; hE reduces to original
          -- st.objects[outTid.toObjId]? which is non-.schedContext by hOut, or
          -- is .schedContext sc. We must contradict hLookN.
          have hPres : (saveOutgoingContext st).objects[outTid.toObjId]?
              = st.objects[outTid.toObjId]? := by
            unfold saveOutgoingContext; rw [hCur]; simp [hOut]
          rw [hPres] at hE
          rw [hEq] at hE
          exact hLookN sc hE

/-- Helper: `schedulerPriorityMatch` transfers through `saveOutgoingContext` because
the scheduler (runQueue) is unchanged, TCB fields (priority, pipBoost,
schedContextBinding) are preserved, and SchedContext objects are untouched —
so `effectiveBucketPriority` agrees on both states. -/
private theorem schedulerPriorityMatch_of_saveOutgoingContext
    (st : SystemState) (hPM : schedulerPriorityMatch st)
    (hObjInv : st.objects.invExt) :
    schedulerPriorityMatch (saveOutgoingContext st) := by
  have hSchedEq : (saveOutgoingContext st).scheduler = st.scheduler := saveOutgoingContext_scheduler st
  intro tid hMem
  rw [hSchedEq] at hMem
  have hOrig := hPM tid hMem
  cases hTid : st.objects[tid.toObjId]? with
  | none =>
    have hNonTcb := saveOutgoingContext_preserves_non_tcb_lookup st tid.toObjId
      (by intro tcb h; rw [hTid] at h; exact absurd h (by simp)) hObjInv
    rw [hSchedEq]; rw [hNonTcb]; simp [hTid]
  | some obj =>
    cases obj with
    | tcb tcb =>
      obtain ⟨tcb', hTcb', _, hPri, _, _, hPip, _⟩ :=
        saveOutgoingContext_tcb_fields st tid.toObjId tcb hTid hObjInv
      simp [hTid] at hOrig; rw [hSchedEq]; simp [hTcb']
      simp [effectiveRunQueuePriority, hPri, hPip]; exact hOrig
    | _ =>
      have hNonTcb := saveOutgoingContext_preserves_non_tcb_lookup st tid.toObjId
        (by intro tcb h; rw [hTid] at h; exact absurd h (by simp)) hObjInv
      rw [hSchedEq]; rw [hNonTcb]; exact hOrig

/-- R6-D: `switchDomain` preserves `schedulerPriorityMatch`.
    switchDomain may insert the current thread at its priority; objects come from
    `saveOutgoingContext` which preserves TCB priorities.
    The proof follows the pattern of `switchDomain_preserves_runnableThreadsAreTCBs`. -/
private theorem switchDomain_preserves_schedulerPriorityMatch
    (st st' : SystemState)
    (hBase : schedulerInvariantBundle st)
    (hPM : schedulerPriorityMatch st)
    (hObjInv : st.objects.invExt)
    (hStep : switchDomain st = .ok ((), st')) :
    schedulerPriorityMatch st' := by
  unfold switchDomain at hStep
  cases hSched : st.scheduler.domainSchedule with
  | nil =>
    simp [hSched] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hPM
  | cons entry rest =>
    simp [hSched] at hStep
    split at hStep
    · -- AK2-I: `.error` fallback; contradiction discharged during split.
      simp at hStep
    · rename_i _ hGet
      simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
      obtain ⟨_, hSt⟩ := hStep
      -- Extract field equalities before subst
      have hObjEq : st'.objects = (saveOutgoingContext st).objects := by subst hSt; rfl
      -- Get schedulerPriorityMatch on saveOutgoingContext state
      have hPMSave := schedulerPriorityMatch_of_saveOutgoingContext st hPM hObjInv
      cases hCur : st.scheduler.current with
      | none =>
        have hRQEq : st'.scheduler.runQueue = st.scheduler.runQueue := by
          subst hSt; simp [hCur]
        exact schedulerPriorityMatch_of_runQueue_objects_eq (saveOutgoingContext st) st'
          hPMSave (by rw [hRQEq, saveOutgoingContext_scheduler]) hObjEq
      | some curTid =>
        cases hCurObj : st.objects[curTid.toObjId]? with
        | none =>
          have hRQEq : st'.scheduler.runQueue = st.scheduler.runQueue := by
            subst hSt; simp [hCur, hCurObj]
          exact schedulerPriorityMatch_of_runQueue_objects_eq (saveOutgoingContext st) st'
            hPMSave (by rw [hRQEq, saveOutgoingContext_scheduler]) hObjEq
        | some obj =>
          cases obj with
          | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ =>
            have hRQEq : st'.scheduler.runQueue = st.scheduler.runQueue := by
              subst hSt; simp [hCur, hCurObj]
            exact schedulerPriorityMatch_of_runQueue_objects_eq (saveOutgoingContext st) st'
              hPMSave (by rw [hRQEq, saveOutgoingContext_scheduler]) hObjEq
          | tcb curTcb =>
            -- runQueue = insert curTid (effectiveRunQueuePriority curTcb)
            have hRQEq : st'.scheduler.runQueue = st.scheduler.runQueue.insert curTid (effectiveRunQueuePriority curTcb) := by
              subst hSt; simp [hCur, hCurObj]
            -- Need to show schedulerPriorityMatch for the insert case
            -- Build from schedulerPriorityMatch_insert on st, then bridge objects
            intro tid hMem
            rw [hRQEq] at hMem
            have hInsert := schedulerPriorityMatch_insert st curTid curTcb hPM hBase.1 hCur hCurObj tid hMem
            -- Bridge: st.objects → st'.objects = (saveOutgoingContext st).objects
            rw [hObjEq, hRQEq]
            cases hTid : st.objects[tid.toObjId]? with
            | none =>
              have hNonTcb := saveOutgoingContext_preserves_non_tcb_lookup st tid.toObjId
                (by intro tcb h; rw [hTid] at h; exact absurd h (by simp)) hObjInv
              simp [hNonTcb, hTid]
            | some tidObj =>
              cases tidObj with
              | tcb tidTcb =>
                obtain ⟨tcb', hTcb', _, hPri, _, _, hPip, _⟩ :=
                  saveOutgoingContext_tcb_fields st tid.toObjId tidTcb hTid hObjInv
                simp [hTid] at hInsert; simp [hTcb']
                simp [effectiveRunQueuePriority, hPri, hPip]; exact hInsert
              | _ =>
                have hNonTcb := saveOutgoingContext_preserves_non_tcb_lookup st tid.toObjId
                  (by intro tcb h; rw [hTid] at h; exact absurd h (by simp)) hObjInv
                simp [hNonTcb, hTid]

-- ============================================================================
-- V5-H: domainTimeRemainingPositive preservation
-- ============================================================================

/-- V5-H: `saveOutgoingContext` preserves `domainTimeRemaining`.
    It only modifies `objects`, not `scheduler`. -/
private theorem saveOutgoingContext_domainTimeRemaining_eq (st : SystemState) :
    (saveOutgoingContext st).scheduler.domainTimeRemaining =
    st.scheduler.domainTimeRemaining := by
  unfold saveOutgoingContext
  cases st.scheduler.current with
  | none => rfl
  | some outTid =>
    cases hObj : st.objects[outTid.toObjId]? with
    | none => simp [hObj]
    | some obj => cases obj <;> simp [hObj]

/-- V5-H: `restoreIncomingContext` preserves `domainTimeRemaining`.
    It only modifies `machine`, not `scheduler`. -/
private theorem restoreIncomingContext_domainTimeRemaining_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (restoreIncomingContext st tid).scheduler.domainTimeRemaining =
    st.scheduler.domainTimeRemaining := by
  unfold restoreIncomingContext
  cases hObj : st.objects[tid.toObjId]? with
  | none => rfl
  | some obj => cases obj <;> simp

/-- V5-H: `schedule` preserves `domainTimeRemainingPositive`.
    `schedule` does not modify `domainTimeRemaining`. -/
theorem schedule_preserves_domainTimeRemainingPositive
    (st st' : SystemState)
    (hInv : domainTimeRemainingPositive st)
    (_hObjInv : st.objects.invExt)
    (hStep : schedule st = .ok ((), st')) :
    domainTimeRemainingPositive st' := by
  unfold schedule at hStep
  cases hChoose : chooseThread st with
  | error e => simp [hChoose] at hStep
  | ok pick =>
    cases pick with
    | mk next stChoose =>
      have hState := chooseThread_preserves_state st stChoose next hChoose
      cases next with
      | none =>
        simp only [hChoose] at hStep
        -- hStep : setCurrentThread none (saveOutgoingContext stChoose) = .ok ((), st')
        unfold setCurrentThread at hStep
        simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨_, rfl⟩ := hStep
        -- st' = { saveOutgoingContext stChoose with scheduler.current := none }
        unfold domainTimeRemainingPositive at *
        -- domainTimeRemaining is in scheduler, current change doesn't affect it
        show ({ saveOutgoingContext stChoose with scheduler := { (saveOutgoingContext stChoose).scheduler with current := none }}).scheduler.domainTimeRemaining > 0
        simp only []
        show (saveOutgoingContext stChoose).scheduler.domainTimeRemaining > 0
        rw [saveOutgoingContext_domainTimeRemaining_eq, hState]
        exact hInv
      | some tid =>
        cases hObj : stChoose.objects[tid.toObjId]? with
        | none => simp [hChoose, hObj] at hStep
        | some obj =>
          cases obj with
          | tcb tcb =>
            by_cases hOk : tid ∈ stChoose.scheduler.runQueue ∧ tcb.domain = stChoose.scheduler.activeDomain
            · -- schedule path: setCurrentThread ∘ restoreIncomingContext ∘ dequeue ∘ saveOutgoingContext
              -- None of these modify domainTimeRemaining.
              simp only [hChoose, hObj, hOk] at hStep
              -- hStep : setCurrentThread (some tid) (restoreIncomingContext ... tid) = .ok ((), st')
              -- Extract st' = the result state
              unfold setCurrentThread at hStep
              obtain ⟨_, rfl⟩ := hStep
              -- Goal: domainTimeRemainingPositive of { restoreIncomingContext ... with scheduler.current := ... }
              unfold domainTimeRemainingPositive at *
              -- current doesn't affect domainTimeRemaining
              show (restoreIncomingContext _ tid).scheduler.domainTimeRemaining > 0
              rw [restoreIncomingContext_domainTimeRemaining_eq]
              -- Now goal: { saveOutgoingContext stChoose with scheduler := { ... with runQueue := ... } }.scheduler.domainTimeRemaining > 0
              show ({ saveOutgoingContext stChoose with scheduler :=
                { (saveOutgoingContext stChoose).scheduler with
                  runQueue := (saveOutgoingContext stChoose).scheduler.runQueue.remove tid }
                }).scheduler.domainTimeRemaining > 0
              simp only []
              show (saveOutgoingContext stChoose).scheduler.domainTimeRemaining > 0
              rw [saveOutgoingContext_domainTimeRemaining_eq, hState]
              exact hInv
            · have hOk' : ¬(stChoose.scheduler.runQueue.contains tid = true ∧
                  tcb.domain = stChoose.scheduler.activeDomain) := by
                simpa [RunQueue.mem_iff_contains] using hOk
              simp [hChoose, hObj, hOk'] at hStep
          | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ =>
            simp [hChoose, hObj] at hStep

/-- V5-H: `handleYield` preserves `domainTimeRemainingPositive`.
    `handleYield` does not modify `domainTimeRemaining`. -/
theorem handleYield_preserves_domainTimeRemainingPositive
    (st st' : SystemState)
    (hInv : domainTimeRemainingPositive st)
    (hObjInv : st.objects.invExt)
    (hStep : handleYield st = .ok ((), st')) :
    domainTimeRemainingPositive st' := by
  unfold handleYield at hStep
  cases hCur : st.scheduler.current with
  | none =>
    -- V5-F: handleYield returns error when current = none
    simp only [hCur] at hStep; cases hStep
  | some tid =>
    simp only [hCur] at hStep
    cases hObj : st.objects[tid.toObjId]? with
    | none => simp [hObj] at hStep
    | some obj =>
      cases obj with
      | tcb tcb =>
        simp only [hObj] at hStep
        apply schedule_preserves_domainTimeRemainingPositive _ st' _ _ hStep
        · -- domainTimeRemainingPositive of intermediate state
          unfold domainTimeRemainingPositive at *; simp; exact hInv
        · exact hObjInv
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ =>
        simp [hObj] at hStep

/-- V5-H: `timerTick` preserves `domainTimeRemainingPositive`.
    `timerTick` only modifies `timeSlice`/`machine`, not `domainTimeRemaining`. -/
theorem timerTick_preserves_domainTimeRemainingPositive
    (st st' : SystemState)
    (hInv : domainTimeRemainingPositive st)
    (hObjInv : st.objects.invExt)
    (hStep : timerTick st = .ok ((), st')) :
    domainTimeRemainingPositive st' := by
  unfold timerTick at hStep
  cases hCur : st.scheduler.current with
  | none =>
    simp only [hCur, Except.ok.injEq, Prod.mk.injEq] at hStep
    obtain ⟨_, rfl⟩ := hStep; exact hInv
  | some tid =>
    simp only [hCur] at hStep
    cases hObj : st.objects[tid.toObjId]? with
    | none => simp [hObj] at hStep
    | some obj =>
      cases obj with
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
      | tcb tcb =>
        simp only [hObj] at hStep
        by_cases hExpire : tcb.timeSlice ≤ 1
        · -- Time-slice expired: schedule on modified state
          simp only [hExpire, ite_true] at hStep
          have hObjInv' := RHTable_insert_preserves_invExt st.objects tid.toObjId
            (KernelObject.tcb { tcb with timeSlice := st.scheduler.configDefaultTimeSlice }) hObjInv
          apply schedule_preserves_domainTimeRemainingPositive _ st' _ hObjInv' hStep
          -- domainTimeRemainingPositive of intermediate state: scheduler unchanged
          unfold domainTimeRemainingPositive at *; simp; exact hInv
        · -- Time-slice not expired: only objects/machine changed
          simp only [hExpire, ite_false, Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, rfl⟩ := hStep; exact hInv

/-- V5-H: `switchDomain` preserves `domainTimeRemainingPositive`.
    In the active branch, `domainTimeRemaining` is set to `entry.length`.
    Requires that all domain schedule entries have positive length. -/
theorem switchDomain_preserves_domainTimeRemainingPositive
    (st st' : SystemState)
    (hInv : domainTimeRemainingPositive st)
    (hEntriesPos : ∀ e, e ∈ st.scheduler.domainSchedule → e.length > 0)
    (hStep : switchDomain st = .ok ((), st')) :
    domainTimeRemainingPositive st' := by
  unfold switchDomain at hStep
  cases hSched : st.scheduler.domainSchedule with
  | nil => simp [hSched] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hInv
  | cons entry rest =>
    simp only [hSched] at hStep
    split at hStep
    · -- AK2-I: `.error` fallback; contradiction discharged during split.
      simp at hStep
    · rename_i nextEntry _
      simp at hStep; obtain ⟨_, rfl⟩ := hStep
      unfold domainTimeRemainingPositive; simp
      have hInList : nextEntry ∈ (entry :: rest) := by
        rename_i hGet
        exact List.mem_of_getElem? hGet
      exact hEntriesPos nextEntry (hSched ▸ hInList)

-- ============================================================================
-- X2-A/X2-C: domainSchedule frame lemmas
-- The domain schedule is set once at boot and is immutable at runtime.
-- Every scheduler operation preserves it, so these are pure frame lemmas.
-- ============================================================================

/-- X2-A: `switchDomain` preserves `domainSchedule`. In no-op branches (empty schedule,
    `getElem?` miss) the state is unchanged. In the active branch, the scheduler update
    uses `{ st.scheduler with ... }` which does not include `domainSchedule`. -/
theorem switchDomain_preserves_domainSchedule
    (st st' : SystemState)
    (hStep : switchDomain st = .ok ((), st')) :
    st'.scheduler.domainSchedule = st.scheduler.domainSchedule := by
  unfold switchDomain at hStep
  cases hSched : st.scheduler.domainSchedule with
  | nil =>
    simp [hSched] at hStep; cases hStep; exact hSched
  | cons entry rest =>
    simp only [hSched] at hStep
    split at hStep
    · -- AK2-I: `.error` fallback; contradiction discharged during split.
      simp at hStep
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
      obtain ⟨_, rfl⟩ := hStep
      show entry :: rest = entry :: rest
      rfl

/-- X2-C: `saveOutgoingContext` preserves `domainSchedule`. -/
private theorem saveOutgoingContext_preserves_domainSchedule
    (st : SystemState) :
    (saveOutgoingContext st).scheduler.domainSchedule = st.scheduler.domainSchedule := by
  unfold saveOutgoingContext
  cases st.scheduler.current with
  | none => rfl
  | some outTid =>
    simp
    split <;> simp

/-- X2-C: `restoreIncomingContext` preserves `domainSchedule`. -/
private theorem restoreIncomingContext_preserves_domainSchedule
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (restoreIncomingContext st tid).scheduler.domainSchedule = st.scheduler.domainSchedule := by
  unfold restoreIncomingContext
  split <;> simp

/-- X2-C: `chooseThread` preserves `domainSchedule`. -/
private theorem chooseThread_preserves_domainSchedule
    (st stCT : SystemState) (opt : Option SeLe4n.ThreadId)
    (hStep : chooseThread st = .ok (opt, stCT)) :
    stCT.scheduler.domainSchedule = st.scheduler.domainSchedule := by
  unfold chooseThread at hStep
  cases hCB : chooseBestInBucket st.objects.get? st.scheduler.runQueue st.scheduler.activeDomain with
  | error e => simp [hCB] at hStep
  | ok val =>
    simp [hCB] at hStep
    cases val with
    | none => simp at hStep; obtain ⟨_, rfl⟩ := hStep; rfl
    | some trip =>
      obtain ⟨tid, _, _⟩ := trip
      simp at hStep; obtain ⟨_, rfl⟩ := hStep; rfl

/-- X2-C: `schedule` preserves `domainSchedule`. `schedule` only modifies `runQueue`,
    `current`, `objects`, and `machine` — never `domainSchedule`. -/
theorem schedule_preserves_domainSchedule
    (st st' : SystemState)
    (hStep : schedule st = .ok ((), st')) :
    st'.scheduler.domainSchedule = st.scheduler.domainSchedule := by
  unfold schedule at hStep
  cases hCT : chooseThread st with
  | error e => simp [hCT] at hStep
  | ok pair =>
    cases pair with
    | mk opt stCT =>
      have hSchedCT := chooseThread_preserves_domainSchedule st stCT opt hCT
      simp [hCT] at hStep
      cases opt with
      | none =>
        simp at hStep; unfold setCurrentThread at hStep; cases hStep
        show (saveOutgoingContext stCT).scheduler.domainSchedule = st.scheduler.domainSchedule
        rw [saveOutgoingContext_preserves_domainSchedule, hSchedCT]
      | some tid =>
        simp at hStep
        split at hStep
        · rename_i tcb _
          split at hStep
          · unfold setCurrentThread restoreIncomingContext saveOutgoingContext at hStep
            split at hStep <;> simp only [Except.ok.injEq, Prod.mk.injEq] at hStep <;>
              obtain ⟨_, rfl⟩ := hStep <;> exact hSchedCT
          · simp at hStep
        · simp at hStep

/-- X2-C: `handleYield` preserves `domainSchedule`. -/
theorem handleYield_preserves_domainSchedule
    (st st' : SystemState)
    (hStep : handleYield st = .ok ((), st')) :
    st'.scheduler.domainSchedule = st.scheduler.domainSchedule := by
  unfold handleYield at hStep
  cases hCur : st.scheduler.current with
  | none => simp [hCur] at hStep
  | some tid =>
    simp [hCur] at hStep
    split at hStep
    · rename_i tcb _
      have := schedule_preserves_domainSchedule _ _ hStep
      simp at this; exact this
    · simp at hStep

/-- X2-C: `timerTick` preserves `domainSchedule`. -/
theorem timerTick_preserves_domainSchedule
    (st st' : SystemState)
    (hStep : timerTick st = .ok ((), st')) :
    st'.scheduler.domainSchedule = st.scheduler.domainSchedule := by
  unfold timerTick at hStep
  cases hCur : st.scheduler.current with
  | none =>
    simp [hCur] at hStep; obtain ⟨_, rfl⟩ := hStep; rfl
  | some tid =>
    simp [hCur] at hStep
    split at hStep
    · rename_i tcb _
      split at hStep
      · -- Time-slice expired: schedule is called
        have hSched := schedule_preserves_domainSchedule _ _ hStep
        simp at hSched; exact hSched
      · -- Time-slice not expired: only objects/machine changed
        simp at hStep; obtain ⟨_, rfl⟩ := hStep; rfl
    · simp at hStep

/-- WS-H6/WS-H12b/WS-H12e/V5-H/X2-A: `switchDomain` preserves the full scheduler invariant bundle.
    V5-H: Now includes `domainTimeRemainingPositive` as the 8th conjunct.
    X2-A: `domainScheduleEntriesPositive` as the 9th conjunct (frame lemma — `domainSchedule`
    immutable at runtime). `hEntriesPos` is now extracted from the bundle instead of
    being required as an external hypothesis. -/
theorem switchDomain_preserves_schedulerInvariantBundleFull
    (st st' : SystemState)
    (hInv : schedulerInvariantBundleFull st)
    (hObjInv : st.objects.invExt)
    (hStep : switchDomain st = .ok ((), st')) :
    schedulerInvariantBundleFull st' := by
  rcases hInv with ⟨hBase, hTS, hCurTS, hEDF, hCtx, hRunnTcb, hPM, hDTR, hEntries⟩
  have hEntriesPos := hEntries
  exact ⟨switchDomain_preserves_schedulerInvariantBundle st st' hBase hStep,
         switchDomain_preserves_timeSlicePositive st st' hTS hCurTS hObjInv hStep,
         switchDomain_preserves_currentTimeSlicePositive st st' hCurTS hStep,
         switchDomain_preserves_edfCurrentHasEarliestDeadline st st' hEDF hStep,
         switchDomain_preserves_contextMatchesCurrent st st' hCtx hStep,
         switchDomain_preserves_runnableThreadsAreTCBs st st' hRunnTcb hObjInv hStep,
         switchDomain_preserves_schedulerPriorityMatch st st' hBase hPM hObjInv hStep,
         switchDomain_preserves_domainTimeRemainingPositive st st' hDTR hEntriesPos hStep,
         fun e hMem => hEntries e (switchDomain_preserves_domainSchedule st st' hStep ▸ hMem)⟩

/-- WS-H6: `setCurrentThread (some tid)` preserves EDF when the selected thread
satisfies the EDF deadline ordering among same-domain/same-priority candidates. -/
theorem setCurrentThread_some_preserves_edfCurrentHasEarliestDeadline
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (tcbSel : TCB)
    (hObj : st.objects[tid.toObjId]? = some (.tcb tcbSel))
    (hEdfLocal : ∀ t, t ∈ st.scheduler.runnable →
      match st.objects[t.toObjId]? with
      | some (.tcb tcb) =>
          tcb.domain = tcbSel.domain →
          effectiveRunQueuePriority tcb = effectiveRunQueuePriority tcbSel →
          tcb.priority = tcbSel.priority →
          tcbSel.deadline.toNat = 0 ∨
            (tcb.deadline.toNat = 0 ∨ tcbSel.deadline.toNat ≤ tcb.deadline.toNat)
      | _ => True)
    (hStep : setCurrentThread (some tid) st = .ok ((), st')) :
    edfCurrentHasEarliestDeadline st' := by
  unfold setCurrentThread at hStep
  cases hStep
  unfold edfCurrentHasEarliestDeadline
  simp only [hObj]
  exact hEdfLocal

/-- WS-H6: If `chooseBestRunnableBy` returns `some (resTid, resPrio, resDl)`, then
`objects resTid.toObjId = some (.tcb tcb)` for some TCB. -/
private theorem chooseBestRunnableBy_result_fields
    (objects : SeLe4n.ObjId → Option KernelObject)
    (eligible : TCB → Bool)
    (runnable : List SeLe4n.ThreadId)
    (init : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline))
    (resTid : SeLe4n.ThreadId) (resPrio : SeLe4n.Priority) (resDl : SeLe4n.Deadline)
    (hOk : chooseBestRunnableBy objects eligible runnable init =
      .ok (some (resTid, resPrio, resDl)))
    (hInit : ∀ iTid iPrio iDl, init = some (iTid, iPrio, iDl) →
      ∃ itcb, objects iTid.toObjId = some (.tcb itcb) ∧
        itcb.priority = iPrio ∧ itcb.deadline = iDl) :
    ∃ tcb, objects resTid.toObjId = some (.tcb tcb) ∧
      tcb.priority = resPrio ∧ tcb.deadline = resDl := by
  induction runnable generalizing init with
  | nil =>
      unfold chooseBestRunnableBy at hOk
      simp at hOk
      cases hOk
      exact hInit resTid resPrio resDl rfl
  | cons hd tl ih =>
      unfold chooseBestRunnableBy at hOk
      cases hHdObj : objects hd.toObjId with
      | none => simp [hHdObj] at hOk
      | some obj =>
          cases obj with
          | tcb hdTcb =>
              simp only [hHdObj] at hOk
              cases hElig : eligible hdTcb with
              | false =>
                  simp only [hElig] at hOk
                  exact ih init hOk hInit
              | true =>
                  simp only [hElig, ↓reduceIte] at hOk
                  cases init with
                  | none =>
                      exact ih (some (hd, hdTcb.priority, hdTcb.deadline)) hOk (by
                        intro iTid iPrio iDl hEq
                        simp at hEq; obtain ⟨rfl, rfl, rfl⟩ := hEq
                        exact ⟨hdTcb, hHdObj, rfl, rfl⟩)
                  | some triple =>
                      obtain ⟨initTid, initPrio, initDl⟩ := triple
                      dsimp only at hOk
                      cases hBeat : isBetterCandidate initPrio initDl hdTcb.priority hdTcb.deadline with
                      | true =>
                          simp only [hBeat, ite_true] at hOk
                          exact ih (some (hd, hdTcb.priority, hdTcb.deadline)) hOk (by
                            intro iTid iPrio iDl hEq
                            simp at hEq; obtain ⟨rfl, rfl, rfl⟩ := hEq
                            exact ⟨hdTcb, hHdObj, rfl, rfl⟩)
                      | false =>
                          simp only [hBeat] at hOk
                          exact ih (some (initTid, initPrio, initDl)) hOk hInit
          | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ =>
              simp [hHdObj] at hOk

/-- WS-H6: Result of `chooseBestRunnableBy` (init = none) is a member of the scanned list. -/
private theorem chooseBestRunnableBy_result_mem_aux
    (objects : SeLe4n.ObjId → Option KernelObject)
    (eligible : TCB → Bool)
    (list : List SeLe4n.ThreadId)
    (init : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline))
    (resTid : SeLe4n.ThreadId) (resPrio : SeLe4n.Priority) (resDl : SeLe4n.Deadline)
    (hOk : chooseBestRunnableBy objects eligible list init =
      .ok (some (resTid, resPrio, resDl)))
    (hAllTcb : ∀ t, t ∈ list → ∃ tcb, objects t.toObjId = some (.tcb tcb)) :
    resTid ∈ list ∨ (∃ ip id, init = some (resTid, ip, id)) := by
  induction list generalizing init with
  | nil =>
    unfold chooseBestRunnableBy at hOk
    simp at hOk; cases hOk
    exact Or.inr ⟨resPrio, resDl, rfl⟩
  | cons hd tl ih =>
    unfold chooseBestRunnableBy at hOk
    have hAllTl : ∀ t, t ∈ tl → ∃ tcb, objects t.toObjId = some (.tcb tcb) :=
      fun t ht => hAllTcb t (List.mem_cons.mpr (Or.inr ht))
    cases hHdObj : objects hd.toObjId with
    | none => simp [hHdObj] at hOk
    | some obj =>
      cases obj with
      | tcb hdTcb =>
        simp only [hHdObj] at hOk
        cases hElig : eligible hdTcb with
        | false =>
          simp only [hElig] at hOk
          have := ih init hOk hAllTl
          exact this.elim (fun h => Or.inl (List.mem_cons.mpr (Or.inr h))) Or.inr
        | true =>
          simp only [hElig, ↓reduceIte] at hOk
          cases init with
          | none =>
            have := ih (some (hd, hdTcb.priority, hdTcb.deadline)) hOk hAllTl
            rcases this with hTl | ⟨ip, id, hInit⟩
            · exact Or.inl (List.mem_cons.mpr (Or.inr hTl))
            · simp at hInit; obtain ⟨rfl, _, _⟩ := hInit
              exact Or.inl (List.mem_cons.mpr (Or.inl rfl))
          | some triple =>
            obtain ⟨initTid, initPrio, initDl⟩ := triple
            dsimp only at hOk
            cases hBeat : isBetterCandidate initPrio initDl hdTcb.priority hdTcb.deadline with
            | true =>
              simp only [hBeat, ite_true] at hOk
              have := ih (some (hd, hdTcb.priority, hdTcb.deadline)) hOk hAllTl
              rcases this with hTl | ⟨ip, id, hInit⟩
              · exact Or.inl (List.mem_cons.mpr (Or.inr hTl))
              · simp at hInit; obtain ⟨rfl, _, _⟩ := hInit
                exact Or.inl (List.mem_cons.mpr (Or.inl rfl))
            | false =>
              simp only [hBeat] at hOk
              have := ih (some (initTid, initPrio, initDl)) hOk hAllTl
              exact this.elim (fun h => Or.inl (List.mem_cons.mpr (Or.inr h))) Or.inr
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ =>
        simp [hHdObj] at hOk

private theorem chooseBestRunnableBy_result_mem
    (objects : SeLe4n.ObjId → Option KernelObject)
    (eligible : TCB → Bool)
    (list : List SeLe4n.ThreadId)
    (resTid : SeLe4n.ThreadId) (resPrio : SeLe4n.Priority) (resDl : SeLe4n.Deadline)
    (hOk : chooseBestRunnableBy objects eligible list none =
      .ok (some (resTid, resPrio, resDl)))
    (hAllTcb : ∀ t, t ∈ list → ∃ tcb, objects t.toObjId = some (.tcb tcb)) :
    resTid ∈ list := by
  have := chooseBestRunnableBy_result_mem_aux objects eligible list none
    resTid resPrio resDl hOk hAllTcb
  rcases this with hMem | ⟨_, _, hNone⟩
  · exact hMem
  · exact absurd hNone (by simp)

/-- WS-H6/WS-H12b: Bridge from `chooseBestInBucket` to the EDF deadline ordering.

Given RunQueue well-formedness and priority-match, the result of
`chooseBestInBucket` is EDF-optimal among all domain-eligible runnable threads
at the same priority level.

WS-H12b: The EDF property is stated over a **subset** of the runnable list
(the post-dequeue queue), but `chooseBestInBucket` was called on the full
pre-dequeue queue. Since the post-dequeue queue is a subset, the universal
quantifier is weaker (holds trivially for the removed element). -/
private theorem chooseBestInBucket_edf_bridge
    (st : SystemState)
    (tid : SeLe4n.ThreadId) (resPrio : SeLe4n.Priority) (resDl : SeLe4n.Deadline)
    (tcbSel : TCB)
    (hwf : RunQueue.wellFormed st.scheduler.runQueue)
    (hpm : schedulerPriorityMatch st)
    (hDomEq : tcbSel.domain = st.scheduler.activeDomain)
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hResult : chooseBestInBucket st.objects.get? st.scheduler.runQueue
      st.scheduler.activeDomain = .ok (some (tid, resPrio, resDl)))
    (hObj : st.objects[tid.toObjId]? = some (.tcb tcbSel)) :
    -- EDF property over the DEQUEUED runnable set (post-remove)
    ∀ t, t ∈ (st.scheduler.runQueue.remove tid).toList →
      match st.objects[t.toObjId]? with
      | some (.tcb tcb) =>
          tcb.domain = tcbSel.domain →
          effectiveRunQueuePriority tcb = effectiveRunQueuePriority tcbSel →
          tcb.priority = tcbSel.priority →
          tcbSel.deadline.toNat = 0 ∨
            (tcb.deadline.toNat = 0 ∨ tcbSel.deadline.toNat ≤ tcb.deadline.toNat)
      | _ => True := by
  intro t hMemDq
  -- t ∈ (rq.remove tid).toList → t ∈ rq.toList (subset)
  have hMemOrig : t ∈ st.scheduler.runnable := by
    simp only [SchedulerState.runnable]
    exact (RunQueue.mem_toList_iff_mem _ t).mpr
      ((RunQueue.mem_remove st.scheduler.runQueue tid t).mp
        ((RunQueue.mem_toList_iff_mem _ t).mp hMemDq)).1
  -- Convert to objects.get?
  have hAllTcbGet : ∀ u, u ∈ st.scheduler.runQueue.toList →
      ∃ utcb, st.objects.get? u.toObjId = some (.tcb utcb) := by
    intro u hMu
    obtain ⟨utcb, hutcb⟩ := hAllTcb u (by simpa [SchedulerState.runnable] using hMu)
    exact ⟨utcb, hutcb⟩
  have hObjGet : st.objects.get? tid.toObjId = some (.tcb tcbSel) := hObj
  -- Domain-eligibility helper
  have eligOfDom : ∀ (tcb : TCB), tcb.domain = tcbSel.domain →
      (fun tc : TCB => tc.domain == st.scheduler.activeDomain) tcb = true := by
    intro tcb htDom; simp; rw [htDom, hDomEq]
  -- Unfold chooseBestInBucket
  unfold chooseBestInBucket at hResult
  cases hBucket : chooseBestRunnableInDomain st.objects.get?
      st.scheduler.runQueue.maxPriorityBucket st.scheduler.activeDomain none with
  | error e => simp [hBucket] at hResult
  | ok bestB =>
    cases bestB with
    | none =>
      -- ── Full-scan fallback ──
      simp only [hBucket] at hResult
      cases hFull : chooseBestRunnableInDomain st.objects.get?
          st.scheduler.runQueue.toList st.scheduler.activeDomain none with
      | error e => simp [hFull] at hResult
      | ok bestF =>
        cases bestF with
        | none => simp [hFull] at hResult
        | some triple =>
          simp only [hFull] at hResult
          have hTripleEq : triple = (tid, resPrio, resDl) := by
            simp at hResult; exact hResult
          subst hTripleEq
          have hFields := chooseBestRunnableBy_result_fields st.objects.get?
            (fun tc => tc.domain == st.scheduler.activeDomain)
            st.scheduler.runQueue.toList none tid resPrio resDl hFull
            (by intro _ _ _ h; simp at h)
          obtain ⟨resTcb, hResTcb, hResPrio, hResDl⟩ := hFields
          rw [hObjGet] at hResTcb; cases hResTcb; subst hResPrio; subst hResDl
          cases hTObj : st.objects[t.toObjId]? with
          | none => simp
          | some tObj =>
            cases tObj with
            | tcb tcb =>
              intro htDom _htEffPrio htPrio
              have hTObjGet : st.objects.get? t.toObjId = some (.tcb tcb) := hTObj
              have hMemList : t ∈ st.scheduler.runQueue.toList := by
                simpa [SchedulerState.runnable] using hMemOrig
              have hOpt := chooseBestRunnableBy_optimal st.objects.get?
                (fun tc => tc.domain == st.scheduler.activeDomain)
                st.scheduler.runQueue.toList tid tcbSel.priority tcbSel.deadline
                hFull hAllTcbGet
              have hNoBetter := hOpt t hMemList tcb hTObjGet (eligOfDom tcb htDom)
              rw [htPrio] at hNoBetter
              exact noBetter_implies_edf tcbSel.deadline tcb.deadline tcbSel.priority hNoBetter
            | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ => simp
    | some triple =>
      -- ── Bucket success ──
      simp only [hBucket] at hResult
      have hTripleEq : triple = (tid, resPrio, resDl) := by
        simp at hResult; exact hResult
      subst hTripleEq
      have hBucketAllTcb : ∀ u, u ∈ st.scheduler.runQueue.maxPriorityBucket →
          ∃ utcb, st.objects.get? u.toObjId = some (.tcb utcb) := by
        intro u hU
        have hURq := RunQueue.maxPriorityBucket_subset st.scheduler.runQueue hwf u hU
        obtain ⟨utcb, hutcb⟩ := hAllTcb u (by
          simpa [SchedulerState.runnable] using
            RunQueue.membership_implies_flat st.scheduler.runQueue u hURq)
        exact ⟨utcb, hutcb⟩
      have hFields := chooseBestRunnableBy_result_fields st.objects.get?
        (fun tc => tc.domain == st.scheduler.activeDomain)
        st.scheduler.runQueue.maxPriorityBucket none tid resPrio resDl hBucket
        (by intro _ _ _ h; simp at h)
      obtain ⟨resTcb, hResTcb, hResPrio, hResDl⟩ := hFields
      rw [hObjGet] at hResTcb; cases hResTcb; subst hResPrio; subst hResDl
      have hTidInBucket : tid ∈ st.scheduler.runQueue.maxPriorityBucket :=
        chooseBestRunnableBy_result_mem st.objects.get?
          (fun tc => tc.domain == st.scheduler.activeDomain)
          st.scheduler.runQueue.maxPriorityBucket tid tcbSel.priority tcbSel.deadline
          hBucket hBucketAllTcb
      obtain ⟨maxPrio, hMP, hTidTP⟩ :=
        RunQueue.maxPriorityBucket_threadPriority st.scheduler.runQueue hwf tid hTidInBucket
      have hTidMem := RunQueue.maxPriorityBucket_subset st.scheduler.runQueue hwf tid hTidInBucket
      have hPMTid := hpm tid hTidMem
      simp only [hObj] at hPMTid
      have hMaxEqPrio : maxPrio = effectiveRunQueuePriority tcbSel := Option.some.inj (hTidTP.symm.trans hPMTid)
      cases hTObj : st.objects[t.toObjId]? with
      | none => simp
      | some tObj =>
        cases tObj with
        | tcb tcb =>
          intro htDom htEffPrio htPrio
          have hTInRq : t ∈ st.scheduler.runQueue := by
            rw [RunQueue.mem_iff_contains]
            exact st.scheduler.runQueue.flat_wf t
              (by simpa [SchedulerState.runnable] using hMemOrig)
          have hPMt := hpm t hTInRq; simp only [hTObj] at hPMt
          -- AI3-A: htEffPrio gives effectiveRunQueuePriority tcb = effectiveRunQueuePriority tcbSel.
          -- Combined with hPMt and hMaxEqPrio, this yields threadPriority[t]? = some maxPrio,
          -- placing t in the maxPriorityBucket alongside tid.
          have hTTP : st.scheduler.runQueue.threadPriority[t]? = some maxPrio :=
            hPMt.trans (congrArg some (htEffPrio.trans hMaxEqPrio.symm))
          have hTInBucket :=
            RunQueue.mem_maxPriorityBucket_of_threadPriority st.scheduler.runQueue hwf
              t maxPrio hTInRq hTTP hMP
          have hTObjGet : st.objects.get? t.toObjId = some (.tcb tcb) := hTObj
          have hOpt := chooseBestRunnableBy_optimal st.objects.get?
            (fun tc => tc.domain == st.scheduler.activeDomain)
            st.scheduler.runQueue.maxPriorityBucket tid tcbSel.priority tcbSel.deadline
            hBucket hBucketAllTcb
          have hNoBetter := hOpt t hTInBucket tcb hTObjGet (eligOfDom tcb htDom)
          rw [htPrio] at hNoBetter
          exact noBetter_implies_edf tcbSel.deadline tcb.deadline tcbSel.priority hNoBetter
        | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ => simp

/-- WS-H6/WS-H12b: `schedule` preserves `edfCurrentHasEarliestDeadline`.

When schedule selects `none`, EDF is trivially `True`. When schedule selects
`some tid`, the EDF property follows from `chooseBestInBucket_edf_bridge`.

WS-H12b: The dequeue step means the post-state's runnable list excludes
the dispatched thread. The EDF bridge is updated accordingly. -/
private theorem schedule_preserves_edfCurrentHasEarliestDeadline
    (st st' : SystemState)
    (hwf : RunQueue.wellFormed st.scheduler.runQueue)
    (hpm : schedulerPriorityMatch st)
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStep : schedule st = .ok ((), st')) :
    edfCurrentHasEarliestDeadline st' := by
  unfold schedule at hStep
  simp only [chooseThread] at hStep
  cases hCIB : chooseBestInBucket st.objects.get? st.scheduler.runQueue
      st.scheduler.activeDomain with
  | error e => simp [hCIB] at hStep
  | ok cibRes =>
    simp only [hCIB] at hStep
    cases cibRes with
    | none =>
      exact setCurrentThread_none_preserves_edfCurrentHasEarliestDeadline
        (saveOutgoingContext st) st' hStep
    | some triple =>
      obtain ⟨tid, resPrio, resDl⟩ := triple
      simp at hStep
      cases hObj : st.objects[tid.toObjId]? with
      | none => simp [hObj] at hStep
      | some obj =>
        cases obj with
        | tcb tcbSel =>
          simp only [hObj] at hStep
          by_cases hSchedOk : st.scheduler.runQueue.contains tid = true ∧
              tcbSel.domain = st.scheduler.activeDomain
          · simp only [hSchedOk] at hStep
            -- After dequeue + context switch, use the subst approach
            have hSet := hStep
            simp [setCurrentThread] at hSet
            subst hSet
            -- edfCurrentHasEarliestDeadline unfolds to check current/runnable/objects
            have hBridge := chooseBestInBucket_edf_bridge st tid resPrio resDl tcbSel
              hwf hpm hSchedOk.2 hAllTcb hCIB hObj
            simp only [edfCurrentHasEarliestDeadline]
            -- Get the saved TCB and its field preservation
            have ⟨tcbSel', hTcbSel', hDomSel, hPriSel, hDlSel, _, hPipSel, hBindSel⟩ :=
              saveOutgoingContext_tcb_fields st tid.toObjId tcbSel hObj hObjInv
            simp [hTcbSel']
            intro t hMem
            -- Simplify hMem: scheduler went through restoreIncomingContext + saveOutgoingContext
            -- but both preserve scheduler, so reduce to st.scheduler.runQueue.remove tid
            simp only [SchedulerState.runnable] at hMem
            have hMemOrig : t ∈ { st.scheduler with runQueue := st.scheduler.runQueue.remove tid }.runnable := by
              simpa [SchedulerState.runnable] using hMem
            have hBridgeT := hBridge t hMemOrig
            -- Case split on whether t has a TCB in original state
            -- For non-TCB cases, we show saveOutgoingContext preserves the lookup:
            -- saveOutgoingContext only inserts at outTid.toObjId where st.objects has a TCB,
            -- so if st.objects[t.toObjId]? has no TCB, neither does the saved state.
            cases hObjT : st.objects[t.toObjId]? with
            | none =>
                -- No TCB at t.toObjId → saveOutgoingContext preserves the lookup
                have hSame := saveOutgoingContext_preserves_non_tcb_lookup st t.toObjId
                  (fun tcb h => by simp [hObjT] at h) hObjInv
                simp [hSame, hObjT]
            | some objT =>
                cases objT with
                | tcb tcbT =>
                    have ⟨tcbT', hTcbT', hDomT, hPriT, hDlT, _, hPipT, hBindT⟩ :=
                      saveOutgoingContext_tcb_fields st t.toObjId tcbT hObjT hObjInv
                    simp [hTcbT']
                    simp [hObjT] at hBridgeT
                    intro hDomEq hEffPriEq hPriEq
                    have hDomOrig : tcbT.domain = tcbSel.domain := by
                      rw [← hDomSel, ← hDomT]; exact hDomEq
                    have hEffPriOrig : effectiveRunQueuePriority tcbT = effectiveRunQueuePriority tcbSel := by
                      -- AI3-A: Bridge effective priorities through saveOutgoingContext.
                      -- tcbT' and tcbSel' have same priority/pipBoost as tcbT and tcbSel.
                      simp only [effectiveRunQueuePriority, hPriT, hPipT, hPriSel, hPipSel] at hEffPriEq ⊢
                      exact hEffPriEq
                    have hPriOrig : tcbT.priority = tcbSel.priority := by
                      rw [← hPriSel, ← hPriT]; exact hPriEq
                    have hB := hBridgeT hDomOrig hEffPriOrig hPriOrig
                    rw [hDlSel, hDlT]; exact hB
                | _ =>
                    -- Non-TCB at t.toObjId → saveOutgoingContext preserves the lookup
                    have hSame := saveOutgoingContext_preserves_non_tcb_lookup st t.toObjId
                      (fun tcb h => by rw [hObjT] at h; cases h) hObjInv
                    rw [hSame, hObjT]; simp [hObjT] at hBridgeT ⊢
          · exfalso; simp [hSchedOk] at hStep
        | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ =>
          simp [hObj] at hStep

-- W2-H (L-3): 1.6M heartbeats — highest in the codebase. Inherent complexity:
-- handleYield composes enqueue + schedule, each requiring full EDF reasoning.
-- The proof unfolds both operations and reasons about run-queue membership,
-- priority ordering, and deadline comparison across the composed transition.
-- Factoring into sub-lemmas was attempted (V7) but the intermediate state
-- between enqueue and schedule requires carrying all scheduler hypotheses,
-- preventing meaningful heartbeat reduction.
-- AF5-J (AF-31): High heartbeats (1.6M for handleYield, 800K for timerTick
-- below) are caused by EDF reasoning requiring full run queue analysis after
-- enqueue + schedule composition. Potential mitigations:
-- (1) Extract intermediate lemmas to reduce per-proof complexity
-- (2) Introduce custom tactics for EDF property threading
-- (3) Accept and pin Lean toolchain version during release cycles
-- Tracked for post-release maintenance.
set_option maxHeartbeats 1600000 in
/-- WS-H6/WS-H12b: `handleYield` preserves `edfCurrentHasEarliestDeadline`.

Under dequeue-on-dispatch, `handleYield` inserts the current thread back
into the run queue and then calls `schedule`, which re-selects the best
candidate from scratch. The EDF property is re-established by the
`schedule` call. -/
private theorem handleYield_preserves_edfCurrentHasEarliestDeadline
    (st st' : SystemState)
    (hwf : RunQueue.wellFormed st.scheduler.runQueue)
    (hpm : schedulerPriorityMatch st)
    (hQCC : queueCurrentConsistent st.scheduler)
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStep : handleYield st = .ok ((), st')) :
    edfCurrentHasEarliestDeadline st' := by
  unfold handleYield at hStep
  cases hCur : st.scheduler.current with
  | none =>
    -- V5-F: handleYield now returns .error .invalidArgument when current = none
    simp only [hCur] at hStep; cases hStep
  | some curTid =>
    simp only [hCur] at hStep
    cases hObj : st.objects[curTid.toObjId]? with
    | none => simp [hObj] at hStep
    | some obj =>
      cases obj with
      | tcb tcb =>
        simp only [hObj] at hStep
        -- After insert+rotateToBack, need wellFormed and prioMatch for the new state
        have hNotMem : curTid ∉ st.scheduler.runQueue := by
          have := hQCC; simp [queueCurrentConsistent, hCur] at this
          intro h; exact this ((RunQueue.mem_toList_iff_mem st.scheduler.runQueue curTid).2 h)
        -- Break the proof into steps to avoid timeout
        have hwf' : RunQueue.wellFormed ((st.scheduler.runQueue.insert curTid (effectiveRunQueuePriority tcb)).rotateToBack curTid) :=
          RunQueue.rotateToBack_preserves_wellFormed _ (RunQueue.insert_preserves_wellFormed st.scheduler.runQueue hwf curTid (effectiveRunQueuePriority tcb)) curTid
        have hpm' : schedulerPriorityMatch
            { st with scheduler := { st.scheduler with
                runQueue := (st.scheduler.runQueue.insert curTid (effectiveRunQueuePriority tcb)).rotateToBack curTid } } := by
          intro t hMem
          have hMemIns : t ∈ st.scheduler.runQueue.insert curTid (effectiveRunQueuePriority tcb) :=
            (RunQueue.mem_rotateToBack _ curTid t).mp hMem
          rw [RunQueue.mem_insert] at hMemIns
          simp only [RunQueue.rotateToBack_threadPriority, RunQueue.insert_threadPriority,
            show (st.scheduler.runQueue.contains curTid) = false from by
              cases h : st.scheduler.runQueue.contains curTid
              · rfl
              · exact absurd h hNotMem,
            Bool.false_eq_true, ↓reduceIte]
          cases hMemIns with
          | inl hOld =>
            have hNeq : curTid ≠ t := fun h => hNotMem (h ▸ hOld)
            have hBEq : (curTid == t) = false := by
              cases h : (curTid == t) <;> simp_all
            simp only [RHTable_getElem?_eq_get?]
            rw [RHTable_getElem?_insert st.scheduler.runQueue.threadPriority _ _ st.scheduler.runQueue.threadPrio_invExtK.1]
            simp only [hBEq, Bool.false_eq_true, ↓reduceIte]
            exact hpm t hOld
          | inr hEq =>
            subst hEq
            simp only [RHTable_getElem?_eq_get?]
            rw [RHTable_getElem?_insert st.scheduler.runQueue.threadPriority _ _ st.scheduler.runQueue.threadPrio_invExtK.1]
            simp only [beq_self_eq_true, ↓reduceIte]
            simp only [RHTable_getElem?_eq_get?] at hObj; rw [hObj]
        have hAllTcb' : ∀ t, t ∈ { st with scheduler := { st.scheduler with
            runQueue := (st.scheduler.runQueue.insert curTid (effectiveRunQueuePriority tcb)).rotateToBack curTid } }.scheduler.runnable →
            ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb) := by
          intro t hMem
          simp only [SchedulerState.runnable, RunQueue.toList] at hMem
          have hMemIns : t ∈ st.scheduler.runQueue.insert curTid (effectiveRunQueuePriority tcb) :=
            (RunQueue.mem_rotateToBack _ curTid t).mp ((RunQueue.mem_toList_iff_mem _ t).mp hMem)
          rw [RunQueue.mem_insert] at hMemIns
          cases hMemIns with
          | inl hOld => exact hAllTcb t (by simp only [SchedulerState.runnable]; exact (RunQueue.mem_toList_iff_mem _ t).mpr hOld)
          | inr hEq => subst hEq; exact ⟨tcb, hObj⟩
        rw [← hCur] at hStep
        let st_mid : SystemState := { st with scheduler := { st.scheduler with
            runQueue := (st.scheduler.runQueue.insert curTid (effectiveRunQueuePriority tcb)).rotateToBack curTid } }
        exact schedule_preserves_edfCurrentHasEarliestDeadline st_mid st' hwf' hpm' hAllTcb' (show st_mid.objects.invExt from hObjInv) hStep
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep

-- W2-H (L-3): 800K heartbeats — timerTick composes domain time decrement +
-- conditional reschedule. Same structural complexity as handleYield above but
-- with an additional branch (time remaining > 0 → no reschedule needed).
set_option maxHeartbeats 800000 in
/-- WS-H6/WS-H12b: `timerTick` preserves `edfCurrentHasEarliestDeadline`.

- **No current thread**: scheduler unchanged, EDF trivially holds.
- **Time-slice not expired**: only the TCB's `timeSlice` field is
  decremented; `scheduler.current` and thread deadlines are unchanged,
  so EDF is preserved.
- **Time-slice expired**: TCB time-slice reset, re-enqueue via insert, and
  `schedule` call re-establishes EDF from scratch. -/
private theorem timerTick_preserves_edfCurrentHasEarliestDeadline
    (st st' : SystemState)
    (hwf : RunQueue.wellFormed st.scheduler.runQueue)
    (hpm : schedulerPriorityMatch st)
    (hQCC : queueCurrentConsistent st.scheduler)
    (hEdf : edfCurrentHasEarliestDeadline st)
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStep : timerTick st = .ok ((), st')) :
    edfCurrentHasEarliestDeadline st' := by
  unfold timerTick at hStep
  cases hCur : st.scheduler.current with
  | none =>
    simp [hCur] at hStep; cases hStep
    unfold edfCurrentHasEarliestDeadline; simp [hCur]
  | some curTid =>
    simp only [hCur] at hStep
    cases hObj : st.objects[curTid.toObjId]? with
    | none => simp [hObj] at hStep
    | some obj =>
      cases obj with
      | tcb curTcb =>
        simp only [hObj] at hStep
        by_cases hExpire : curTcb.timeSlice ≤ 1
        · -- Time-slice expired: reset, re-enqueue, reschedule
          rw [if_pos hExpire] at hStep
          -- curTid ∉ runQueue (by QCC)
          have hNotMem : curTid ∉ st.scheduler.runQueue := by
            have := hQCC; simp [queueCurrentConsistent, hCur] at this
            intro h; exact this ((RunQueue.mem_toList_iff_mem st.scheduler.runQueue curTid).2 h)
          -- Break proof into steps to avoid timeout
          have hwf' : RunQueue.wellFormed (st.scheduler.runQueue.insert curTid (effectiveRunQueuePriority curTcb)) :=
            RunQueue.insert_preserves_wellFormed st.scheduler.runQueue hwf curTid (effectiveRunQueuePriority curTcb)
          have hContainsFalse : st.scheduler.runQueue.contains curTid = false := by
            cases h : st.scheduler.runQueue.contains curTid
            · rfl
            · exact absurd h hNotMem
          have hpm' : schedulerPriorityMatch
              { st with
                objects := st.objects.insert curTid.toObjId (.tcb { curTcb with timeSlice := st.scheduler.configDefaultTimeSlice })
                machine := tick st.machine
                scheduler := { st.scheduler with runQueue := st.scheduler.runQueue.insert curTid (effectiveRunQueuePriority curTcb) } } := by
            intro t hMem
            simp only [RunQueue.insert_threadPriority, hContainsFalse, Bool.false_eq_true, ↓reduceIte]
            rw [RunQueue.mem_insert] at hMem
            cases hMem with
            | inl hOld =>
              have hNeq : curTid ≠ t := fun h => hNotMem (h ▸ hOld)
              have hBEq : (curTid == t) = false := by
                cases h : (curTid == t) <;> simp_all
              have hObjBEq : (curTid.toObjId == t.toObjId) = false := by
                cases h : (curTid.toObjId == t.toObjId) with
                | false => rfl
                | true => exact absurd (ThreadId.toObjId_injective curTid t (eq_of_beq h)) hNeq
              -- objects side: insert-ne, threadPriority side: insert-ne
              simp only [RHTable_getElem?_eq_get?]
              rw [RHTable_getElem?_insert st.objects _ _ hObjInv,
                  RHTable_getElem?_insert st.scheduler.runQueue.threadPriority _ _ st.scheduler.runQueue.threadPrio_invExtK.1]
              simp only [hObjBEq, hBEq, Bool.false_eq_true, ↓reduceIte]
              exact hpm t hOld
            | inr hEq =>
              subst hEq
              -- threadPriority side: (rq.threadPriority.insert t prio).get? t = some prio
              simp only [RHTable_getElem?_eq_get?]
              rw [RHTable_getElem?_insert st.scheduler.runQueue.threadPriority _ _ st.scheduler.runQueue.threadPrio_invExtK.1]
              simp only [beq_self_eq_true, ite_true]
              -- objects side: (st.objects.insert t.toObjId (.tcb {...})).get? t.toObjId = some (.tcb {...})
              rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
              simp only [beq_self_eq_true, ite_true]
              -- AI3-A: effectiveRunQueuePriority only depends on priority + pipBoost,
              -- both preserved by the timeSlice-only update
              simp [effectiveRunQueuePriority]
          have hAllTcb' : ∀ t, t ∈ { st with
              objects := st.objects.insert curTid.toObjId (.tcb { curTcb with timeSlice := st.scheduler.configDefaultTimeSlice })
              machine := tick st.machine
              scheduler := { st.scheduler with runQueue := st.scheduler.runQueue.insert curTid (effectiveRunQueuePriority curTcb) } }.scheduler.runnable →
              ∃ tcb, (st.objects.insert curTid.toObjId (.tcb { curTcb with timeSlice := st.scheduler.configDefaultTimeSlice }))[t.toObjId]? = some (.tcb tcb) := by
            intro t hMem
            simp only [SchedulerState.runnable, RunQueue.toList] at hMem
            have hMemIns := (RunQueue.mem_toList_iff_mem _ t).mp hMem
            rw [RunQueue.mem_insert] at hMemIns
            cases hMemIns with
            | inl hOld =>
              by_cases hEq : t = curTid
              · subst hEq; exact absurd hOld hNotMem
              · have ⟨tcbOrig, hTcbOrig⟩ := hAllTcb t (by
                  simp only [SchedulerState.runnable]; exact (RunQueue.mem_toList_iff_mem _ t).mpr hOld)
                simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv, threadId_ne_objId_beq_false curTid t hEq]
                exact ⟨tcbOrig, hTcbOrig⟩
            | inr hEq =>
              subst hEq
              simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]; simp
          have hObjInv' := RHTable_insert_preserves_invExt st.objects curTid.toObjId (KernelObject.tcb { curTcb with timeSlice := st.scheduler.configDefaultTimeSlice }) hObjInv
          rw [← hCur] at hStep
          exact schedule_preserves_edfCurrentHasEarliestDeadline _ st' hwf' hpm' hAllTcb' hObjInv' hStep
        · -- Time-slice not expired: only timeSlice changes
          rw [if_neg hExpire] at hStep
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
          subst hStep
          unfold edfCurrentHasEarliestDeadline at hEdf ⊢
          simp only [hCur] at hEdf ⊢
          rw [hObj] at hEdf
          simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
          simp only [beq_self_eq_true, ite_true]
          intro t hMem
          specialize hEdf t hMem
          by_cases hEq : curTid.toObjId == t.toObjId
          · rw [RHTable_getElem?_insert st.objects _ _ hObjInv]; simp only [hEq, ite_true]
            intro _ _ _; exact Or.inr (Or.inr (Nat.le_refl _))
          · have hEqF : (curTid.toObjId == t.toObjId) = false := Bool.eq_false_iff.mpr hEq
            rw [RHTable_getElem?_insert st.objects _ _ hObjInv]; simp only [hEqF]; exact hEdf
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ =>
        simp [hObj] at hStep

-- ============================================================================
-- WS-H12c/H-03: contextMatchesCurrent preservation proofs
-- ============================================================================

/-- WS-H12c/H-03: `schedule` establishes (and therefore preserves)
`contextMatchesCurrent`. The inline context switch in `schedule` atomically
saves the outgoing thread's registers and restores the incoming thread's
registers, ensuring machine.regs = currentThread.registerContext. -/
private theorem schedule_preserves_contextMatchesCurrent
    (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : schedule st = .ok ((), st')) :
    contextMatchesCurrent st' := by
  unfold schedule at hStep
  cases hChoose : chooseThread st with
  | error e => simp [hChoose] at hStep
  | ok pick =>
    cases pick with
    | mk next stChoose =>
      cases next with
      | none =>
        simp only [hChoose] at hStep
        have hSet : setCurrentThread none (saveOutgoingContext stChoose) = .ok ((), st') := hStep
        simp [setCurrentThread] at hSet
        subst hSet
        simp [contextMatchesCurrent]
      | some tid =>
        cases hObj : stChoose.objects[tid.toObjId]? with
        | none => simp [hChoose, hObj] at hStep
        | some obj =>
          cases obj with
          | tcb tcb =>
            by_cases hOk : tid ∈ stChoose.scheduler.runQueue ∧ tcb.domain = stChoose.scheduler.activeDomain
            · simp only [hChoose, hObj, hOk] at hStep
              have hSet := hStep
              simp [setCurrentThread] at hSet
              subst hSet
              -- After setCurrentThread: current = some tid
              -- objects = stRestored.objects = (restoreIncomingContext stDequeued tid).objects
              -- = stDequeued.objects = (saveOutgoingContext stChoose).objects
              -- machine = stRestored.machine = (restoreIncomingContext stDequeued tid).machine
              simp only [contextMatchesCurrent]
              -- Need: objects[tid.toObjId]? has a TCB and machine.regs = tcb'.registerContext
              -- chooseThread preserves state, so stChoose.objects = st.objects
              have hState := chooseThread_preserves_state st stChoose (some tid) hChoose
              have hObjInvC : stChoose.objects.invExt := hState ▸ hObjInv
              have ⟨tcb', hTcb'⟩ := saveOutgoingContext_preserves_tcb stChoose tid.toObjId tcb hObj hObjInvC
              -- restoreIncomingContext reads from stDequeued.objects = (saveOutgoingContext stChoose).objects
              simp only [restoreIncomingContext, hTcb']
              exact RegisterFile.beq_self _
            · have hOk' : ¬(stChoose.scheduler.runQueue.contains tid = true ∧
                  tcb.domain = stChoose.scheduler.activeDomain) := by
                simpa [RunQueue.mem_iff_contains] using hOk
              simp [hChoose, hObj, hOk'] at hStep
          | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ =>
            simp [hChoose, hObj] at hStep

/-- WS-H12c/H-03: `handleYield` preserves `contextMatchesCurrent`.
`handleYield` calls `schedule` which re-establishes the invariant. -/
private theorem handleYield_preserves_contextMatchesCurrent
    (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : handleYield st = .ok ((), st')) :
    contextMatchesCurrent st' := by
  unfold handleYield at hStep
  cases hCur : st.scheduler.current with
  | none =>
    -- V5-F: handleYield now returns .error .invalidArgument when current = none
    simp only [hCur] at hStep; cases hStep
  | some tid =>
    simp only [hCur] at hStep
    cases hObj : st.objects[tid.toObjId]? with
    | none => simp [hObj] at hStep
    | some obj =>
      cases obj with
      | tcb tcb =>
        simp only [hObj] at hStep
        apply schedule_preserves_contextMatchesCurrent _ st' _ hStep
        exact hObjInv
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ =>
        simp [hObj] at hStep

/-- WS-H12c/H-03: `timerTick` preserves `contextMatchesCurrent`.
- When no thread is current: only advances machine timer, current remains none → vacuous.
- When time slice doesn't expire: decrements timeSlice via storeObject, machine.regs and
  current are unchanged → invariant preserved.
- When time slice expires: re-enqueues + calls `schedule` → invariant re-established. -/
private theorem timerTick_preserves_contextMatchesCurrent
    (st st' : SystemState)
    (hInv : contextMatchesCurrent st)
    (hObjInv : st.objects.invExt)
    (hStep : timerTick st = .ok ((), st')) :
    contextMatchesCurrent st' := by
  unfold timerTick at hStep
  cases hCur : st.scheduler.current with
  | none =>
    -- No current thread → just advance timer → current = none → vacuous
    simp only [hCur, Except.ok.injEq, Prod.mk.injEq] at hStep
    obtain ⟨_, hStEq⟩ := hStep; subst hStEq
    simp [contextMatchesCurrent, hCur]
  | some curTid =>
    simp only [hCur] at hStep
    cases hObj : st.objects[curTid.toObjId]? with
    | none => simp [hObj] at hStep
    | some obj =>
      cases obj with
      | tcb tcb =>
        simp only [hObj] at hStep
        by_cases hExpire : tcb.timeSlice ≤ 1
        · -- Time slice expired → re-enqueue + schedule
          simp only [hExpire, ite_true] at hStep
          have hObjInv' := RHTable_insert_preserves_invExt st.objects curTid.toObjId (KernelObject.tcb { tcb with timeSlice := st.scheduler.configDefaultTimeSlice }) hObjInv
          exact schedule_preserves_contextMatchesCurrent _ st' hObjInv' hStep
        · -- Time slice not expired → inline state construction
          simp only [hExpire, ite_false, Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, hStEq⟩ := hStep; subst hStEq
          -- st' = { st with objects := ..insert.., machine := tick st.machine }
          -- current unchanged (= some curTid), machine.regs unchanged (tick only changes timer)
          simp only [contextMatchesCurrent, hCur]
          simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv, beq_self_eq_true]; simp
          -- Goal: (tick st.machine).regs = tcb.registerContext
          simp only [contextMatchesCurrent, hCur, hObj] at hInv
          simp only [tick]; exact hInv
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ =>
        simp [hObj] at hStep

/-- WS-H12c: Frame theorem for `contextMatchesCurrent`. If a state transition
preserves `machine.regs`, `scheduler.current`, and the object at the current
thread's ID, then `contextMatchesCurrent` is preserved. This is the primary
mechanism for proving IPC and capability operations preserve the invariant:
they never modify register context or machine registers. -/
theorem contextMatchesCurrent_frame
    (st st' : SystemState)
    (hInv : contextMatchesCurrent st)
    (hMachine : st'.machine.regs = st.machine.regs)
    (hCurrent : st'.scheduler.current = st.scheduler.current)
    (hObjects : ∀ tid, st.scheduler.current = some tid →
      st'.objects[tid.toObjId]? = st.objects[tid.toObjId]?) :
    contextMatchesCurrent st' := by
  simp only [contextMatchesCurrent]
  cases hCur : st.scheduler.current with
  | none =>
    have : st'.scheduler.current = none := by rw [hCurrent, hCur]
    simp [this]
  | some tid =>
    have hCur' : st'.scheduler.current = some tid := by rw [hCurrent, hCur]
    have hObjEq := hObjects tid hCur
    -- Extract the content of hInv before simp modifies it
    simp only [contextMatchesCurrent, hCur] at hInv
    simp only [hCur']
    rw [hObjEq]
    cases hObj : st.objects[tid.toObjId]? with
    | none => simp
    | some obj =>
      cases obj with
      | tcb tcb =>
        simp only [hObj] at hInv
        simp only []
        rw [hMachine]; exact hInv
      | _ => simp

-- ============================================================================
-- R6-D: schedulerPriorityMatch preservation lemmas
-- ============================================================================

-- ============================================================================
-- R6-D: schedulerPriorityMatch preservation lemmas (schedule, handleYield, timerTick)
-- ============================================================================

/-- R6-D: `schedule` preserves `schedulerPriorityMatch`. Schedule removes the
    dispatched thread and modifies TCBs via context save/restore. Since context
    save only changes `registerContext` (not `priority`), the priority mapping is
    preserved for all remaining runQueue members.
    Proof follows `schedule_preserves_runnableThreadsAreTCBs` pattern. -/
private theorem schedule_preserves_schedulerPriorityMatch
    (st st' : SystemState)
    (hpm : schedulerPriorityMatch st)
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStep : schedule st = .ok ((), st')) :
    schedulerPriorityMatch st' := by
  unfold schedule at hStep
  cases hChoose : chooseThread st with
  | error e => simp [hChoose] at hStep
  | ok pick =>
    cases pick with
    | mk next stChoose =>
      have hStEqBase := chooseThread_preserves_state st stChoose next (by rw [hChoose])
      have hObjInvC : stChoose.objects.invExt := hStEqBase ▸ hObjInv
      cases next with
      | none =>
        -- Idle: no thread dispatched, runQueue unchanged
        simp only [hChoose] at hStep
        have hObjSt' : st'.objects = (saveOutgoingContext stChoose).objects := by
          simp only [setCurrentThread] at hStep
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, rfl⟩ := hStep; rfl
        have hRQSt' : st'.scheduler.runQueue = stChoose.scheduler.runQueue := by
          simp only [setCurrentThread] at hStep
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, rfl⟩ := hStep; simp [saveOutgoingContext_scheduler]
        intro tid hMem
        rw [hRQSt'] at hMem ⊢
        rw [hObjSt']
        -- stChoose = st means stChoose.scheduler.runQueue = st.scheduler.runQueue etc.
        have hRQEq : stChoose.scheduler.runQueue = st.scheduler.runQueue := by rw [hStEqBase]
        have hObjEq : stChoose.objects = st.objects := by rw [hStEqBase]
        rw [hRQEq] at hMem
        have hOldPM := hpm tid hMem
        have hMemRunnable : tid ∈ st.scheduler.runnable := by
          simp only [SchedulerState.runnable]
          exact (RunQueue.mem_toList_iff_mem _ _).mpr hMem
        obtain ⟨tcb, hTcb⟩ := hAllTcb tid hMemRunnable
        have hTcbC : stChoose.objects[tid.toObjId]? = some (.tcb tcb) := by rw [hObjEq]; exact hTcb
        obtain ⟨tcb', hTcb', _, hPrioEq, _, _, hPipEq⟩ :=
          saveOutgoingContext_tcb_fields stChoose tid.toObjId tcb hTcbC hObjInvC
        -- Goal: match (saveOutgoing).objects.get? tid.toObjId with tcb → threadPrio = prio
        -- Key facts: hTcb' gives the saveOutgoing lookup; hPrioEq links priorities
        -- hOldPM gives the original match result with st's threadPriority
        -- Strategy: show the match on objects.get? gives .tcb tcb', then rewrite prio
        simp only [RHTable_getElem?_eq_get?] at hTcb' ⊢
        rw [hTcb']; simp only []
        -- Goal: stChoose.scheduler.runQueue.threadPriority.get? tid = some (effectiveRunQueuePriority tcb')
        simp [effectiveRunQueuePriority, hPrioEq, hPipEq]
        -- Goal: stChoose.scheduler.runQueue.threadPriority.get? tid = some (effectiveRunQueuePriority tcb)
        -- Convert stChoose → st via hRQEq
        have : stChoose.scheduler.runQueue.threadPriority = st.scheduler.runQueue.threadPriority := by
          rw [hStEqBase]
        rw [this]
        -- Now use hOldPM
        simp only [RHTable_getElem?_eq_get?] at hOldPM hTcb
        rw [hTcb] at hOldPM; simp only [] at hOldPM
        exact hOldPM
      | some selTid =>
        -- Dispatch: selTid removed, context save/restore
        simp only [hChoose] at hStep
        cases hObj : stChoose.objects[selTid.toObjId]? with
        | none => simp [hObj] at hStep
        | some obj =>
          cases obj with
          | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ =>
            simp [hObj] at hStep
          | tcb tcb =>
            simp only [hObj] at hStep
            by_cases hSchedOk : selTid ∈ stChoose.scheduler.runQueue ∧ tcb.domain = stChoose.scheduler.activeDomain
            · rw [if_pos hSchedOk] at hStep
              have hObjSt' : st'.objects = (saveOutgoingContext stChoose).objects := by
                simp only [setCurrentThread] at hStep
                simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, rfl⟩ := hStep; simp [restoreIncomingContext_objects]
              have hSchedSt' : st'.scheduler.runQueue = stChoose.scheduler.runQueue.remove selTid := by
                simp only [setCurrentThread] at hStep
                simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, rfl⟩ := hStep
                simp [restoreIncomingContext_scheduler, saveOutgoingContext_scheduler]
              intro t hMem
              rw [hSchedSt'] at hMem
              rw [RunQueue.mem_remove] at hMem
              obtain ⟨hMemOrig, hNeSelTid⟩ := hMem
              -- Convert to st-level membership
              have hRQEq : stChoose.scheduler.runQueue = st.scheduler.runQueue := by rw [hStEqBase]
              have hObjEq : stChoose.objects = st.objects := by rw [hStEqBase]
              have hMemSt : t ∈ st.scheduler.runQueue := by rw [← hRQEq]; exact hMemOrig
              have hMemRunnable : t ∈ st.scheduler.runnable := by
                simp only [SchedulerState.runnable]
                exact (RunQueue.mem_toList_iff_mem _ _).mpr hMemSt
              have hOldPM := hpm t hMemSt
              obtain ⟨tcb', hTcb'⟩ := hAllTcb t hMemRunnable
              -- objects after saveOutgoingContext: priority preserved
              rw [hObjSt']
              have hTcbC : stChoose.objects[t.toObjId]? = some (.tcb tcb') := by rw [hObjEq]; exact hTcb'
              obtain ⟨tcb'', hTcb'', _, hPrioEq, _, _, hPipEq⟩ :=
                saveOutgoingContext_tcb_fields stChoose t.toObjId tcb' hTcbC hObjInvC
              simp only [RHTable_getElem?_eq_get?] at hTcb'' ⊢
              rw [hTcb'']; simp only []
              -- Goal: (runQueue.remove selTid).threadPriority.get? t = some (effectiveRunQueuePriority tcb'')
              simp [effectiveRunQueuePriority, hPrioEq, hPipEq]
              -- Goal: (runQueue.remove selTid).threadPriority.get? t = some tcb'.priority
              -- threadPriority after remove = erase selTid; for t ≠ selTid, unchanged
              rw [hSchedSt']
              simp only [RunQueue.remove]
              -- Goal: (stChoose.scheduler.runQueue.threadPriority.erase selTid).get? t = some tcb'.priority
              have hTNeSel : ¬(selTid == t) = true := by
                intro h; exact hNeSelTid ((eq_of_beq h).symm)
              rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_ne_K
                stChoose.scheduler.runQueue.threadPriority selTid t hTNeSel
                stChoose.scheduler.runQueue.threadPrio_invExtK]
              -- Goal: stChoose.scheduler.runQueue.threadPriority.get? t = some tcb'.priority
              have : stChoose.scheduler.runQueue.threadPriority = st.scheduler.runQueue.threadPriority := by
                rw [hStEqBase]
              rw [this]
              simp only [RHTable_getElem?_eq_get?] at hOldPM hTcb'
              rw [hTcb'] at hOldPM; simp only [] at hOldPM
              exact hOldPM
            · have hSchedOk' : ¬(stChoose.scheduler.runQueue.contains selTid = true ∧ tcb.domain = stChoose.scheduler.activeDomain) := by
                simpa [RunQueue.mem_iff_contains] using hSchedOk
              simp [hSchedOk'] at hStep

/-- R6-D: `handleYield` preserves `schedulerPriorityMatch`.
    handleYield re-enqueues current at its priority then calls schedule.
    Proof delegates to `schedule_preserves_schedulerPriorityMatch` on the
    intermediate state after insert+rotateToBack. -/
private theorem handleYield_preserves_schedulerPriorityMatch
    (st st' : SystemState)
    (hpm : schedulerPriorityMatch st)
    (hQCC : queueCurrentConsistent st.scheduler)
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStep : handleYield st = .ok ((), st')) :
    schedulerPriorityMatch st' := by
  unfold handleYield at hStep
  cases hCur : st.scheduler.current with
  | none =>
    -- V5-F: handleYield now returns .error .invalidArgument when current = none
    simp [hCur] at hStep
  | some curTid =>
    cases hObj : st.objects[curTid.toObjId]? with
    | none => simp [hCur, hObj] at hStep
    | some obj =>
      cases obj with
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ =>
        simp [hCur, hObj] at hStep
      | tcb curTcb =>
        simp only [hCur, hObj] at hStep
        have hNotMem : curTid ∉ st.scheduler.runQueue := by
          simp [queueCurrentConsistent, hCur] at hQCC
          intro h; exact hQCC ((RunQueue.mem_toList_iff_mem _ _).2 h)
        have hContF : st.scheduler.runQueue.contains curTid = false := by
          cases h : st.scheduler.runQueue.contains curTid; rfl; exact absurd h hNotMem
        -- Intermediate state: insert curTid at curTcb.priority, rotateToBack
        apply schedule_preserves_schedulerPriorityMatch _ st' _ _ (by exact hObjInv) hStep
        · -- schedulerPriorityMatch on intermediate state
          intro t hMem
          have hMemIns : t ∈ st.scheduler.runQueue.insert curTid (effectiveRunQueuePriority curTcb) :=
            (RunQueue.mem_rotateToBack _ curTid t).mp hMem
          rw [RunQueue.mem_insert] at hMemIns
          simp only [RunQueue.rotateToBack_threadPriority, RunQueue.insert_threadPriority,
            hContF, Bool.false_eq_true, ↓reduceIte]
          cases hMemIns with
          | inl hOld =>
            have hNeq : curTid ≠ t := fun h => hNotMem (h ▸ hOld)
            have hBEq : (curTid == t) = false := by cases h : (curTid == t) <;> simp_all
            simp only [RHTable_getElem?_eq_get?]
            rw [RHTable_getElem?_insert st.scheduler.runQueue.threadPriority _ _
              st.scheduler.runQueue.threadPrio_invExtK.1]
            simp only [hBEq, Bool.false_eq_true, ↓reduceIte]
            exact hpm t hOld
          | inr hEq =>
            subst hEq
            simp only [RHTable_getElem?_eq_get?]
            rw [RHTable_getElem?_insert st.scheduler.runQueue.threadPriority _ _
              st.scheduler.runQueue.threadPrio_invExtK.1]
            simp only [beq_self_eq_true, ↓reduceIte]
            simp only [RHTable_getElem?_eq_get?] at hObj; rw [hObj]
        · -- hAllTcb on intermediate state
          intro t hMem
          simp only [SchedulerState.runnable] at hMem
          rw [RunQueue.mem_toList_iff_mem, RunQueue.mem_rotateToBack, RunQueue.mem_insert] at hMem
          cases hMem with
          | inl hOld =>
            exact hAllTcb t (by simp [SchedulerState.runnable]; exact (RunQueue.mem_toList_iff_mem _ _).mpr hOld)
          | inr hEq =>
            subst hEq; exact ⟨curTcb, hObj⟩

/-- R6-D: `timerTick` preserves `schedulerPriorityMatch`.
    Non-expire: only timeSlice/timer change. Expire: timeSlice reset + insert + schedule.
    Uses same `hpm'` pattern as `timerTick_preserves_edfCurrentHasEarliestDeadline`. -/
private theorem timerTick_preserves_schedulerPriorityMatch
    (st st' : SystemState)
    (hpm : schedulerPriorityMatch st)
    (hQCC : queueCurrentConsistent st.scheduler)
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStep : timerTick st = .ok ((), st')) :
    schedulerPriorityMatch st' := by
  unfold timerTick at hStep
  cases hCur : st.scheduler.current with
  | none =>
    simp [hCur] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hpm
  | some curTid =>
    simp only [hCur] at hStep
    cases hObj : st.objects[curTid.toObjId]? with
    | none => simp [hObj] at hStep
    | some obj =>
      cases obj with
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ =>
        simp [hObj] at hStep
      | tcb curTcb =>
        simp only [hObj] at hStep
        have hNotMem : curTid ∉ st.scheduler.runQueue := by
          simp [queueCurrentConsistent, hCur] at hQCC
          intro h; exact hQCC ((RunQueue.mem_toList_iff_mem _ _).2 h)
        have hContF : st.scheduler.runQueue.contains curTid = false := by
          cases h : st.scheduler.runQueue.contains curTid; rfl; exact absurd h hNotMem
        by_cases hExp : curTcb.timeSlice ≤ 1
        · -- Expire: reset timeSlice, insert, schedule
          rw [if_pos hExp] at hStep
          have hObjInv' := RHTable_insert_preserves_invExt st.objects curTid.toObjId
            (KernelObject.tcb { curTcb with timeSlice := st.scheduler.configDefaultTimeSlice }) hObjInv
          apply schedule_preserves_schedulerPriorityMatch _ st' _ _ hObjInv' hStep
          · -- schedulerPriorityMatch on intermediate state (after insert into runQueue + objects)
            intro t hMem
            rw [RunQueue.mem_insert] at hMem
            simp only [RunQueue.insert_threadPriority, hContF, Bool.false_eq_true, ↓reduceIte]
            cases hMem with
            | inl hOld =>
              have hNeq : curTid ≠ t := fun h => hNotMem (h ▸ hOld)
              have hBEq : (curTid == t) = false := by cases h : (curTid == t) <;> simp_all
              have hObjBEq : (curTid.toObjId == t.toObjId) = false := by
                cases h : (curTid.toObjId == t.toObjId) with
                | false => rfl
                | true => exact absurd (ThreadId.toObjId_injective curTid t (eq_of_beq h)) hNeq
              simp only [RHTable_getElem?_eq_get?]
              rw [RHTable_getElem?_insert st.objects _ _ hObjInv,
                  RHTable_getElem?_insert st.scheduler.runQueue.threadPriority _ _
                    st.scheduler.runQueue.threadPrio_invExtK.1]
              simp only [hObjBEq, hBEq, Bool.false_eq_true, ↓reduceIte]
              exact hpm t hOld
            | inr hEq =>
              subst hEq
              simp only [RHTable_getElem?_eq_get?]
              rw [RHTable_getElem?_insert st.scheduler.runQueue.threadPriority _ _
                st.scheduler.runQueue.threadPrio_invExtK.1]
              simp only [beq_self_eq_true, ite_true]
              rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
              simp only [beq_self_eq_true, ite_true]
              -- AI3-A: effectiveRunQueuePriority only depends on priority + pipBoost,
              -- both preserved by the timeSlice-only update
              simp [effectiveRunQueuePriority]
          · -- hAllTcb on intermediate state
            intro t hMem
            simp only [SchedulerState.runnable] at hMem
            rw [RunQueue.mem_toList_iff_mem, RunQueue.mem_insert] at hMem
            cases hMem with
            | inl hOld =>
              have hMemOrig : t ∈ st.scheduler.runnable := by
                simp [SchedulerState.runnable]; exact (RunQueue.mem_toList_iff_mem _ _).mpr hOld
              obtain ⟨tcbT, hTcbT⟩ := hAllTcb t hMemOrig
              simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
              by_cases hEq : curTid.toObjId == t.toObjId
              · simp [hEq]
              · simp [hEq]; exact ⟨tcbT, hTcbT⟩
            | inr hEq =>
              subst hEq
              simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
              simp [BEq.beq]
        · -- Non-expire: only timeSlice decremented, timer incremented
          rw [if_neg hExp] at hStep
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, rfl⟩ := hStep
          intro tid hMem
          have hOldPM := hpm tid hMem
          -- objects changed at curTid (timeSlice only); runQueue unchanged
          simp only [RHTable_getElem?_eq_get?] at hOldPM ⊢
          rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
          by_cases hEq : curTid.toObjId == tid.toObjId
          · -- tid = curTid → contradiction (curTid not in runQueue, tid is)
            have hTidEq : curTid = tid := ThreadId.toObjId_injective curTid tid (eq_of_beq hEq)
            exact absurd (hTidEq ▸ hMem) hNotMem
          · simp only [hEq]; exact hOldPM

-- ============================================================================
-- WS-H6/WS-H12b: Full scheduler invariant bundle composition theorems
-- ============================================================================

/-- WS-H6/WS-H12b: `schedule` preserves the full scheduler invariant bundle.
    R6-D: `schedulerPriorityMatch` now extracted from the bundle. -/
theorem schedule_preserves_schedulerInvariantBundleFull
    (st st' : SystemState)
    (hInv : schedulerInvariantBundleFull st)
    (hwf : RunQueue.wellFormed st.scheduler.runQueue)
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStep : schedule st = .ok ((), st')) :
    schedulerInvariantBundleFull st' := by
  rcases hInv with ⟨hBase, hTS, hCurTS, hEDF, _hCtx, _hRunnTcb, hPM, hDTR, hEntries⟩
  have hpm := hPM
  exact ⟨schedule_preserves_schedulerInvariantBundle st st' hBase hObjInv hStep,
         schedule_preserves_timeSlicePositive st st' hTS hObjInv hStep,
         schedule_preserves_currentTimeSlicePositive st st' hTS hObjInv hStep,
         schedule_preserves_edfCurrentHasEarliestDeadline st st' hwf hpm hAllTcb hObjInv hStep,
         schedule_preserves_contextMatchesCurrent st st' hObjInv hStep,
         schedule_preserves_runnableThreadsAreTCBs st st' hAllTcb hObjInv hStep,
         schedule_preserves_schedulerPriorityMatch st st' hpm hAllTcb hObjInv hStep,
         schedule_preserves_domainTimeRemainingPositive st st' hDTR hObjInv hStep,
         fun e hMem => hEntries e (schedule_preserves_domainSchedule st st' hStep ▸ hMem)⟩

/-- WS-H6/WS-H12b: `handleYield` preserves the full scheduler invariant bundle.
    R6-D: `schedulerPriorityMatch` now extracted from the bundle. -/
theorem handleYield_preserves_schedulerInvariantBundleFull
    (st st' : SystemState)
    (hInv : schedulerInvariantBundleFull st)
    (hwf : RunQueue.wellFormed st.scheduler.runQueue)
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStep : handleYield st = .ok ((), st')) :
    schedulerInvariantBundleFull st' := by
  rcases hInv with ⟨hBase, hTS, hCurTS, hEDF, _hCtx, _hRunnTcb, hPM, hDTR, hEntries⟩
  have hpm := hPM
  exact ⟨handleYield_preserves_schedulerInvariantBundle st st' hBase hObjInv hStep,
         handleYield_preserves_timeSlicePositive st st' hTS hCurTS hObjInv hStep,
         handleYield_preserves_currentTimeSlicePositive st st' hTS hCurTS hObjInv hStep,
         handleYield_preserves_edfCurrentHasEarliestDeadline st st' hwf hpm hBase.1 hAllTcb hObjInv hStep,
         handleYield_preserves_contextMatchesCurrent st st' hObjInv hStep,
         handleYield_preserves_runnableThreadsAreTCBs st st' hAllTcb hObjInv hStep,
         handleYield_preserves_schedulerPriorityMatch st st' hpm hBase.1 hAllTcb hObjInv hStep,
         handleYield_preserves_domainTimeRemainingPositive st st' hDTR hObjInv hStep,
         fun e hMem => hEntries e (handleYield_preserves_domainSchedule st st' hStep ▸ hMem)⟩

/-- WS-H6/WS-H12b: `timerTick` preserves the full scheduler invariant bundle.
    R6-D: `schedulerPriorityMatch` now extracted from the bundle.
    AC2-C: Requires `configDefaultTimeSlice > 0` for time-slice positivity proofs. -/
theorem timerTick_preserves_schedulerInvariantBundleFull
    (st st' : SystemState)
    (hInv : schedulerInvariantBundleFull st)
    (hwf : RunQueue.wellFormed st.scheduler.runQueue)
    (hAllTcb : ∀ t, t ∈ st.scheduler.runnable →
      ∃ tcb, st.objects[t.toObjId]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hConfigTS : st.scheduler.configDefaultTimeSlice > 0)
    (hStep : timerTick st = .ok ((), st')) :
    schedulerInvariantBundleFull st' := by
  rcases hInv with ⟨hBase, hTS, hCurTS, hEDF, hCtx, _hRunnTcb, hPM, hDTR, hEntries⟩
  have hpm := hPM
  exact ⟨timerTick_preserves_schedulerInvariantBundle st st' ⟨hBase.1, hBase.2.1, hBase.2.2⟩ hObjInv hStep,
         timerTick_preserves_timeSlicePositive st st' hTS hObjInv hConfigTS hStep,
         timerTick_preserves_currentTimeSlicePositive st st' hTS hCurTS hObjInv hConfigTS hStep,
         timerTick_preserves_edfCurrentHasEarliestDeadline st st' hwf hpm hBase.1 hEDF hAllTcb hObjInv hStep,
         timerTick_preserves_contextMatchesCurrent st st' hCtx hObjInv hStep,
         timerTick_preserves_runnableThreadsAreTCBs st st' hAllTcb hObjInv hStep,
         timerTick_preserves_schedulerPriorityMatch st st' hpm hBase.1 hAllTcb hObjInv hStep,
         timerTick_preserves_domainTimeRemainingPositive st st' hDTR hObjInv hStep,
         fun e hMem => hEntries e (timerTick_preserves_domainSchedule st st' hStep ▸ hMem)⟩

-- ============================================================================
-- S3-E: scheduleDomain full bundle preservation
-- ============================================================================

/-- S3-E: Helper — `switchDomain` preserves `RunQueue.wellFormed`.
    In the expire path, the current thread (if any) is re-enqueued via `insert`,
    which preserves well-formedness. In all other paths the runQueue is unchanged. -/
private theorem switchDomain_preserves_runQueueWellFormed
    (st st' : SystemState)
    (hwf : RunQueue.wellFormed st.scheduler.runQueue)
    (hStep : switchDomain st = .ok ((), st')) :
    RunQueue.wellFormed st'.scheduler.runQueue := by
  unfold switchDomain at hStep
  cases hSched : st.scheduler.domainSchedule with
  | nil => simp [hSched] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hwf
  | cons entry rest =>
    simp only [hSched] at hStep
    split at hStep
    · -- AK2-I: `.error` fallback; contradiction discharged during split.
      simp at hStep
    · rename_i hGet
      simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
      obtain ⟨_, rfl⟩ := hStep
      simp only
      cases hCur : st.scheduler.current with
      | none => exact hwf
      | some tid =>
        simp only []
        cases hObj : st.objects[tid.toObjId]? with
        | none => exact hwf
        | some obj =>
          cases obj with
          | tcb tcb => exact RunQueue.insert_preserves_wellFormed _ hwf _ _
          | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ =>
            exact hwf

/-- S3-E/U-M08/V5-H/X2-A: `scheduleDomain` preserves `schedulerInvariantBundleFull`.

    Composes `switchDomain_preserves_schedulerInvariantBundleFull` and
    `schedule_preserves_schedulerInvariantBundleFull` for the expire path.
    In the non-expire path, `domainTimeRemaining` is decremented by 1;
    V5-H proves the result is still > 0 since the guard ensures > 1.
    X2-A: `hEntriesPos` is now extracted from the bundle (9th conjunct)
    instead of being required as an external hypothesis. -/
theorem scheduleDomain_preserves_schedulerInvariantBundleFull
    (st st' : SystemState)
    (hInv : schedulerInvariantBundleFull st)
    (hwf : RunQueue.wellFormed st.scheduler.runQueue)
    (hObjInv : st.objects.invExt)
    (hStep : scheduleDomain st = .ok ((), st')) :
    schedulerInvariantBundleFull st' := by
  unfold scheduleDomain at hStep
  by_cases hExpire : st.scheduler.domainTimeRemaining ≤ 1
  · simp [hExpire] at hStep
    cases hSw : switchDomain st with
    | error e => simp [hSw] at hStep
    | ok pair =>
        cases pair with
        | mk _ stSw =>
            have hSched : schedule stSw = .ok ((), st') := by simpa [hSw] using hStep
            -- switchDomain preserves the full bundle (X2-A: hEntriesPos now in bundle)
            have hSwInv : schedulerInvariantBundleFull stSw :=
              switchDomain_preserves_schedulerInvariantBundleFull st stSw hInv hObjInv (by simp [hSw])
            -- switchDomain preserves objects.invExt
            have hSwObjInv : stSw.objects.invExt :=
              switchDomain_preserves_objects_invExt st stSw hObjInv (by simp [hSw])
            -- switchDomain preserves RunQueue.wellFormed
            have hSwWf : RunQueue.wellFormed stSw.scheduler.runQueue :=
              switchDomain_preserves_runQueueWellFormed st stSw hwf (by simp [hSw])
            -- Extract runnableThreadsAreTCBs from the full bundle
            have hSwAllTcb : ∀ t, t ∈ stSw.scheduler.runnable →
                ∃ tcb, stSw.objects[t.toObjId]? = some (.tcb tcb) :=
              hSwInv.2.2.2.2.2.1
            exact schedule_preserves_schedulerInvariantBundleFull stSw st'
              hSwInv hSwWf hSwAllTcb hSwObjInv hSched
  · -- Non-expire: domainTimeRemaining decremented by 1
    simp [hExpire] at hStep
    cases hStep
    -- V5-H: All bundle components except domainTimeRemainingPositive are preserved
    -- trivially (only domainTimeRemaining changed). For domainTimeRemainingPositive,
    -- ¬(domainTimeRemaining ≤ 1) implies domainTimeRemaining > 1, so - 1 > 0.
    rcases hInv with ⟨hBase, hTS, hCurTS, hEDF, hCtx, hRunnTcb, hPM, hDTR, hEntries⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hBase
    · exact hTS
    · exact hCurTS
    · exact hEDF
    · exact hCtx
    · exact hRunnTcb
    · exact hPM
    · unfold domainTimeRemainingPositive at *; simp; omega
    · exact hEntries

-- ============================================================================
-- Z4-Q/R/S/T/U: SchedContext-aware preservation theorems
-- ============================================================================

-- Z4-Q1: timerTickBudget unbound branch preserves scheduler state structure.
-- The unbound path delegates to legacy time-slice logic, modifying only the TCB
-- object and machine timer. The scheduler's runQueue, replenishQueue, and all
-- SchedContext objects are unchanged (frame reasoning).

/-- Z4-Q1: `timerTickBudget` unbound non-preempt preserves scheduler fields. -/
theorem timerTickBudget_unbound_nopreempt_scheduler_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) (st' : SystemState)
    (hUnbound : tcb.schedContextBinding = .unbound)
    (hNotExpired : ¬(tcb.timeSlice ≤ 1))
    (hStep : timerTickBudget st tid tcb = .ok (st', false)) :
    st'.scheduler = st.scheduler := by
  simp [timerTickBudget, hUnbound, hNotExpired] at hStep
  cases hStep; rfl

/-- Z4-Q2: `timerTickBudget` unbound preempt preserves replenishQueue. -/
theorem timerTickBudget_unbound_preempt_replenishQueue_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) (st' : SystemState)
    (hUnbound : tcb.schedContextBinding = .unbound)
    (hExpired : tcb.timeSlice ≤ 1)
    (hStep : timerTickBudget st tid tcb = .ok (st', true)) :
    st'.scheduler.replenishQueue = st.scheduler.replenishQueue := by
  simp [timerTickBudget, hUnbound, hExpired] at hStep
  cases hStep; rfl

-- Z4-R: Replenishment queue preservation.

/-- Z4-R1: `popDueReplenishments` returns a sorted queue (prefix removal
preserves sortedness). Delegates to Z3's `popDue_preserves_sorted`. -/
theorem popDueReplenishments_sorted
    (st : SystemState) (now : Nat)
    (hSorted : replenishQueueSorted st.scheduler.replenishQueue) :
    replenishQueueSorted (popDueReplenishments st now).1 := by
  unfold popDueReplenishments
  exact popDue_preserves_sorted hSorted

/-- Z4-R2: `popDueReplenishments` preserves size consistency.
Delegates to Z3's `popDue_sizeConsistent`. -/
theorem popDueReplenishments_sizeConsistent
    (st : SystemState) (now : Nat)
    (hSize : replenishQueueSizeConsistent st.scheduler.replenishQueue) :
    replenishQueueSizeConsistent (popDueReplenishments st now).1 := by
  unfold popDueReplenishments
  exact popDue_sizeConsistent hSize

-- Z4-S: Legacy path preserves new SchedContext invariants.

/-- Z4-S1: `refillSchedContext` is a no-op when the ObjId doesn't map to a
SchedContext (defensive fallback). -/
theorem refillSchedContext_noop
    (st : SystemState) (scId : SeLe4n.SchedContextId) (now : Nat)
    (hNone : ∀ sc, st.objects[scId.toObjId]? ≠ some (.schedContext sc)) :
    refillSchedContext st scId now = st := by
  unfold refillSchedContext
  simp only [GetElem?.getElem?]
  match h : st.objects.get? scId.toObjId with
  | none => rfl
  | some (.schedContext sc) =>
    exfalso; exact hNone sc (by simp [GetElem?.getElem?, h])
  | some (.tcb _) => rfl
  | some (.endpoint _) => rfl
  | some (.notification _) => rfl
  | some (.vspaceRoot _) => rfl
  | some (.cnode _) => rfl
  | some (.untyped _) => rfl

-- Z4-Q1 (substantive): Budget decrement preserves positivity.

/-- Z4-Q1: When `budgetRemaining > 1`, consuming 1 tick leaves the budget > 0.
This is the core arithmetic lemma for CBS budget decrement correctness. -/
theorem budget_decrement_stays_positive (b : Nat) (h : b > 1) :
    b - 1 > 0 := by omega

/-- Z4-Q2 (substantive): When `budgetRemaining > 1` in the bound decrement path,
the resulting SchedContext has `budgetRemaining > 0`. Proves the CBS budget
accounting maintains the `budgetPositive` invariant through normal ticks. -/
theorem consumeBudget_positive_of_gt_one (sc : SchedContext)
    (h : sc.budgetRemaining.val > 1) :
    (consumeBudget sc 1).budgetRemaining.val > 0 := by
  simp [consumeBudget, Budget.decrement]
  omega

-- Z4-S1 (substantive): Unbound timerTickBudget preserves scheduler structure.

/-- Z4-S1a: `timerTickBudget` unbound non-preempt inserts only a `.tcb` into the
object store. All SchedContext objects are untouched because the unbound path
only writes `.tcb tcb'`. The inserted key is `tid.toObjId`. -/
theorem timerTickBudget_unbound_nopreempt_objects_key
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) (st' : SystemState)
    (hUnbound : tcb.schedContextBinding = .unbound)
    (hNotExpired : ¬(tcb.timeSlice ≤ 1))
    (hStep : timerTickBudget st tid tcb = .ok (st', false)) :
    ∃ tcb', st'.objects = st.objects.insert tid.toObjId (.tcb tcb') := by
  unfold timerTickBudget at hStep
  rw [hUnbound, if_neg hNotExpired] at hStep
  have hinj := Except.ok.inj hStep
  have hfst := congrArg Prod.fst hinj
  simp only [] at hfst
  subst hfst
  exact ⟨{ tcb with timeSlice := tcb.timeSlice - 1, schedContextBinding := .unbound }, rfl⟩

/-- Z4-S1b: `timerTickBudget` unbound preempt inserts only a `.tcb` into the
object store. All SchedContext objects are untouched. -/
theorem timerTickBudget_unbound_preempt_objects_key
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) (st' : SystemState)
    (hUnbound : tcb.schedContextBinding = .unbound)
    (hExpired : tcb.timeSlice ≤ 1)
    (hStep : timerTickBudget st tid tcb = .ok (st', true)) :
    ∃ tcb', st'.objects = st.objects.insert tid.toObjId (.tcb tcb') := by
  unfold timerTickBudget at hStep
  rw [hUnbound, if_pos hExpired] at hStep
  have hinj := Except.ok.inj hStep
  have hfst := congrArg Prod.fst hinj
  simp only [] at hfst
  subst hfst
  exact ⟨{ tcb with timeSlice := st.scheduler.configDefaultTimeSlice, schedContextBinding := .unbound }, rfl⟩

-- Z4-S2 (substantive): consumeBudget preserves per-SchedContext well-formedness.

/-- Z4-S2a: `consumeBudget` preserves per-object `wellFormed`.
Bridges Z2's per-object theorem to the system-level invariant. -/
theorem consumeBudget_preserves_wf
    (sc : SchedContext) (ticks : Nat) (h : sc.wellFormed) :
    (consumeBudget sc ticks).wellFormed :=
  consumeBudget_preserves_wellFormed sc ticks h

/-- Z4-S2b: `consumeBudget` preserves the full 4-conjunct `schedContextWellFormed`.
Composes Z2's four per-component preservation theorems. -/
theorem consumeBudget_preserves_schedContextWellFormed_full
    (sc : SchedContext) (ticks : Nat)
    (h : schedContextWellFormed sc) :
    schedContextWellFormed (consumeBudget sc ticks) := by
  obtain ⟨hwf, hbounds, hrepl, hamounts⟩ := h
  exact ⟨consumeBudget_preserves_wellFormed sc ticks hwf,
         consumeBudget_preserves_budgetWithinBounds sc ticks hbounds,
         consumeBudget_preserves_replenishmentListWellFormed sc ticks hrepl,
         consumeBudget_preserves_replenishmentAmountsBounded sc ticks hamounts⟩

-- Z4-S3 (substantive): scheduleReplenishment preserves per-SchedContext well-formedness.

/-- Z4-S3: `scheduleReplenishment` preserves the full 4-conjunct
`schedContextWellFormed`, given that the consumed amount is positive and
within budget. These preconditions hold in both callers:
- `timerTickBudget` exhaustion: consumed = budgetRemaining > 0 (guard), ≤ budget (invariant)
- `handleYieldWithBudget`: consumed = budgetRemaining > 0 (current is positive), ≤ budget (invariant) -/
theorem scheduleReplenishment_preserves_schedContextWellFormed_full
    (sc : SchedContext) (now : Nat) (consumed : Budget)
    (h : schedContextWellFormed sc)
    (hPos : consumed.val > 0)
    (hLe : consumed.val ≤ sc.budget.val) :
    schedContextWellFormed (scheduleReplenishment sc now consumed) := by
  obtain ⟨hwf, hbounds, hrepl, hamounts⟩ := h
  exact ⟨scheduleReplenishment_preserves_wellFormed sc now consumed hwf,
         scheduleReplenishment_preserves_budgetWithinBounds sc now consumed hbounds,
         scheduleReplenishment_preserves_replenishmentListWellFormed
           sc now consumed hrepl hPos,
         scheduleReplenishment_preserves_replenishmentAmountsBounded
           sc now consumed hamounts hLe⟩

-- Z4-T: Selection correctness and dequeue preservation.

/-- Z4-T1: `chooseThreadEffective` preserves state — re-export of the
Selection.lean theorem for use in preservation proofs. -/
theorem chooseThreadEffective_state_unchanged
    (st : SystemState) (res : Option SeLe4n.ThreadId) (st' : SystemState)
    (hStep : chooseThreadEffective st = .ok (res, st')) :
    st' = st :=
  chooseThreadEffective_preserves_state st st' res hStep

/-- Z4-T2: Removing a thread from the runnable list preserves `budgetPositive`
for remaining threads. Under dequeue-on-dispatch, the dequeued thread exits
the ∀-quantifier domain, so the invariant holds for the smaller set. -/
theorem budgetPositive_subset
    (st : SystemState)
    (hBp : budgetPositive st)
    (tid : SeLe4n.ThreadId) :
    ∀ tid', tid' ∈ st.scheduler.runnable → tid' ≠ tid →
      match st.objects[tid'.toObjId]? with
      | some (.tcb tcb) =>
        match tcb.schedContextBinding with
        | .unbound => True
        | .bound scId | .donated scId _ =>
          match st.objects[scId.toObjId]? with
          | some (.schedContext sc) => sc.budgetRemaining.val > 0
          | _ => True
      | _ => True :=
  fun tid' hMem' _ => hBp tid' hMem'

-- Z4-U: Backward compatibility and yield preservation.

/-- Z4-U1: `effectivePriority_unbound` — unbound threads resolve to TCB fields.
This confirms the backward-compatibility guarantee. -/
theorem effectivePriority_unbound_legacy
    (st : SystemState) (tcb : TCB)
    (hUnbound : tcb.schedContextBinding = .unbound)
    (hNoPip : tcb.pipBoost = none := by rfl) :
    effectivePriority st tcb = some (tcb.priority, tcb.deadline, tcb.domain) := by
  simp [effectivePriority, hUnbound, hNoPip]

/-- Z4-U2: `hasSufficientBudget_unbound` — unbound threads are always eligible. -/
theorem hasSufficientBudget_unbound_legacy
    (st : SystemState) (tcb : TCB)
    (hUnbound : tcb.schedContextBinding = .unbound) :
    hasSufficientBudget st tcb = true := by
  simp [hasSufficientBudget, hUnbound]

/-- Z4-U3: `cbsUpdateDeadline` preserves per-object `wellFormed`.
Composes with Z4-S2/S3 for the full exhaustion pipeline:
consumeBudget → scheduleReplenishment → cbsUpdateDeadline. -/
theorem cbsUpdateDeadline_preserves_wf
    (sc : SchedContext) (now : Nat) (preempt : Bool)
    (h : sc.wellFormed) :
    (cbsUpdateDeadline sc now preempt).wellFormed := by
  simp [cbsUpdateDeadline]
  split
  · -- Deadline updated case: only deadline field changes
    simp [SchedContext.wellFormed]
    obtain ⟨hp, hbp, hrb, hrl⟩ := h
    exact ⟨hp, hbp, hrb, hrl⟩
  · -- No update: identity
    exact h

-- ============================================================================
-- AN5-B (SCH-M03): Replenishment pipeline ordering preservation
-- ============================================================================

/-! ### SCH-M03 — Replenishment pipeline ordering witness

`replenishmentPipelineOrder` (in `Scheduler/Invariant.lean`) captures
the post-pop-due post-condition: under a sorted input queue and a pop
at time `now`, every remaining entry has `eligibleAt > now`. See the
scope note in `Scheduler/Invariant.lean` for the important caveat
that this predicate is pipeline-relative, not a free-standing state
invariant preserved by arbitrary operations.

**Preservation witness** (this section): when the pre-state has a
SORTED `replenishQueue` (`replenishQueueSorted` in
`SchedContext/ReplenishQueue.lean`, Z3-F), the post-state of a pure
`popDue now` call satisfies the pair-level witness `pair.2 > now` for
every remaining entry. This is exactly the contract
`replenishmentPipelineOrder` asserts at the point where `machine.timer`
equals `now`.

The predicate is PIPELINE-relative, not a free-standing state
invariant — see the scope note in `Scheduler/Invariant.lean` at
`replenishmentPipelineOrder` for details. A bare `tick` of the timer
does NOT preserve the invariant; re-entry into `processReplenishmentsDue`
re-establishes it. The composed `timerTickWithBudget` preserves the
invariant in the idiomatic "pop then tick" ordering because the
post-pop pair-level witness is stronger than the post-tick requirement
(remaining `eligibleAt > now → eligibleAt ≥ now + 1 = post-tick timer`
only when the entry's `eligibleAt > now` strictly; if `eligibleAt = now`
it was already popped). The full `timerTickWithBudget` composition
theorem is tracked for the Theme 4.7 file split (AN5-A) when per-op
preservation moves into child modules. -/

/-- AN5-B (SCH-M03): Under `pairwiseSortedBy`, every element of a list
has `.2` ≥ the head's `.2`. Technical helper for the popDue-remaining
witness. -/
private theorem pairwiseSortedBy_head_le_all :
    ∀ (id0 : SeLe4n.SchedContextId) (t0 : Nat)
      (rest : List (SeLe4n.SchedContextId × Nat)),
      pairwiseSortedBy ((id0, t0) :: rest) →
      ∀ p ∈ rest, t0 ≤ p.2
  | _id0, _t0, [], _h => by intro p hp; simp at hp
  | id0, t0, (id1, t1) :: tl, h => by
      intro p hp
      have h1 : t0 ≤ t1 := pairwiseSortedBy_head_le_second h
      have hTl : pairwiseSortedBy ((id1, t1) :: tl) := h.2
      cases hp with
      | head => exact h1
      | tail _ hTail =>
          have : t1 ≤ p.2 :=
            pairwiseSortedBy_head_le_all id1 t1 tl hTl p hTail
          exact Nat.le_trans h1 this

/-- AN5-B (SCH-M03): After `popDue now`, every remaining entry has
`eligibleAt > now`, under the sortedness precondition on the input
queue. Direct consequence of `ReplenishQueue.splitDue`'s prefix-split
semantics: the remaining suffix starts at the first entry whose
`eligibleAt > now`, and under sortedness all subsequent entries also
satisfy `eligibleAt > now`. -/
theorem popDueReplenishments_remaining_gt_now
    (st : SystemState) (now : Nat)
    (hSorted : replenishQueueSorted st.scheduler.replenishQueue)
    (pair : SeLe4n.SchedContextId × Nat)
    (hMem : pair ∈ (popDueReplenishments st now).1.entries) :
    pair.2 > now := by
  unfold popDueReplenishments at hMem
  simp only [ReplenishQueue.popDue] at hMem
  -- hMem : pair ∈ (splitDue entries now).2
  -- hSorted : entries is pairwiseSortedBy (ascending on .2)
  unfold replenishQueueSorted at hSorted
  revert hMem hSorted
  induction st.scheduler.replenishQueue.entries with
  | nil =>
      intro _ hMem
      simp [ReplenishQueue.splitDue] at hMem
  | cons hd tl ih =>
      intro hSort hMem
      simp only [ReplenishQueue.splitDue] at hMem
      split at hMem
      · -- hd.2 ≤ now: dropped from remaining, recurse
        rename_i _hHdLe
        have hSortTl : pairwiseSortedBy tl :=
          pairwiseSortedBy_tail hSort
        exact ih hSortTl hMem
      · -- hd.2 > now: remaining = hd :: tl
        rename_i hHdGt
        have hHd : hd.2 > now := Nat.lt_of_not_le hHdGt
        simp only [List.mem_cons] at hMem
        rcases hMem with hEq | hTailMem
        · rw [hEq]; exact hHd
        · -- Under sortedness, every element of tl has .2 ≥ hd.2 > now
          match hd, hSort, hHd with
          | (id0, t0), hSortCons, hHd0 =>
              have hAll : ∀ p ∈ tl, t0 ≤ p.2 :=
                pairwiseSortedBy_head_le_all id0 t0 tl hSortCons
              have hTle : t0 ≤ pair.2 := hAll pair hTailMem
              have hHdGt' : t0 > now := hHd0
              omega

