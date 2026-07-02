-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.EndpointPreservation

import SeLe4n.Kernel.IPC.Invariant.CallReplyRecv.Call

/-! # ReplyRecv Preservation (AN3-D)

Extracted from `CallReplyRecv.lean` as part of AN3-D (IPC-M04 / Theme 4.7).
Contains `endpointReplyRecv` preservation for `ipcInvariant`,
`schedulerInvariantBundle`, and `ipcSchedulerContractPredicates`, the
`endpointReply_preserves_ipcSchedulerContractPredicates` companion, the
`endpointCall_preserves_objects_invExt` witness, and the `endpointCallWithCaps`
preservation cluster.
-/


namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (bootCoreId)

/-- PR #827 #3 fold: `consumeCallerReply` preserves `ipcSchedulerContractPredicates`
— the runnable set is untouched (scheduler frame) and every TCB's `ipcState` is a
preserved field, so all six coherence clauses transport. -/
theorem consumeCallerReply_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hContract : ipcSchedulerContractPredicates st)
    (hObjInv : st.objects.invExt)
    (hStep : SystemState.consumeCallerReply caller rid st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  obtain ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply, hBlockNotif⟩ := hContract
  have hSched := SystemState.consumeCallerReply_scheduler_eq st st' caller rid hStep
  have hFwd := SystemState.consumeCallerReply_tcb_forward st st' caller rid hObjInv hStep
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tid tcb hT hMem
    obtain ⟨ty, hSt, hIS, _⟩ := hFwd tid.toObjId tcb hT
    rw [hSched] at hMem
    rw [hIS]
    exact hReady tid ty hSt hMem
  · intro tid tcb epId hT hIpc
    obtain ⟨ty, hSt, hIS, _⟩ := hFwd tid.toObjId tcb hT
    rw [hSched]
    exact hBlockSend tid ty epId hSt (hIS ▸ hIpc)
  · intro tid tcb epId hT hIpc
    obtain ⟨ty, hSt, hIS, _⟩ := hFwd tid.toObjId tcb hT
    rw [hSched]
    exact hBlockRecv tid ty epId hSt (hIS ▸ hIpc)
  · intro tid tcb epId hT hIpc
    obtain ⟨ty, hSt, hIS, _⟩ := hFwd tid.toObjId tcb hT
    rw [hSched]
    exact hBlockCall tid ty epId hSt (hIS ▸ hIpc)
  · intro tid tcb epId rt hT hIpc
    obtain ⟨ty, hSt, hIS, _⟩ := hFwd tid.toObjId tcb hT
    rw [hSched]
    exact hBlockReply tid ty epId rt hSt (hIS ▸ hIpc)
  · intro tid tcb nid hT hIpc
    obtain ⟨ty, hSt, hIS, _⟩ := hFwd tid.toObjId tcb hT
    rw [hSched]
    exact hBlockNotif tid ty nid hSt (hIS ▸ hIpc)

/-- WS-H12a: endpointReplyRecv preserves ipcInvariant.
Chains storeTcbIpcStateAndMessage + ensureRunnable + endpointReceiveDual preservation. -/
theorem endpointReplyRecv_preserves_ipcInvariant
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcInvariant st)
    (hObjInv : st.objects.invExt)
    (replyId : Option SeLe4n.ReplyId)
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg replyId st = .ok ((), st')) :
    ipcInvariant st' := by
  unfold endpointReplyRecv at hStep
  -- WS-H12d: Eliminate bounds-check if-branches (error cases contradict hStep : ... = .ok ...)
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st replyTarget with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnCall _ =>
      simp [hIpc] at hStep
    | blockedOnReply _ expectedReplier =>
      simp only [hIpc] at hStep
      -- Helper: any receive-leg input state carrying the invariant proves the goal
      -- (PR #827 #3 fold: the leg's input is now the post-consume state).
      suffices ∀ st3, ipcInvariant st3 → st3.objects.invExt →
          (∀ stR, endpointReceiveDual endpointId receiver replyId st3 = .ok stR →
            ipcInvariant stR.2) by
        -- AK1-B (I-H02): Fail-closed on expectedReplier = none
        cases expectedReplier with
        | none => simp at hStep
        | some expected =>
          simp only at hStep
          split at hStep
          · revert hStep
            cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
            | error e => simp
            | ok st1 =>
              simp only []
              have hInv1 := storeTcbIpcStateAndMessage_preserves_ipcInvariant st st1 replyTarget .ready (some msg) hInv hObjInv hMsg
              have hInv2 : ipcInvariant (ensureRunnable st1 replyTarget) :=
                fun oid ntfn h => hInv1 oid ntfn (by rwa [ensureRunnable_preserves_objects] at h)
              have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st1 replyTarget .ready (some msg) hObjInv hMsg
              have hObjInvEns : (ensureRunnable st1 replyTarget).objects.invExt := by rwa [ensureRunnable_preserves_objects]
              -- PR #827 #3 fold: peel the atomic consume (no-op when unlinked).
              cases hRO : tcb.replyObject with
              | none =>
                simp only []
                cases hRecv : endpointReceiveDual endpointId receiver replyId (ensureRunnable st1 replyTarget) with
                | error e => simp
                | ok result =>
                  simp only [Except.ok.injEq, Prod.mk.injEq]
                  intro ⟨_, hEq⟩; subst hEq
                  exact this _ hInv2 hObjInvEns result hRecv
              | some rid =>
                cases hCons : SystemState.consumeCallerReply replyTarget rid (ensureRunnable st1 replyTarget) with
                | error e => simp [hCons]
                | ok p3 =>
                  obtain ⟨⟨⟩, st3⟩ := p3
                  simp only [hCons]
                  have hInv3 := consumeCallerReply_preserves_ipcInvariant _ _ replyTarget rid hObjInvEns hInv2 hCons
                  have hObjInv3 := SystemState.consumeCallerReply_preserves_objects_invExt _ _ replyTarget rid hObjInvEns hCons
                  cases hRecv : endpointReceiveDual endpointId receiver replyId st3 with
                  | error e => simp
                  | ok result =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    exact this st3 hInv3 hObjInv3 result hRecv
          · simp_all
      intro st3 hInv3 hObjInv3 stR hRecv
      exact endpointReceiveDual_preserves_ipcInvariant _ stR.2 endpointId receiver stR.1 replyId hInv3 hObjInv3 (by
        have : stR = (stR.1, stR.2) := Prod.ext rfl rfl; rw [this] at hRecv; exact hRecv)

/-- WS-H12a: endpointReplyRecv preserves schedulerInvariantBundle.
Chains storeTcbIpcStateAndMessage + ensureRunnable + endpointReceiveDual preservation. -/
theorem endpointReplyRecv_preserves_schedulerInvariantBundle
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : schedulerInvariantBundle st)
    (hObjInv : st.objects.invExt)
    (hCurrReady : currentThreadIpcReady st)
    (hCurrNotHead : currentNotEndpointQueueHead st)
    (replyId : Option SeLe4n.ReplyId)
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg replyId st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  unfold endpointReplyRecv at hStep
  -- WS-H12d: Eliminate bounds-check if-branches (error cases contradict hStep : ... = .ok ...)
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st replyTarget with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnCall _ =>
      simp [hIpc] at hStep
    | blockedOnReply _ expectedReplier =>
      simp only [hIpc] at hStep
      -- Helper: any receive-leg input state carrying the bundle facts proves the goal
      -- (PR #827 #3 fold: the leg's input is now the post-consume state).
      suffices ∀ st3, schedulerInvariantBundle st3 → currentNotEndpointQueueHead st3 →
          st3.objects.invExt →
          (∀ stR, endpointReceiveDual endpointId receiver replyId st3 = .ok stR →
            schedulerInvariantBundle stR.2) by
        -- AK1-B (I-H02): Fail-closed on expectedReplier = none
        cases expectedReplier with
        | none => simp at hStep
        | some expected =>
          simp only at hStep
          split at hStep
          · revert hStep
            cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
            | error e => simp
            | ok st1 =>
              simp only []
              obtain ⟨hQCC, hRQU, hCTV⟩ := hInv
              have hSchedEq := storeTcbIpcStateAndMessage_scheduler_eq st st1 replyTarget .ready (some msg) hMsg
              have hTargetTcbObj := lookupTcb_some_objects st replyTarget tcb hLookup
              have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st1 replyTarget .ready (some msg) hObjInv hMsg
              have hObjInvEns : (ensureRunnable st1 replyTarget).objects.invExt := by rwa [ensureRunnable_preserves_objects]
              have hInvMid : schedulerInvariantBundle (ensureRunnable st1 replyTarget) := by
                refine ⟨?_, ?_, ?_⟩
                · unfold queueCurrentConsistent
                  rw [ensureRunnable_scheduler_current, hSchedEq]
                  cases hCurr : (st.scheduler.currentOnCore bootCoreId) with
                  | none => trivial
                  | some x =>
                    have hNotMem : x ∉ st.scheduler.runnable := by
                      have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this
                    have hNe : x ≠ replyTarget := by
                      intro hEq
                      have hObj := lookupTcb_some_objects st replyTarget tcb hLookup
                      rw [hEq] at hCurr
                      have hReady : tcb.ipcState = .ready := by
                        simp [currentThreadIpcReady, hCurr] at hCurrReady; exact hCurrReady tcb hObj
                      simp [hIpc] at hReady
                    exact ensureRunnable_not_mem_of_not_mem st1 replyTarget x (hSchedEq ▸ hNotMem) hNe
                · exact ensureRunnable_nodup st1 replyTarget (hSchedEq ▸ hRQU)
                · show currentThreadValid (ensureRunnable st1 replyTarget)
                  unfold currentThreadValid
                  simp only [ensureRunnable_scheduler_current, ensureRunnable_preserves_objects, hSchedEq]
                  cases hCurr : (st.scheduler.currentOnCore bootCoreId) with
                  | none => simp
                  | some x =>
                    simp only []
                    have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by
                      simp [currentThreadValid, hCurr] at hCTV; exact hCTV
                    by_cases hNeTid : x.toObjId = replyTarget.toObjId
                    · have hTargetTcb : ∃ t, st.objects[replyTarget.toObjId]? = some (.tcb t) := hNeTid ▸ hCTV'
                      have h := storeTcbIpcStateAndMessage_tcb_exists_at_target st st1 replyTarget .ready (some msg) hObjInv hMsg hTargetTcb
                      rwa [← hNeTid] at h
                    · rcases hCTV' with ⟨tcb', hTcbObj⟩
                      exact ⟨tcb', (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 replyTarget .ready (some msg) x.toObjId hNeTid hObjInv hMsg) ▸ hTcbObj⟩
              have hCNHMid : currentNotEndpointQueueHead (ensureRunnable st1 replyTarget) := by
                unfold currentNotEndpointQueueHead
                rw [ensureRunnable_scheduler_current, hSchedEq]
                cases hCurr' : (st.scheduler.currentOnCore bootCoreId) with
                | none => trivial
                | some tid =>
                  intro oid ep' hEp'
                  rw [ensureRunnable_preserves_objects] at hEp'
                  have hOidNe : oid ≠ replyTarget.toObjId := by
                    intro h; subst h
                    obtain ⟨tcb', hTcb'⟩ := storeTcbIpcStateAndMessage_tcb_exists_at_target st st1 replyTarget .ready (some msg) hObjInv hMsg ⟨tcb, hTargetTcbObj⟩
                    rw [hTcb'] at hEp'; cases hEp'
                  have hEp'' : st.objects[oid]? = some (.endpoint ep') := by
                    rwa [storeTcbIpcStateAndMessage_preserves_objects_ne st st1 replyTarget .ready (some msg) oid hOidNe hObjInv hMsg] at hEp'
                  have := hCurrNotHead; simp [currentNotEndpointQueueHead, hCurr'] at this
                  exact this oid ep' hEp''
              -- PR #827 #3 fold: peel the atomic consume (no-op when unlinked).
              cases hRO : tcb.replyObject with
              | none =>
                simp only []
                cases hRecv : endpointReceiveDual endpointId receiver replyId (ensureRunnable st1 replyTarget) with
                | error e => simp
                | ok result =>
                  simp only [Except.ok.injEq, Prod.mk.injEq]
                  intro ⟨_, hEq⟩; subst hEq
                  exact this _ hInvMid hCNHMid hObjInvEns result hRecv
              | some rid =>
                cases hCons : SystemState.consumeCallerReply replyTarget rid (ensureRunnable st1 replyTarget) with
                | error e => simp [hCons]
                | ok p3 =>
                  obtain ⟨⟨⟩, st3⟩ := p3
                  simp only [hCons]
                  have hInv3 : schedulerInvariantBundle st3 :=
                    consumeCallerReply_preserves_schedulerInvariantBundle _ _ replyTarget rid hInvMid hObjInvEns hCons
                  have hCNH3 : currentNotEndpointQueueHead st3 := by
                    have hNT := SystemState.consumeCallerReply_nonTcbNonReply_agree _ _ replyTarget rid hObjInvEns hCons
                    have hSchedC := SystemState.consumeCallerReply_scheduler_eq _ _ replyTarget rid hCons
                    unfold currentNotEndpointQueueHead at hCNHMid ⊢
                    rw [hSchedC]
                    cases hCurr2 : ((ensureRunnable st1 replyTarget).scheduler.currentOnCore bootCoreId) with
                    | none => exact True.intro
                    | some tid =>
                      rw [hCurr2] at hCNHMid
                      intro oid ep hEp
                      exact hCNHMid oid ep ((hNT oid (.endpoint ep)
                        (fun tt => by exact KernelObject.noConfusion)
                        (fun rr => by exact KernelObject.noConfusion)).mp hEp)
                  have hObjInv3 := SystemState.consumeCallerReply_preserves_objects_invExt _ _ replyTarget rid hObjInvEns hCons
                  cases hRecv : endpointReceiveDual endpointId receiver replyId st3 with
                  | error e => simp
                  | ok result =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    exact this st3 hInv3 hCNH3 hObjInv3 result hRecv
          · simp_all
      intro st3 hInv3 hCNH3 hObjInv3 stR hRecv
      exact endpointReceiveDual_preserves_schedulerInvariantBundle _ stR.2 endpointId receiver stR.1 replyId hInv3 hCNH3 hObjInv3
        (by have : stR = (stR.1, stR.2) := Prod.ext rfl rfl; rw [this] at hRecv; exact hRecv)

/-- WS-H12a: endpointReplyRecv preserves ipcSchedulerContractPredicates.
Chains storeTcbIpcStateAndMessage + ensureRunnable + endpointReceiveDual preservation. -/
theorem endpointReplyRecv_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (hContract : ipcSchedulerContractPredicates st)
    (hObjInv : st.objects.invExt)
    (replyId : Option SeLe4n.ReplyId)
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg replyId st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hContract with ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply, hBlockNotif⟩
  unfold endpointReplyRecv at hStep
  -- WS-H12d: Eliminate bounds-check if-branches (error cases contradict hStep : ... = .ok ...)
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st replyTarget with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnCall _ =>
      simp [hIpc] at hStep
    | blockedOnReply _ expectedReplier =>
      simp only [hIpc] at hStep
      -- Helper: any receive-leg input state carrying the contract facts proves the
      -- goal (PR #827 #3 fold: the leg's input is now the post-consume state).
      suffices ∀ st3, ipcSchedulerContractPredicates st3 → st3.objects.invExt →
          (∀ stR, endpointReceiveDual endpointId receiver replyId st3 = .ok stR →
            ipcSchedulerContractPredicates stR.2) by
        -- AK1-B (I-H02): Fail-closed on expectedReplier = none
        cases expectedReplier with
        | none => simp at hStep
        | some expected =>
          simp only at hStep
          split at hStep
          · revert hStep
            cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
            | error e => simp
            | ok st1 =>
              simp only []
              have hSchedEq := storeTcbIpcStateAndMessage_scheduler_eq st st1 replyTarget .ready (some msg) hMsg
              have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st1 replyTarget .ready (some msg) hObjInv hMsg
              have hObjInvEns : (ensureRunnable st1 replyTarget).objects.invExt := by rwa [ensureRunnable_preserves_objects]
              have hContractMid : ipcSchedulerContractPredicates (ensureRunnable st1 replyTarget) := by
                refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
                · intro tid tcb' hTcb' hRun'
                  rw [ensureRunnable_preserves_objects] at hTcb'
                  by_cases hNe : tid.toObjId = replyTarget.toObjId
                  · exact storeTcbIpcStateAndMessage_ipcState_eq st st1 replyTarget .ready (some msg) hObjInv hMsg tcb' (hNe ▸ hTcb')
                  · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 replyTarget .ready (some msg) tid.toObjId hNe hObjInv hMsg).symm.trans hTcb'
                    have hNeTid : tid ≠ replyTarget := fun h => hNe (congrArg ThreadId.toObjId h)
                    rcases ensureRunnable_mem_reverse st1 replyTarget tid hRun' with hOld | hEq
                    · exact hReady tid tcb' hTcbPre (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
                    · exact absurd hEq hNeTid
                · intro tid tcb' eid hTcb' hIpcState'
                  rw [ensureRunnable_preserves_objects] at hTcb'
                  by_cases hNe : tid.toObjId = replyTarget.toObjId
                  · have := storeTcbIpcStateAndMessage_ipcState_eq st st1 replyTarget .ready (some msg) hObjInv hMsg tcb' (hNe ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hNeTid : tid ≠ replyTarget := fun h => hNe (congrArg ThreadId.toObjId h)
                    have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 replyTarget .ready (some msg) tid.toObjId hNe hObjInv hMsg).symm.trans hTcb'
                    intro hRun'
                    rcases ensureRunnable_mem_reverse st1 replyTarget tid hRun' with hOld | hEq
                    · exact hBlockSend tid tcb' eid hTcbPre hIpcState' (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
                    · exact absurd hEq hNeTid
                · intro tid tcb' eid hTcb' hIpcState'
                  rw [ensureRunnable_preserves_objects] at hTcb'
                  by_cases hNe : tid.toObjId = replyTarget.toObjId
                  · have := storeTcbIpcStateAndMessage_ipcState_eq st st1 replyTarget .ready (some msg) hObjInv hMsg tcb' (hNe ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hNeTid : tid ≠ replyTarget := fun h => hNe (congrArg ThreadId.toObjId h)
                    have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 replyTarget .ready (some msg) tid.toObjId hNe hObjInv hMsg).symm.trans hTcb'
                    intro hRun'
                    rcases ensureRunnable_mem_reverse st1 replyTarget tid hRun' with hOld | hEq
                    · exact hBlockRecv tid tcb' eid hTcbPre hIpcState' (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
                    · exact absurd hEq hNeTid
                · intro tid tcb' eid hTcb' hIpcState'
                  rw [ensureRunnable_preserves_objects] at hTcb'
                  by_cases hNe : tid.toObjId = replyTarget.toObjId
                  · have := storeTcbIpcStateAndMessage_ipcState_eq st st1 replyTarget .ready (some msg) hObjInv hMsg tcb' (hNe ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hNeTid : tid ≠ replyTarget := fun h => hNe (congrArg ThreadId.toObjId h)
                    have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 replyTarget .ready (some msg) tid.toObjId hNe hObjInv hMsg).symm.trans hTcb'
                    intro hRun'
                    rcases ensureRunnable_mem_reverse st1 replyTarget tid hRun' with hOld | hEq
                    · exact hBlockCall tid tcb' eid hTcbPre hIpcState' (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
                    · exact absurd hEq hNeTid
                · intro tid tcb' eid rt hTcb' hIpcState'
                  rw [ensureRunnable_preserves_objects] at hTcb'
                  by_cases hNe : tid.toObjId = replyTarget.toObjId
                  · have := storeTcbIpcStateAndMessage_ipcState_eq st st1 replyTarget .ready (some msg) hObjInv hMsg tcb' (hNe ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hNeTid : tid ≠ replyTarget := fun h => hNe (congrArg ThreadId.toObjId h)
                    have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 replyTarget .ready (some msg) tid.toObjId hNe hObjInv hMsg).symm.trans hTcb'
                    intro hRun'
                    rcases ensureRunnable_mem_reverse st1 replyTarget tid hRun' with hOld | hEq
                    · exact hBlockReply tid tcb' eid rt hTcbPre hIpcState' (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
                    · exact absurd hEq hNeTid
                · -- blockedOnNotificationNotRunnable (WS-F6/D2)
                  intro tid tcb' nid hTcb' hIpcState'
                  rw [ensureRunnable_preserves_objects] at hTcb'
                  by_cases hNe : tid.toObjId = replyTarget.toObjId
                  · have := storeTcbIpcStateAndMessage_ipcState_eq st st1 replyTarget .ready (some msg) hObjInv hMsg tcb' (hNe ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hNeTid : tid ≠ replyTarget := fun h => hNe (congrArg ThreadId.toObjId h)
                    have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 replyTarget .ready (some msg) tid.toObjId hNe hObjInv hMsg).symm.trans hTcb'
                    intro hRun'
                    rcases ensureRunnable_mem_reverse st1 replyTarget tid hRun' with hOld | hEq
                    · exact hBlockNotif tid tcb' nid hTcbPre hIpcState' (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
                    · exact absurd hEq hNeTid
              -- PR #827 #3 fold: peel the atomic consume (no-op when unlinked).
              cases hRO : tcb.replyObject with
              | none =>
                simp only []
                cases hRecv : endpointReceiveDual endpointId receiver replyId (ensureRunnable st1 replyTarget) with
                | error e => simp
                | ok result =>
                  simp only [Except.ok.injEq, Prod.mk.injEq]
                  intro ⟨_, hEq⟩; subst hEq
                  exact this _ hContractMid hObjInvEns result hRecv
              | some rid =>
                cases hCons : SystemState.consumeCallerReply replyTarget rid (ensureRunnable st1 replyTarget) with
                | error e => simp [hCons]
                | ok p3 =>
                  obtain ⟨⟨⟩, st3⟩ := p3
                  simp only [hCons]
                  have hContract3 : ipcSchedulerContractPredicates st3 :=
                    consumeCallerReply_preserves_ipcSchedulerContractPredicates _ _ replyTarget rid hContractMid hObjInvEns hCons
                  have hObjInv3 := SystemState.consumeCallerReply_preserves_objects_invExt _ _ replyTarget rid hObjInvEns hCons
                  cases hRecv : endpointReceiveDual endpointId receiver replyId st3 with
                  | error e => simp
                  | ok result =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    exact this st3 hContract3 hObjInv3 result hRecv
          · simp_all
      intro st3 hContract3 hObjInv3 stR hRecv
      exact endpointReceiveDual_preserves_ipcSchedulerContractPredicates _ stR.2 endpointId receiver stR.1 replyId hContract3 hObjInv3 (by
        have : stR = (stR.1, stR.2) := Prod.ext rfl rfl
        rw [this] at hRecv; exact hRecv)

/-- WS-F1/TPI-D09: endpointReply preserves ipcSchedulerContractPredicates.
endpointReply only stores a TCB and calls ensureRunnable; the contract
predicate preservation follows the handshake_path_preserves_contracts pattern
since the target is set to .ready and added to runnable. -/
theorem endpointReply_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState)
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (hContract : ipcSchedulerContractPredicates st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hContract with ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply, hBlockNotif⟩
  unfold endpointReply at hStep
  -- WS-H12d: Eliminate bounds-check if-branches (error cases contradict hStep : ... = .ok ...)
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready => simp [hIpc] at hStep
    | blockedOnSend _ => simp [hIpc] at hStep
    | blockedOnReceive _ => simp [hIpc] at hStep
    | blockedOnNotification _ => simp [hIpc] at hStep
    | blockedOnCall _ => simp [hIpc] at hStep
    | blockedOnReply epId replyTarget =>
      simp only [hIpc] at hStep
      -- AK1-B (I-H02): Fail-closed on replyTarget = none
      -- Both branches share identical 5-conjunct proof after authorization resolves.
      -- Helper: given st1 from storeTcbIpcStateAndMessage, prove the 5 conjuncts.
      suffices ∀ st1, storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st1 →
          ipcSchedulerContractPredicates (ensureRunnable st1 target) by
        cases replyTarget with
        | none => simp at hStep
        | some expected =>
          simp only at hStep
          split at hStep
          · -- authorized = true
            cases hMsg : storeTcbIpcStateAndMessage st target .ready (some msg) with
            | error e => simp [hMsg] at hStep
            | ok st1 =>
              simp only [hMsg] at hStep
              have hMid := this st1 hMsg
              have hObjInvMid : (ensureRunnable st1 target).objects.invExt := by
                rw [ensureRunnable_preserves_objects]
                exact storeTcbIpcStateAndMessage_preserves_objects_invExt st st1 target .ready (some msg) hObjInv hMsg
              -- PR #827 #3 fold: peel the atomic consume (no-op when unlinked).
              cases hRO : tcb.replyObject with
              | none =>
                simp only [hRO, Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
                rw [← hStep]; exact hMid
              | some rid =>
                simp only [hRO] at hStep
                exact consumeCallerReply_preserves_ipcSchedulerContractPredicates _ _ target rid hMid hObjInvMid hStep
          · -- authorized = false
            simp_all
      -- Shared proof body
      intro st1 hMsg
      have hSchedEq := storeTcbIpcStateAndMessage_scheduler_eq st st1 target .ready (some msg) hMsg
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- runnableThreadIpcReady
        intro tid tcb' hTcb' hRun'
        rw [ensureRunnable_preserves_objects] at hTcb'
        by_cases hNe : tid.toObjId = target.toObjId
        · exact storeTcbIpcStateAndMessage_ipcState_eq st st1 target .ready (some msg) hObjInv hMsg tcb' (hNe ▸ hTcb')
        · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 target .ready (some msg) tid.toObjId hNe hObjInv hMsg).symm.trans hTcb'
          have hNeTid : tid ≠ target := fun h => hNe (congrArg ThreadId.toObjId h)
          rcases ensureRunnable_mem_reverse st1 target tid hRun' with hOld | hEq
          · exact hReady tid tcb' hTcbPre (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
          · exact absurd hEq hNeTid
      · -- blockedOnSendNotRunnable
        intro tid tcb' eid hTcb' hIpcState'
        rw [ensureRunnable_preserves_objects] at hTcb'
        by_cases hNe : tid.toObjId = target.toObjId
        · have := storeTcbIpcStateAndMessage_ipcState_eq st st1 target .ready (some msg) hObjInv hMsg tcb' (hNe ▸ hTcb')
          rw [this] at hIpcState'; cases hIpcState'
        · have hNeTid : tid ≠ target := fun h => hNe (congrArg ThreadId.toObjId h)
          have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 target .ready (some msg) tid.toObjId hNe hObjInv hMsg).symm.trans hTcb'
          intro hRun'
          rcases ensureRunnable_mem_reverse st1 target tid hRun' with hOld | hEq
          · exact hBlockSend tid tcb' eid hTcbPre hIpcState' (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
          · exact absurd hEq hNeTid
      · -- blockedOnReceiveNotRunnable
        intro tid tcb' eid hTcb' hIpcState'
        rw [ensureRunnable_preserves_objects] at hTcb'
        by_cases hNe : tid.toObjId = target.toObjId
        · have := storeTcbIpcStateAndMessage_ipcState_eq st st1 target .ready (some msg) hObjInv hMsg tcb' (hNe ▸ hTcb')
          rw [this] at hIpcState'; cases hIpcState'
        · have hNeTid : tid ≠ target := fun h => hNe (congrArg ThreadId.toObjId h)
          have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 target .ready (some msg) tid.toObjId hNe hObjInv hMsg).symm.trans hTcb'
          intro hRun'
          rcases ensureRunnable_mem_reverse st1 target tid hRun' with hOld | hEq
          · exact hBlockRecv tid tcb' eid hTcbPre hIpcState' (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
          · exact absurd hEq hNeTid
      · -- blockedOnCallNotRunnable
        intro tid tcb' eid hTcb' hIpcState'
        rw [ensureRunnable_preserves_objects] at hTcb'
        by_cases hNe : tid.toObjId = target.toObjId
        · have := storeTcbIpcStateAndMessage_ipcState_eq st st1 target .ready (some msg) hObjInv hMsg tcb' (hNe ▸ hTcb')
          rw [this] at hIpcState'; cases hIpcState'
        · have hNeTid : tid ≠ target := fun h => hNe (congrArg ThreadId.toObjId h)
          have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 target .ready (some msg) tid.toObjId hNe hObjInv hMsg).symm.trans hTcb'
          intro hRun'
          rcases ensureRunnable_mem_reverse st1 target tid hRun' with hOld | hEq
          · exact hBlockCall tid tcb' eid hTcbPre hIpcState' (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
          · exact absurd hEq hNeTid
      · -- blockedOnReplyNotRunnable
        intro tid tcb' eid rt' hTcb' hIpcState'
        rw [ensureRunnable_preserves_objects] at hTcb'
        by_cases hNe : tid.toObjId = target.toObjId
        · have := storeTcbIpcStateAndMessage_ipcState_eq st st1 target .ready (some msg) hObjInv hMsg tcb' (hNe ▸ hTcb')
          rw [this] at hIpcState'; cases hIpcState'
        · have hNeTid : tid ≠ target := fun h => hNe (congrArg ThreadId.toObjId h)
          have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 target .ready (some msg) tid.toObjId hNe hObjInv hMsg).symm.trans hTcb'
          intro hRun'
          rcases ensureRunnable_mem_reverse st1 target tid hRun' with hOld | hEq
          · exact hBlockReply tid tcb' eid rt' hTcbPre hIpcState' (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
          · exact absurd hEq hNeTid
      · -- blockedOnNotificationNotRunnable (WS-F6/D2)
        intro tid tcb' nid hTcb' hIpcState'
        rw [ensureRunnable_preserves_objects] at hTcb'
        by_cases hNe : tid.toObjId = target.toObjId
        · have := storeTcbIpcStateAndMessage_ipcState_eq st st1 target .ready (some msg) hObjInv hMsg tcb' (hNe ▸ hTcb')
          rw [this] at hIpcState'; cases hIpcState'
        · have hNeTid : tid ≠ target := fun h => hNe (congrArg ThreadId.toObjId h)
          have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 target .ready (some msg) tid.toObjId hNe hObjInv hMsg).symm.trans hTcb'
          intro hRun'
          rcases ensureRunnable_mem_reverse st1 target tid hRun' with hOld | hEq
          · exact hBlockNotif tid tcb' nid hTcbPre hIpcState' (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
          · exact absurd hEq hNeTid

-- ============================================================================
-- endpointCall preserves objects.invExt
-- ============================================================================

/-- endpointCall preserves objects.invExt through all sub-operations. -/
theorem endpointCall_preserves_objects_invExt
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    st'.objects.invExt := by
  unfold endpointCall at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg] at hStep
            have hObjInvMsg := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 .ready (some msg) hObjInv1 hMsg
            have hObjInvEns : (ensureRunnable st2 pair.1).objects.invExt := by rwa [ensureRunnable_preserves_objects]
            -- AK1-C (I-M01): storeTcbIpcStateAndMessage replaces storeTcbIpcState to atomically clear caller's pendingMessage
            cases hIpc : storeTcbIpcStateAndMessage (ensureRunnable st2 pair.1) caller (.blockedOnReply endpointId (some pair.1)) none with
            | error e => simp [hIpc] at hStep
            | ok st4 =>
              simp only [hIpc] at hStep
              have hObjInvIpc := storeTcbIpcStateAndMessage_preserves_objects_invExt _ st4 caller _ none hObjInvEns hIpc
              -- WS-SM SM6.D (#7.3 fold): thread the server-first reply link.
              cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
              | error e => simp [hLink] at hStep
              | ok pL =>
                obtain ⟨_, st5⟩ := pL
                simp only [hLink, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                have hObjInv5 := linkServerStashedReply_preserves_objects_invExt st4 st5 caller pair.1 hObjInvIpc hLink
                rwa [removeRunnable_preserves_objects]
      | none =>
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false caller st st1 hObjInv hEnq
          cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hObjInvMsg := storeTcbIpcStateAndMessage_preserves_objects_invExt st1 st2 caller _ (some msg) hObjInv1 hMsg
            rwa [removeRunnable_preserves_objects]

-- ============================================================================
-- M3-E4: endpointCallWithCaps preservation
-- ============================================================================

/-- M3-E4: endpointCallWithCaps preserves ipcInvariant. Same structure as
endpointSendDualWithCaps: every branch either returns the post-call state
(preserved by endpointCall) or passes through ipcUnwrapCaps (precondition-free
preservation). -/
theorem endpointCallWithCaps_preserves_ipcInvariant
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (callerCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hInv : ipcInvariant st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointCallWithCaps endpointId caller msg endpointRights
             callerCspaceRoot receiverSlotBase st = .ok (summary, st')) :
    ipcInvariant st' := by
  simp only [endpointCallWithCaps] at hStep
  cases hCall : endpointCall endpointId caller msg st with
  | error e => simp [hCall] at hStep
  | ok pair =>
    rcases pair with ⟨_, stMid⟩
    have hInvMid := endpointCall_preserves_ipcInvariant st stMid endpointId caller msg hInv hObjInv hCall
    have hObjInvMid : stMid.objects.invExt := endpointCall_preserves_objects_invExt st stMid endpointId caller msg hObjInv hCall
    simp [hCall] at hStep
    -- AN10-B: post-migration `endpointCallWithCaps` reads via `getEndpoint?`.
    cases hEp : st.getEndpoint? endpointId with
    | none =>
      simp [hEp] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hInvMid
    | some ep =>
      simp [hEp] at hStep
      cases hHead : ep.receiveQ.head with
      | none =>
        simp [hHead] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hInvMid
      | some receiverId =>
        simp [hHead] at hStep
        by_cases hEmpty : msg.caps = #[]
        · simp [hEmpty] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hInvMid
        · simp [hEmpty] at hStep
          cases hLookup : lookupCspaceRoot stMid receiverId with
          | none => simp [hLookup] at hStep -- WS-RC R1 (DEEP-IPC-03): fail-closed, vacuous
          | some recvRoot =>
            simp [hLookup] at hStep
            exact ipcUnwrapCaps_preserves_ipcInvariant msg callerCspaceRoot recvRoot
              receiverSlotBase _ stMid st' summary hInvMid hObjInvMid hStep

-- ============================================================================
-- V3-G5 (M-PRF-5): waitingThreadsPendingMessageNone preservation
-- for call/replyRecv operations
-- ============================================================================

-- V3-G5 (M-PRF-5): `endpointCall`/`endpointReplyRecv` preserve
-- `waitingThreadsPendingMessageNone`.
-- Machine-checked proofs in Structural.lean:
--   `endpointCall_preserves_waitingThreadsPendingMessageNone`
--   `endpointReplyRecv_preserves_waitingThreadsPendingMessageNone`

end SeLe4n.Kernel
