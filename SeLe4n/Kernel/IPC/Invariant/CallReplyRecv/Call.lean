-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.EndpointPreservation

/-! # Call Preservation (AN3-D)

Extracted from `CallReplyRecv.lean` as part of AN3-D (IPC-M04 / Theme 4.7).
Contains `endpointCall` preservation theorems for `ipcInvariant`,
`schedulerInvariantBundle`, and `ipcSchedulerContractPredicates`, plus the
`endpointCall_blocked_stays_blocked` structural witness.  Declarations are
unchanged in order, content, and proof; only the file boundary has moved.
The parent `CallReplyRecv.lean` re-exports every child so all existing
`import SeLe4n.Kernel.IPC.Invariant.CallReplyRecv` consumers continue to
typecheck without modification.
-/


namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (bootCoreId)

-- ============================================================================
-- WS-F1: endpointCall / endpointReplyRecv invariant preservation (F-11 remediation)
--
-- TPI-D09: Compound operation preservation proof infrastructure
--
-- Architecture: endpointCall = endpointQueuePopHead + storeTcbIpcStateAndMessage
-- + ensureRunnable + storeTcbIpcState + removeRunnable. endpointReplyRecv =
-- storeTcbIpcStateAndMessage + ensureRunnable + endpointReceiveDual.
--
-- The preservation argument decomposes into the already-proven sub-operation
-- preservation lemmas. endpointReply (fully proved above) serves as the model.
-- ============================================================================

/-- WS-F1/TPI-D09: endpointCall preserves ipcInvariant. -/
theorem endpointCall_preserves_ipcInvariant
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (payload : SendPayload)
    (hInv : ipcInvariant st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointCall endpointId caller payload st = .ok ((), st')) :
    ipcInvariant st' := by
  unfold endpointCall SystemState.getObject? at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ | frame _ | pageTable _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        -- Handshake: PopHead → storeTcbIpcStateAndMessage → ensureRunnable → storeTcbIpcState → removeRunnable
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 _ hObjInv hPop
          have hInv1 := endpointQueuePopHead_preserves_ipcInvariant endpointId true st pair.2.2 pair.1 hInv hObjInv hPop
          cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some (sendPayloadMessage st caller payload)) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg] at hStep
            have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 .ready (some (sendPayloadMessage st caller payload)) hObjInv1 hMsg
            have hInv2 := storeTcbIpcStateAndMessage_preserves_ipcInvariant pair.2.2 st2 pair.1 .ready (some (sendPayloadMessage st caller payload)) hInv1 hObjInv1 hMsg
            have hInv3 : ipcInvariant (ensureRunnable st2 pair.1) :=
              fun oid ntfn h => hInv2 oid ntfn ((ensureRunnable_objectsAgreeOffRunLinks _ _).get_notification_iff.mp h)
            -- AK1-C (I-M01): storeTcbIpcStateAndMessage replaces storeTcbIpcState to atomically clear caller's pendingMessage
            cases hIpc : storeTcbIpcStateAndMessage (ensureRunnable st2 pair.1) caller (.blockedOnReply endpointId (some pair.1)) none with
            | error e => simp [hIpc] at hStep
            | ok st4 =>
              simp only [hIpc] at hStep
              have hObjInvEns : (ensureRunnable st2 pair.1).objects.invExt := ensureRunnable_objects_invExt _ _ (by assumption)
              have hInv4 := storeTcbIpcStateAndMessage_preserves_ipcInvariant _ st4 caller _ none hInv3 hObjInvEns hIpc
              have hObjInv4 := storeTcbIpcStateAndMessage_preserves_objects_invExt _ st4 caller _ none hObjInvEns hIpc
              -- WS-SM SM6.D (#7.3 fold): thread the server-first reply link
              cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
              | error e => simp [hLink] at hStep
              | ok pL =>
                obtain ⟨_, st5⟩ := pL
                simp only [hLink, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                have hInv5 := linkServerStashedReply_preserves_ipcInvariant st4 st5 caller pair.1 hInv4 hObjInv4 hLink
                exact fun oid ntfn h => hInv5 oid ntfn ((removeRunnable_objectsAgreeOffRunLinks _ _).get_notification_iff.mp h)
      | none =>
        -- Blocking: Enqueue → storeTcbIpcStateAndMessage → removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false caller st st1 hObjInv hEnq
          have hInv1 := endpointQueueEnqueue_preserves_ipcInvariant endpointId false caller st st1 hInv hObjInv hEnq
          cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) none with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            refine ipcInvariant_of_objectsAgreeOffRunLinks (recordSendCap_objectsAgreeOffRunLinks _ _ _ _) ?_
            have hInv2 := storeTcbIpcStateAndMessage_preserves_ipcInvariant st1 st2 caller _ none hInv1 hObjInv1 hMsg
            exact fun oid ntfn h => hInv2 oid ntfn ((removeRunnable_objectsAgreeOffRunLinks _ _).get_notification_iff.mp h)

/-- WS-F1/TPI-D09: endpointCall preserves schedulerInvariantBundle. -/
theorem endpointCall_preserves_schedulerInvariantBundle
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (payload : SendPayload)
    (hInv : schedulerInvariantBundle st)
    (hCurrNotHead : currentNotEndpointQueueHead st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointCall endpointId caller payload st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  rcases hInv with ⟨hQCC, hRQU, hCTV⟩
  unfold endpointCall SystemState.getObject? at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ | frame _ | pageTable _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        -- Handshake: PopHead → storeTcbIpcStateAndMessage → ensureRunnable → storeTcbIpcState → removeRunnable
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hSchedPop := endpointQueuePopHead_scheduler_eq endpointId true st pair.2.2 pair.1 hPop
          have hObjInvPop := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 _ hObjInv hPop
          cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some (sendPayloadMessage st caller payload)) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg] at hStep
            have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq pair.2.2 st2 pair.1 .ready (some (sendPayloadMessage st caller payload)) hMsg
            have hObjInvMsg := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 .ready (some (sendPayloadMessage st caller payload)) hObjInvPop hMsg
            have hObjInvEns : (ensureRunnable st2 pair.1).objects.invExt := ensureRunnable_objects_invExt _ _ (by assumption)
            -- AK1-C (I-M01): storeTcbIpcStateAndMessage replaces storeTcbIpcState to atomically clear caller's pendingMessage
            cases hIpc : storeTcbIpcStateAndMessage (ensureRunnable st2 pair.1) caller (.blockedOnReply endpointId (some pair.1)) none with
            | error e => simp [hIpc] at hStep
            | ok st4 =>
              simp only [hIpc] at hStep
              have hObjInvIpc := storeTcbIpcStateAndMessage_preserves_objects_invExt (ensureRunnable st2 pair.1) st4 caller (.blockedOnReply endpointId (some pair.1)) none hObjInvEns hIpc
              have hSchedIpc := storeTcbIpcStateAndMessage_scheduler_eq (ensureRunnable st2 pair.1) st4 caller (.blockedOnReply endpointId (some pair.1)) none hIpc
              have hCurrEq : (st4.scheduler.currentOnCore bootCoreId) = (st.scheduler.currentOnCore bootCoreId) := by
                rw [hSchedIpc, ensureRunnable_scheduler_current, hSchedMsg, hSchedPop]
              -- Forward the current thread's TCB through pop → message-store →
              -- ensureRunnable → caller's `.blockedOnReply` store, parametric in the
              -- final state `S` (either `st4` or the call-path fold of `st4`).
              have hTcbInSt4 : ∀ x : SeLe4n.ThreadId, x ≠ caller →
                  st.scheduler.currentOnCore bootCoreId = some x →
                  ∃ tcb, st4.objects[x.toObjId]? = some (.tcb tcb) := by
                intro x hEq' hCurr
                have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by
                  simp [currentThreadValid, hCurr] at hCTV; exact hCTV
                rcases hCTV' with ⟨tcbX, hTcbX⟩
                obtain ⟨tcb1, hTcb1⟩ := endpointQueuePopHead_tcb_forward endpointId true st pair.2.2 pair.1 x.toObjId tcbX hObjInv hPop hTcbX
                have hNeCaller : x.toObjId ≠ caller.toObjId := fun h => hEq' (threadId_toObjId_injective h)
                have hTcb2 : ∃ tcb2, st2.objects[x.toObjId]? = some (.tcb tcb2) := by
                  by_cases hNeTid : x.toObjId = pair.1.toObjId
                  · have hTargetTcb : ∃ t, pair.2.2.objects[pair.1.toObjId]? = some (.tcb t) := hNeTid ▸ ⟨tcb1, hTcb1⟩
                    have h := storeTcbIpcStateAndMessage_tcb_exists_at_target pair.2.2 st2 pair.1 .ready (some (sendPayloadMessage st caller payload)) hObjInvPop hMsg hTargetTcb
                    rwa [← hNeTid] at h
                  · exact ⟨tcb1, (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 .ready (some (sendPayloadMessage st caller payload)) x.toObjId hNeTid hObjInvPop hMsg) ▸ hTcb1⟩
                rcases hTcb2 with ⟨tcb2, hTcb2⟩
                rw [storeTcbIpcStateAndMessage_preserves_objects_ne _ st4 caller _ none x.toObjId hNeCaller hObjInvEns hIpc]
                exact (ensureRunnable_objectsAgreeOffRunLinks _ _).exists_tcb_iff.mpr ⟨tcb2, hTcb2⟩
              -- WS-SM SM6.D (#7.3 fold): thread the server-first reply link.  Generalise
              -- over the final state `S` (`st4` or the fold; both share `st4`'s scheduler),
              -- proving the bundle from a scheduler-equality to `st4` and a current-TCB
              -- forwarder.  The `linkServerStashedReply` fold is scheduler-preserving, so
              -- the `ensureRunnable`-added `pair.1` reasoning is unchanged.
              suffices hGoal : ∀ S : SystemState, S.scheduler = st4.scheduler →
                  (∀ x : SeLe4n.ThreadId, x ≠ caller →
                    st.scheduler.currentOnCore bootCoreId = some x →
                    ∃ tcb, S.objects[x.toObjId]? = some (.tcb tcb)) →
                  st' = removeRunnable S caller →
                  schedulerInvariantBundle st' by
                cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
                | error e => simp [hLink] at hStep
                | ok pL =>
                  obtain ⟨_, st5⟩ := pL
                  simp only [hLink, Except.ok.injEq, Prod.mk.injEq] at hStep
                  obtain ⟨_, hEq⟩ := hStep
                  have hSchedSt5 : st5.scheduler = st4.scheduler :=
                    linkServerStashedReply_scheduler_eq st4 st5 caller pair.1 hLink
                  refine hGoal st5 hSchedSt5 (fun x hEq' hCurr => ?_) hEq.symm
                  obtain ⟨tcb4, hTcb4⟩ := hTcbInSt4 x hEq' hCurr
                  exact linkServerStashedReply_tcb_forward st4 st5 caller pair.1 x.toObjId tcb4 hObjInvIpc hLink hTcb4
              -- Discharge the generalised bundle for an arbitrary `S` with `S.scheduler = st4.scheduler`.
              intro S hSchedS hTcbS hEq; subst hEq
              refine ⟨?_, ?_, ?_⟩
              · unfold queueCurrentConsistent
                rw [removeRunnable_scheduler_current, hSchedS, hCurrEq]
                cases hCurr : (st.scheduler.currentOnCore bootCoreId) with
                | none => simp
                | some x =>
                  by_cases hEq' : x = caller
                  · subst hEq'; simp
                  · rw [if_neg (show ¬(some x = some caller) from fun h => hEq' (Option.some.inj h))]
                    show x ∉ (removeRunnable S caller).scheduler.runnable
                    have hNotMem : x ∉ st.scheduler.runnable := by
                      have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this
                    have hNePair : x ≠ pair.1 := by
                      have hHeadEq := endpointQueuePopHead_returns_head endpointId true st ep pair.1 pair.2.2 hObj hPop
                      simp at hHeadEq
                      intro hEq; rw [hEq] at hCurr
                      have := hCurrNotHead; simp [currentNotEndpointQueueHead, hCurr] at this
                      exact (this endpointId ep hObj).1 hHeadEq
                    apply removeRunnable_not_mem_of_not_mem
                    rw [congrArg SchedulerState.runnable hSchedS, congrArg SchedulerState.runnable hSchedIpc]
                    exact ensureRunnable_not_mem_of_not_mem _ pair.1 x
                      (by rw [congrArg SchedulerState.runnable hSchedMsg, congrArg SchedulerState.runnable hSchedPop]; exact hNotMem)
                      hNePair
              · apply removeRunnable_nodup
                rw [congrArg SchedulerState.runnable hSchedS, congrArg SchedulerState.runnable hSchedIpc]
                apply ensureRunnable_nodup
                rw [congrArg SchedulerState.runnable hSchedMsg, congrArg SchedulerState.runnable hSchedPop]
                exact hRQU
              · unfold currentThreadValid
                rw [removeRunnable_scheduler_current, hSchedS, hCurrEq]
                cases hCurr : (st.scheduler.currentOnCore bootCoreId) with
                | none => simp
                | some x =>
                  by_cases hEq' : x = caller
                  · subst hEq'; simp
                  · rw [if_neg (show ¬(some x = some caller) from fun h => hEq' (Option.some.inj h))]
                    refine (removeRunnable_objectsAgreeOffRunLinks _ _).exists_tcb_iff.mpr ?_
                    show ∃ tcb, S.objects[x.toObjId]? = some (.tcb tcb)
                    exact hTcbS x hEq' hCurr
      | none =>
        -- Blocking: Enqueue → storeTcbIpcStateAndMessage → removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hSchedEnq := endpointQueueEnqueue_scheduler_eq endpointId false caller st st1 hEnq
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false caller st st1 hObjInv hEnq
          cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) none with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            refine schedulerInvariantBundle_of_objectsAgreeOffRunLinks (recordSendCap_objectsAgreeOffRunLinks _ _ _ _) rfl ?_
            have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq st1 st2 caller (.blockedOnCall endpointId) none hMsg
            have hSchedEq : st2.scheduler = st.scheduler := hSchedMsg.trans hSchedEnq
            refine ⟨?_, ?_, ?_⟩
            · unfold queueCurrentConsistent
              rw [removeRunnable_scheduler_current, hSchedEq]
              cases hCurr : (st.scheduler.currentOnCore bootCoreId) with
              | none => simp
              | some x =>
                by_cases hEq' : x = caller
                · subst hEq'; simp
                · rw [if_neg (show ¬(some x = some caller) from fun h => hEq' (Option.some.inj h))]
                  show x ∉ (removeRunnable st2 caller).scheduler.runnable
                  have hNotMem : x ∉ st.scheduler.runnable := by
                    have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this
                  exact removeRunnable_not_mem_of_not_mem st2 caller x (hSchedEq ▸ hNotMem)
            · exact removeRunnable_nodup st2 caller (hSchedEq ▸ hRQU)
            · unfold currentThreadValid
              rw [removeRunnable_scheduler_current,
                  hSchedEq]
              cases hCurr : (st.scheduler.currentOnCore bootCoreId) with
              | none => simp
              | some x =>
                by_cases hEq' : x = caller
                · subst hEq'; simp
                · rw [if_neg (show ¬(some x = some caller) from fun h => hEq' (Option.some.inj h))]
                  refine (removeRunnable_objectsAgreeOffRunLinks _ _).exists_tcb_iff.mpr ?_
                  show ∃ tcb, st2.objects[x.toObjId]? = some (.tcb tcb)
                  have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by
                    simp [currentThreadValid, hCurr] at hCTV; exact hCTV
                  rcases hCTV' with ⟨tcbX, hTcbX⟩
                  obtain ⟨tcb1, hTcb1⟩ := endpointQueueEnqueue_tcb_forward endpointId false caller st st1 x.toObjId tcbX hObjInv hEnq hTcbX
                  have hNeTid : x.toObjId ≠ caller.toObjId := fun h => hEq' (threadId_toObjId_injective h)
                  exact ⟨tcb1, (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 caller (.blockedOnCall endpointId) none x.toObjId hNeTid hObjInv1 hMsg) ▸ hTcb1⟩

/-- WS-F1/TPI-D09: endpointCall preserves ipcSchedulerContractPredicates. -/
theorem endpointCall_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (payload : SendPayload)
    (hContract : ipcSchedulerContractPredicates st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointCall endpointId caller payload st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hContract with ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply, hBlockNotif⟩
  unfold endpointCall SystemState.getObject? at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ | frame _ | pageTable _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        -- Handshake: PopHead → storeTcbIpcStateAndMessage(.ready) → ensureRunnable → storeTcbIpcState(.blockedOnReply) → removeRunnable
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hSchedPop := endpointQueuePopHead_scheduler_eq endpointId true st pair.2.2 pair.1 hPop
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          have hContractPop := contracts_of_same_scheduler_ipcState st pair.2.2 hSchedPop
            (fun tid tcb' h => endpointQueuePopHead_tcb_ipcState_backward endpointId true st pair.2.2 pair.1 tid tcb' hObjInv hPop h)
            ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply, hBlockNotif⟩
          cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some (sendPayloadMessage st caller payload)) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg] at hStep
            have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq pair.2.2 st2 pair.1 .ready (some (sendPayloadMessage st caller payload)) hMsg
            have hObjInvMsg := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 .ready (some (sendPayloadMessage st caller payload)) hObjInv1 hMsg
            have hObjInvEns : (ensureRunnable st2 pair.1).objects.invExt := ensureRunnable_objects_invExt _ _ (by assumption)
            -- AK1-C (I-M01): storeTcbIpcStateAndMessage replaces storeTcbIpcState to atomically clear caller's pendingMessage
            cases hIpc : storeTcbIpcStateAndMessage (ensureRunnable st2 pair.1) caller (.blockedOnReply endpointId (some pair.1)) none with
            | error e => simp [hIpc] at hStep
            | ok st4 =>
              simp only [hIpc] at hStep
              have hObjInvIpc := storeTcbIpcStateAndMessage_preserves_objects_invExt (ensureRunnable st2 pair.1) st4 caller (.blockedOnReply endpointId (some pair.1)) none hObjInvEns hIpc
              have hSchedIpc := storeTcbIpcStateAndMessage_scheduler_eq (ensureRunnable st2 pair.1) st4 caller (.blockedOnReply endpointId (some pair.1)) none hIpc
              -- WS-SM SM6.D (#7.3 fold): thread the server-first reply link.  The fold is
              -- scheduler-preserving and only rewrites TCB `replyObject` /
              -- `pendingReceiveReply` fields (never `ipcState`), so the contracts at the
              -- post-`removeRunnable` `st5`-state transport from the post-`removeRunnable`
              -- `st4`-state via `contracts_of_same_scheduler_ipcState` — leaving the
              -- six-conjunct backward reasoning for `removeRunnable st4 caller` unchanged.
              suffices hContract4 : ipcSchedulerContractPredicates (removeRunnable st4 caller) by
                cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
                | error e => simp [hLink] at hStep
                | ok pL =>
                  obtain ⟨_, st5⟩ := pL
                  simp only [hLink, Except.ok.injEq, Prod.mk.injEq] at hStep
                  obtain ⟨_, hEq⟩ := hStep; subst hEq
                  have hSched5 : st5.scheduler = st4.scheduler :=
                    linkServerStashedReply_scheduler_eq st4 st5 caller pair.1 hLink
                  refine contracts_of_runnable_eq_ipcState (removeRunnable st4 caller)
                    (removeRunnable st5 caller) ?_ ?_ hContract4
                  · -- the dequeue's queue reads only the scheduler, which the fold keeps.
                    simp only [SchedulerState.runnable, removeRunnable_scheduler, hSched5,
                      SchedulerState.markReschedulePendingOnCoreIf_runQueueOnCore,
                      SchedulerState.setCurrentOnCore_runQueueOnCore,
                      SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
                  · -- ipcState-backward across the fold (objects survive `removeRunnable`).
                    intro tid tcb' hTcb'
                    run_links_back (removeRunnable_objectsAgreeOffRunLinks _ _) at tcb' hTcb'
                    obtain ⟨tcb, hTcb, hIpcEq⟩ :=
                      linkServerStashedReply_tcb_ipcState_backward st4 st5 caller pair.1 tid tcb' hObjInvIpc hLink hTcb'
                    run_links_fwd (removeRunnable_objectsAgreeOffRunLinks st4 caller) at tcb hTcb
                    exact ⟨_, hTcb, hIpcEq⟩
              rcases hContractPop with ⟨hReady', hBlockSend', hBlockRecv', hBlockCall', hBlockReply', hBlockNotif'⟩
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
              · -- runnableThreadIpcReady
                intro tid tcb' hTcb' hRun'
                run_links_back (removeRunnable_objectsAgreeOffRunLinks _ _) at tcb' hTcb'
                by_cases hNeCaller : tid = caller
                · subst hNeCaller; exact absurd hRun' (removeRunnable_not_mem_self st4 _)
                · have hNeCallerObjId : tid.toObjId ≠ caller.toObjId := fun h => hNeCaller (threadId_toObjId_injective h)
                  rw [storeTcbIpcStateAndMessage_preserves_objects_ne _ st4 caller _ none tid.toObjId hNeCallerObjId hObjInvEns hIpc] at hTcb'
                  run_links_back (ensureRunnable_objectsAgreeOffRunLinks _ _) at tcb' hTcb'
                  by_cases hNeRecv : tid.toObjId = pair.1.toObjId
                  · exact storeTcbIpcStateAndMessage_ipcState_eq pair.2.2 st2 pair.1 .ready (some (sendPayloadMessage st caller payload)) hObjInv1 hMsg tcb' (hNeRecv ▸ hTcb')
                  · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 .ready (some (sendPayloadMessage st caller payload)) tid.toObjId hNeRecv hObjInv1 hMsg).symm.trans hTcb'
                    have hNeTid : tid ≠ pair.1 := fun h => hNeRecv (congrArg ThreadId.toObjId h)
                    have ⟨hRunSt4, _⟩ := (removeRunnable_runnable_mem st4 caller tid).mp hRun'
                    rw [congrArg SchedulerState.runnable hSchedIpc] at hRunSt4
                    rcases ensureRunnable_mem_reverse st2 pair.1 tid hRunSt4 with hOld | hEq
                    · exact hReady' tid tcb' hTcbPre (show tid ∈ pair.2.2.scheduler.runnable by rwa [← hSchedMsg])
                    · exact absurd hEq hNeTid
              · -- blockedOnSendNotRunnable
                intro tid tcb' eid hTcb' hIpcState'
                run_links_back (removeRunnable_objectsAgreeOffRunLinks _ _) at tcb' hTcb'
                by_cases hNeCaller : tid = caller
                · subst hNeCaller; exact removeRunnable_not_mem_self st4 _
                · have hNeCallerObjId : tid.toObjId ≠ caller.toObjId := fun h => hNeCaller (threadId_toObjId_injective h)
                  rw [storeTcbIpcStateAndMessage_preserves_objects_ne _ st4 caller _ none tid.toObjId hNeCallerObjId hObjInvEns hIpc] at hTcb'
                  run_links_back (ensureRunnable_objectsAgreeOffRunLinks _ _) at tcb' hTcb'
                  by_cases hNeRecv : tid.toObjId = pair.1.toObjId
                  · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2.2 st2 pair.1 .ready (some (sendPayloadMessage st caller payload)) hObjInv1 hMsg tcb' (hNeRecv ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hNeTid : tid ≠ pair.1 := fun h => hNeRecv (congrArg ThreadId.toObjId h)
                    have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 .ready (some (sendPayloadMessage st caller payload)) tid.toObjId hNeRecv hObjInv1 hMsg).symm.trans hTcb'
                    intro hRun'
                    have ⟨hRunSt4, _⟩ := (removeRunnable_runnable_mem st4 caller tid).mp hRun'
                    rw [congrArg SchedulerState.runnable hSchedIpc] at hRunSt4
                    rcases ensureRunnable_mem_reverse st2 pair.1 tid hRunSt4 with hOld | hEq
                    · exact hBlockSend' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.2.scheduler.runnable by rwa [← hSchedMsg])
                    · exact absurd hEq hNeTid
              · -- blockedOnReceiveNotRunnable
                intro tid tcb' eid hTcb' hIpcState'
                run_links_back (removeRunnable_objectsAgreeOffRunLinks _ _) at tcb' hTcb'
                by_cases hNeCaller : tid = caller
                · subst hNeCaller; exact removeRunnable_not_mem_self st4 _
                · have hNeCallerObjId : tid.toObjId ≠ caller.toObjId := fun h => hNeCaller (threadId_toObjId_injective h)
                  rw [storeTcbIpcStateAndMessage_preserves_objects_ne _ st4 caller _ none tid.toObjId hNeCallerObjId hObjInvEns hIpc] at hTcb'
                  run_links_back (ensureRunnable_objectsAgreeOffRunLinks _ _) at tcb' hTcb'
                  by_cases hNeRecv : tid.toObjId = pair.1.toObjId
                  · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2.2 st2 pair.1 .ready (some (sendPayloadMessage st caller payload)) hObjInv1 hMsg tcb' (hNeRecv ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hNeTid : tid ≠ pair.1 := fun h => hNeRecv (congrArg ThreadId.toObjId h)
                    have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 .ready (some (sendPayloadMessage st caller payload)) tid.toObjId hNeRecv hObjInv1 hMsg).symm.trans hTcb'
                    intro hRun'
                    have ⟨hRunSt4, _⟩ := (removeRunnable_runnable_mem st4 caller tid).mp hRun'
                    rw [congrArg SchedulerState.runnable hSchedIpc] at hRunSt4
                    rcases ensureRunnable_mem_reverse st2 pair.1 tid hRunSt4 with hOld | hEq
                    · exact hBlockRecv' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.2.scheduler.runnable by rwa [← hSchedMsg])
                    · exact absurd hEq hNeTid
              · -- blockedOnCallNotRunnable
                intro tid tcb' eid hTcb' hIpcState'
                run_links_back (removeRunnable_objectsAgreeOffRunLinks _ _) at tcb' hTcb'
                by_cases hNeCaller : tid = caller
                · subst hNeCaller; exact removeRunnable_not_mem_self st4 _
                · have hNeCallerObjId : tid.toObjId ≠ caller.toObjId := fun h => hNeCaller (threadId_toObjId_injective h)
                  rw [storeTcbIpcStateAndMessage_preserves_objects_ne _ st4 caller _ none tid.toObjId hNeCallerObjId hObjInvEns hIpc] at hTcb'
                  run_links_back (ensureRunnable_objectsAgreeOffRunLinks _ _) at tcb' hTcb'
                  by_cases hNeRecv : tid.toObjId = pair.1.toObjId
                  · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2.2 st2 pair.1 .ready (some (sendPayloadMessage st caller payload)) hObjInv1 hMsg tcb' (hNeRecv ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hNeTid : tid ≠ pair.1 := fun h => hNeRecv (congrArg ThreadId.toObjId h)
                    have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 .ready (some (sendPayloadMessage st caller payload)) tid.toObjId hNeRecv hObjInv1 hMsg).symm.trans hTcb'
                    intro hRun'
                    have ⟨hRunSt4, _⟩ := (removeRunnable_runnable_mem st4 caller tid).mp hRun'
                    rw [congrArg SchedulerState.runnable hSchedIpc] at hRunSt4
                    rcases ensureRunnable_mem_reverse st2 pair.1 tid hRunSt4 with hOld | hEq
                    · exact hBlockCall' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.2.scheduler.runnable by rwa [← hSchedMsg])
                    · exact absurd hEq hNeTid
              · -- blockedOnReplyNotRunnable
                intro tid tcb' eid rt hTcb' hIpcState'
                run_links_back (removeRunnable_objectsAgreeOffRunLinks _ _) at tcb' hTcb'
                by_cases hNeCaller : tid = caller
                · subst hNeCaller; exact removeRunnable_not_mem_self st4 _
                · have hNeCallerObjId : tid.toObjId ≠ caller.toObjId := fun h => hNeCaller (threadId_toObjId_injective h)
                  rw [storeTcbIpcStateAndMessage_preserves_objects_ne _ st4 caller _ none tid.toObjId hNeCallerObjId hObjInvEns hIpc] at hTcb'
                  run_links_back (ensureRunnable_objectsAgreeOffRunLinks _ _) at tcb' hTcb'
                  by_cases hNeRecv : tid.toObjId = pair.1.toObjId
                  · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2.2 st2 pair.1 .ready (some (sendPayloadMessage st caller payload)) hObjInv1 hMsg tcb' (hNeRecv ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hNeTid : tid ≠ pair.1 := fun h => hNeRecv (congrArg ThreadId.toObjId h)
                    have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 .ready (some (sendPayloadMessage st caller payload)) tid.toObjId hNeRecv hObjInv1 hMsg).symm.trans hTcb'
                    intro hRun'
                    have ⟨hRunSt4, _⟩ := (removeRunnable_runnable_mem st4 caller tid).mp hRun'
                    rw [congrArg SchedulerState.runnable hSchedIpc] at hRunSt4
                    rcases ensureRunnable_mem_reverse st2 pair.1 tid hRunSt4 with hOld | hEq
                    · exact hBlockReply' tid tcb' eid rt hTcbPre hIpcState' (show tid ∈ pair.2.2.scheduler.runnable by rwa [← hSchedMsg])
                    · exact absurd hEq hNeTid
              · -- blockedOnNotificationNotRunnable (WS-F6/D2)
                intro tid tcb' nid hTcb' hIpcState'
                run_links_back (removeRunnable_objectsAgreeOffRunLinks _ _) at tcb' hTcb'
                by_cases hNeCaller : tid = caller
                · subst hNeCaller; exact removeRunnable_not_mem_self st4 _
                · have hNeCallerObjId : tid.toObjId ≠ caller.toObjId := fun h => hNeCaller (threadId_toObjId_injective h)
                  rw [storeTcbIpcStateAndMessage_preserves_objects_ne _ st4 caller _ none tid.toObjId hNeCallerObjId hObjInvEns hIpc] at hTcb'
                  run_links_back (ensureRunnable_objectsAgreeOffRunLinks _ _) at tcb' hTcb'
                  by_cases hNeRecv : tid.toObjId = pair.1.toObjId
                  · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2.2 st2 pair.1 .ready (some (sendPayloadMessage st caller payload)) hObjInv1 hMsg tcb' (hNeRecv ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hNeTid : tid ≠ pair.1 := fun h => hNeRecv (congrArg ThreadId.toObjId h)
                    have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 .ready (some (sendPayloadMessage st caller payload)) tid.toObjId hNeRecv hObjInv1 hMsg).symm.trans hTcb'
                    intro hRun'
                    have ⟨hRunSt4, _⟩ := (removeRunnable_runnable_mem st4 caller tid).mp hRun'
                    rw [congrArg SchedulerState.runnable hSchedIpc] at hRunSt4
                    rcases ensureRunnable_mem_reverse st2 pair.1 tid hRunSt4 with hOld | hEq
                    · exact hBlockNotif' tid tcb' nid hTcbPre hIpcState' (show tid ∈ pair.2.2.scheduler.runnable by rwa [← hSchedMsg])
                    · exact absurd hEq hNeTid
      | none =>
        -- Blocking: Enqueue → storeTcbIpcStateAndMessage → removeRunnable (same as SendDual blocking)
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hSchedEnq := endpointQueueEnqueue_scheduler_eq endpointId false caller st st1 hEnq
          have hObjInvEnq := endpointQueueEnqueue_preserves_objects_invExt endpointId false caller st st1 hObjInv hEnq
          have hContractEnq := contracts_of_same_scheduler_ipcState st st1 hSchedEnq
            (fun tid tcb' h => endpointQueueEnqueue_tcb_ipcState_backward endpointId false caller st st1 tid tcb' hObjInv hEnq h)
            ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply, hBlockNotif⟩
          cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) none with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            refine ipcSchedulerContractPredicates_of_objectsAgreeOffRunLinks (recordSendCap_objectsAgreeOffRunLinks _ _ _ _) rfl ?_
            rcases hContractEnq with ⟨hReady', hBlockSend', hBlockRecv', hBlockCall', hBlockReply', hBlockNotif'⟩
            have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq st1 st2 caller (.blockedOnCall endpointId) none hMsg
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
            · intro tid tcb' hTcb' hRun'
              run_links_back (removeRunnable_objectsAgreeOffRunLinks _ _) at tcb' hTcb'
              by_cases hNe : tid = caller
              · subst hNe; exact absurd hRun' (removeRunnable_not_mem_self st2 _)
              · have hNeObjId : tid.toObjId ≠ caller.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 caller _ none tid.toObjId hNeObjId hObjInvEnq hMsg).symm.trans hTcb'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 caller tid).mp hRun'
                exact hReady' tid tcb' hTcbPre (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])
            · intro tid tcb' eid hTcb' hIpcState'
              run_links_back (removeRunnable_objectsAgreeOffRunLinks _ _) at tcb' hTcb'
              by_cases hNe : tid = caller
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ caller.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 caller _ none tid.toObjId hNeObjId hObjInvEnq hMsg).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 caller tid).mp hRun'
                exact hBlockSend' tid tcb' eid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])
            · intro tid tcb' eid hTcb' hIpcState'
              run_links_back (removeRunnable_objectsAgreeOffRunLinks _ _) at tcb' hTcb'
              by_cases hNe : tid = caller
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ caller.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 caller _ none tid.toObjId hNeObjId hObjInvEnq hMsg).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 caller tid).mp hRun'
                exact hBlockRecv' tid tcb' eid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])
            · intro tid tcb' eid hTcb' hIpcState'
              run_links_back (removeRunnable_objectsAgreeOffRunLinks _ _) at tcb' hTcb'
              by_cases hNe : tid = caller
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ caller.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 caller _ none tid.toObjId hNeObjId hObjInvEnq hMsg).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 caller tid).mp hRun'
                exact hBlockCall' tid tcb' eid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])
            · intro tid tcb' eid rt hTcb' hIpcState'
              run_links_back (removeRunnable_objectsAgreeOffRunLinks _ _) at tcb' hTcb'
              by_cases hNe : tid = caller
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ caller.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 caller _ none tid.toObjId hNeObjId hObjInvEnq hMsg).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 caller tid).mp hRun'
                exact hBlockReply' tid tcb' eid rt hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])
            · -- blockedOnNotificationNotRunnable (WS-F6/D2)
              intro tid tcb' nid hTcb' hIpcState'
              run_links_back (removeRunnable_objectsAgreeOffRunLinks _ _) at tcb' hTcb'
              by_cases hNe : tid = caller
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ caller.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 caller _ none tid.toObjId hNeObjId hObjInvEnq hMsg).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 caller tid).mp hRun'
                exact hBlockNotif' tid tcb' nid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])

/-- WS-H1/C-01: A Call sender that enters the endpoint call path does not
remain runnable after the operation completes. Both execution paths
(rendezvous and no-rendezvous) end with `removeRunnable ... caller`,
ensuring the caller blocks until an explicit reply. -/
theorem endpointCall_blocked_stays_blocked
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (payload : SendPayload)
    (hStep : endpointCall endpointId caller payload st = .ok ((), st')) :
    caller ∉ st'.scheduler.runnable := by
  unfold endpointCall SystemState.getObject? at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ | frame _ | pageTable _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        simp only [hHead] at hStep
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hPop] at hStep
        | ok pair =>
          simp only [hPop] at hStep
          cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some (sendPayloadMessage st caller payload)) with
          | error e => simp [hMsg] at hStep
          | ok st'' =>
            simp only [hMsg] at hStep
            -- AK1-C (I-M01): storeTcbIpcStateAndMessage replaces storeTcbIpcState to atomically clear caller's pendingMessage
            cases hIpc : storeTcbIpcStateAndMessage (ensureRunnable st'' pair.1) caller
                (.blockedOnReply endpointId (some pair.1)) none with
            | error e => simp [hIpc] at hStep
            | ok st4 =>
              simp only [hIpc] at hStep
              -- WS-SM SM6.D (#7.3 fold): the server-first reply link sits between the
              -- caller's `.blockedOnReply` store and the final `removeRunnable`; the
              -- caller is still descheduled in the final state.
              cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
              | error e => simp [hLink] at hStep
              | ok pL =>
                obtain ⟨_, st5⟩ := pL
                simp only [hLink, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                exact removeRunnable_not_mem_self st5 caller
      | none =>
        simp only [hHead] at hStep
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hEnq] at hStep
        | ok st1 =>
          simp only [hEnq] at hStep
          cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) none with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact removeRunnable_not_mem_self st2 caller

end SeLe4n.Kernel
