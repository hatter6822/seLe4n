import SeLe4n.Kernel.IPC.Invariant.EndpointPreservation

namespace SeLe4n.Kernel

open SeLe4n.Model

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
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcInvariant st)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    ipcInvariant st' := by
  unfold endpointCall at hStep
  -- WS-H12d: Eliminate bounds-check if-branches (error cases contradict hStep : ... = .ok ...)
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        -- Handshake: PopHead → storeTcbIpcStateAndMessage → ensureRunnable → storeTcbIpcState → removeRunnable
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hInv1 := endpointQueuePopHead_preserves_ipcInvariant endpointId true st pair.2 pair.1 hInv hPop
          cases hMsg : storeTcbIpcStateAndMessage pair.2 pair.1 .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg] at hStep
            have hInv2 := storeTcbIpcStateAndMessage_preserves_ipcInvariant pair.2 st2 pair.1 .ready (some msg) hInv1 hMsg
            have hInv3 : ipcInvariant (ensureRunnable st2 pair.1) :=
              fun oid ntfn h => hInv2 oid ntfn (by rwa [ensureRunnable_preserves_objects] at h)
            cases hIpc : storeTcbIpcState (ensureRunnable st2 pair.1) caller (.blockedOnReply endpointId (some pair.1)) with
            | error e => simp [hIpc] at hStep
            | ok st4 =>
              simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hEq⟩ := hStep; subst hEq
              have hInv4 := storeTcbIpcState_preserves_ipcInvariant _ st4 caller _ hInv3 hIpc
              exact fun oid ntfn h => hInv4 oid ntfn (by rwa [removeRunnable_preserves_objects] at h)
      | none =>
        -- Blocking: Enqueue → storeTcbIpcStateAndMessage → removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hInv1 := endpointQueueEnqueue_preserves_ipcInvariant endpointId false caller st st1 hInv hEnq
          cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hInv2 := storeTcbIpcStateAndMessage_preserves_ipcInvariant st1 st2 caller _ (some msg) hInv1 hMsg
            exact fun oid ntfn h => hInv2 oid ntfn (by rwa [removeRunnable_preserves_objects] at h)

/-- WS-F1/TPI-D09: endpointCall preserves schedulerInvariantBundle. -/
theorem endpointCall_preserves_schedulerInvariantBundle
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : schedulerInvariantBundle st)
    (hCurrNotHead : currentNotEndpointQueueHead st)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  rcases hInv with ⟨hQCC, hRQU, hCTV⟩
  unfold endpointCall at hStep
  -- WS-H12d: Eliminate bounds-check if-branches (error cases contradict hStep : ... = .ok ...)
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        -- Handshake: PopHead → storeTcbIpcStateAndMessage → ensureRunnable → storeTcbIpcState → removeRunnable
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hSchedPop := endpointQueuePopHead_scheduler_eq endpointId true st pair.2 pair.1 hPop
          cases hMsg : storeTcbIpcStateAndMessage pair.2 pair.1 .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg] at hStep
            have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq pair.2 st2 pair.1 .ready (some msg) hMsg
            cases hIpc : storeTcbIpcState (ensureRunnable st2 pair.1) caller (.blockedOnReply endpointId (some pair.1)) with
            | error e => simp [hIpc] at hStep
            | ok st4 =>
              simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hEq⟩ := hStep; subst hEq
              have hSchedIpc := storeTcbIpcState_scheduler_eq (ensureRunnable st2 pair.1) st4 caller (.blockedOnReply endpointId (some pair.1)) hIpc
              have hCurrEq : st4.scheduler.current = st.scheduler.current := by
                rw [congrArg SchedulerState.current hSchedIpc, ensureRunnable_scheduler_current,
                    congrArg SchedulerState.current hSchedMsg, congrArg SchedulerState.current hSchedPop]
              refine ⟨?_, ?_, ?_⟩
              · unfold queueCurrentConsistent
                rw [removeRunnable_scheduler_current, hCurrEq]
                cases hCurr : st.scheduler.current with
                | none => simp
                | some x =>
                  by_cases hEq' : x = caller
                  · subst hEq'; simp
                  · rw [if_neg (show ¬(some x = some caller) from fun h => hEq' (Option.some.inj h))]
                    show x ∉ (removeRunnable st4 caller).scheduler.runnable
                    have hNotMem : x ∉ st.scheduler.runnable := by
                      have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this
                    have hNePair : x ≠ pair.1 := by
                      have hHeadEq := endpointQueuePopHead_returns_head endpointId true st ep pair.1 pair.2 hObj hPop
                      simp at hHeadEq
                      intro hEq; rw [hEq] at hCurr
                      have := hCurrNotHead; simp [currentNotEndpointQueueHead, hCurr] at this
                      exact (this endpointId ep hObj).1 hHeadEq
                    apply removeRunnable_not_mem_of_not_mem
                    rw [congrArg SchedulerState.runnable hSchedIpc]
                    exact ensureRunnable_not_mem_of_not_mem _ pair.1 x
                      (by rw [congrArg SchedulerState.runnable hSchedMsg, congrArg SchedulerState.runnable hSchedPop]; exact hNotMem)
                      hNePair
              · apply removeRunnable_nodup
                rw [congrArg SchedulerState.runnable hSchedIpc]
                apply ensureRunnable_nodup
                rw [congrArg SchedulerState.runnable hSchedMsg, congrArg SchedulerState.runnable hSchedPop]
                exact hRQU
              · unfold currentThreadValid
                rw [removeRunnable_preserves_objects, removeRunnable_scheduler_current, hCurrEq]
                cases hCurr : st.scheduler.current with
                | none => simp
                | some x =>
                  by_cases hEq' : x = caller
                  · subst hEq'; simp
                  · rw [if_neg (show ¬(some x = some caller) from fun h => hEq' (Option.some.inj h))]
                    show ∃ tcb, st4.objects[x.toObjId]? = some (.tcb tcb)
                    have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by
                      simp [currentThreadValid, hCurr] at hCTV; exact hCTV
                    rcases hCTV' with ⟨tcbX, hTcbX⟩
                    obtain ⟨tcb1, hTcb1⟩ := endpointQueuePopHead_tcb_forward endpointId true st pair.2 pair.1 x.toObjId tcbX hPop hTcbX
                    have hNeCaller : x.toObjId ≠ caller.toObjId := fun h => hEq' (threadId_toObjId_injective h)
                    have hTcb2 : ∃ tcb2, st2.objects[x.toObjId]? = some (.tcb tcb2) := by
                      by_cases hNeTid : x.toObjId = pair.1.toObjId
                      · have hTargetTcb : ∃ t, pair.2.objects[pair.1.toObjId]? = some (.tcb t) := hNeTid ▸ ⟨tcb1, hTcb1⟩
                        have h := storeTcbIpcStateAndMessage_tcb_exists_at_target pair.2 st2 pair.1 .ready (some msg) hMsg hTargetTcb
                        rwa [← hNeTid] at h
                      · exact ⟨tcb1, (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready (some msg) x.toObjId hNeTid hMsg) ▸ hTcb1⟩
                    rcases hTcb2 with ⟨tcb2, hTcb2⟩
                    exact ⟨tcb2, by rw [storeTcbIpcState_preserves_objects_ne _ st4 caller _ x.toObjId hNeCaller hIpc, ensureRunnable_preserves_objects]; exact hTcb2⟩
      | none =>
        -- Blocking: Enqueue → storeTcbIpcStateAndMessage → removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hSchedEnq := endpointQueueEnqueue_scheduler_eq endpointId false caller st st1 hEnq
          cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq st1 st2 caller (.blockedOnCall endpointId) (some msg) hMsg
            have hSchedEq : st2.scheduler = st.scheduler := hSchedMsg.trans hSchedEnq
            refine ⟨?_, ?_, ?_⟩
            · unfold queueCurrentConsistent
              rw [removeRunnable_scheduler_current, congrArg SchedulerState.current hSchedEq]
              cases hCurr : st.scheduler.current with
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
              rw [removeRunnable_preserves_objects, removeRunnable_scheduler_current,
                  congrArg SchedulerState.current hSchedEq]
              cases hCurr : st.scheduler.current with
              | none => simp
              | some x =>
                by_cases hEq' : x = caller
                · subst hEq'; simp
                · rw [if_neg (show ¬(some x = some caller) from fun h => hEq' (Option.some.inj h))]
                  show ∃ tcb, st2.objects[x.toObjId]? = some (.tcb tcb)
                  have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by
                    simp [currentThreadValid, hCurr] at hCTV; exact hCTV
                  rcases hCTV' with ⟨tcbX, hTcbX⟩
                  obtain ⟨tcb1, hTcb1⟩ := endpointQueueEnqueue_tcb_forward endpointId false caller st st1 x.toObjId tcbX hEnq hTcbX
                  have hNeTid : x.toObjId ≠ caller.toObjId := fun h => hEq' (threadId_toObjId_injective h)
                  exact ⟨tcb1, (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 caller (.blockedOnCall endpointId) (some msg) x.toObjId hNeTid hMsg) ▸ hTcb1⟩

/-- WS-F1/TPI-D09: endpointCall preserves ipcSchedulerContractPredicates. -/
theorem endpointCall_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hContract with ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply⟩
  unfold endpointCall at hStep
  -- WS-H12d: Eliminate bounds-check if-branches (error cases contradict hStep : ... = .ok ...)
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        -- Handshake: PopHead → storeTcbIpcStateAndMessage(.ready) → ensureRunnable → storeTcbIpcState(.blockedOnReply) → removeRunnable
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hSchedPop := endpointQueuePopHead_scheduler_eq endpointId true st pair.2 pair.1 hPop
          have hContractPop := contracts_of_same_scheduler_ipcState st pair.2 hSchedPop
            (fun tid tcb' h => endpointQueuePopHead_tcb_ipcState_backward endpointId true st pair.2 pair.1 tid tcb' hPop h)
            ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply⟩
          cases hMsg : storeTcbIpcStateAndMessage pair.2 pair.1 .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg] at hStep
            have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq pair.2 st2 pair.1 .ready (some msg) hMsg
            cases hIpc : storeTcbIpcState (ensureRunnable st2 pair.1) caller (.blockedOnReply endpointId (some pair.1)) with
            | error e => simp [hIpc] at hStep
            | ok st4 =>
              simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hEq⟩ := hStep; subst hEq
              have hSchedIpc := storeTcbIpcState_scheduler_eq (ensureRunnable st2 pair.1) st4 caller (.blockedOnReply endpointId (some pair.1)) hIpc
              rcases hContractPop with ⟨hReady', hBlockSend', hBlockRecv', hBlockCall', hBlockReply'⟩
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · -- runnableThreadIpcReady
                intro tid tcb' hTcb' hRun'
                rw [removeRunnable_preserves_objects] at hTcb'
                by_cases hNeCaller : tid = caller
                · subst hNeCaller; exact absurd hRun' (removeRunnable_not_mem_self st4 _)
                · have hNeCallerObjId : tid.toObjId ≠ caller.toObjId := fun h => hNeCaller (threadId_toObjId_injective h)
                  rw [storeTcbIpcState_preserves_objects_ne _ st4 caller _ tid.toObjId hNeCallerObjId hIpc, ensureRunnable_preserves_objects] at hTcb'
                  by_cases hNeRecv : tid.toObjId = pair.1.toObjId
                  · exact storeTcbIpcStateAndMessage_ipcState_eq pair.2 st2 pair.1 .ready (some msg) hMsg tcb' (hNeRecv ▸ hTcb')
                  · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready (some msg) tid.toObjId hNeRecv hMsg).symm.trans hTcb'
                    have hNeTid : tid ≠ pair.1 := fun h => hNeRecv (congrArg ThreadId.toObjId h)
                    have ⟨hRunSt4, _⟩ := (removeRunnable_runnable_mem st4 caller tid).mp hRun'
                    rw [congrArg SchedulerState.runnable hSchedIpc] at hRunSt4
                    rcases ensureRunnable_mem_reverse st2 pair.1 tid hRunSt4 with hOld | hEq
                    · exact hReady' tid tcb' hTcbPre (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                    · exact absurd hEq hNeTid
              · -- blockedOnSendNotRunnable
                intro tid tcb' eid hTcb' hIpcState'
                rw [removeRunnable_preserves_objects] at hTcb'
                by_cases hNeCaller : tid = caller
                · subst hNeCaller; exact removeRunnable_not_mem_self st4 _
                · have hNeCallerObjId : tid.toObjId ≠ caller.toObjId := fun h => hNeCaller (threadId_toObjId_injective h)
                  rw [storeTcbIpcState_preserves_objects_ne _ st4 caller _ tid.toObjId hNeCallerObjId hIpc, ensureRunnable_preserves_objects] at hTcb'
                  by_cases hNeRecv : tid.toObjId = pair.1.toObjId
                  · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2 st2 pair.1 .ready (some msg) hMsg tcb' (hNeRecv ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hNeTid : tid ≠ pair.1 := fun h => hNeRecv (congrArg ThreadId.toObjId h)
                    have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready (some msg) tid.toObjId hNeRecv hMsg).symm.trans hTcb'
                    intro hRun'
                    have ⟨hRunSt4, _⟩ := (removeRunnable_runnable_mem st4 caller tid).mp hRun'
                    rw [congrArg SchedulerState.runnable hSchedIpc] at hRunSt4
                    rcases ensureRunnable_mem_reverse st2 pair.1 tid hRunSt4 with hOld | hEq
                    · exact hBlockSend' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                    · exact absurd hEq hNeTid
              · -- blockedOnReceiveNotRunnable
                intro tid tcb' eid hTcb' hIpcState'
                rw [removeRunnable_preserves_objects] at hTcb'
                by_cases hNeCaller : tid = caller
                · subst hNeCaller; exact removeRunnable_not_mem_self st4 _
                · have hNeCallerObjId : tid.toObjId ≠ caller.toObjId := fun h => hNeCaller (threadId_toObjId_injective h)
                  rw [storeTcbIpcState_preserves_objects_ne _ st4 caller _ tid.toObjId hNeCallerObjId hIpc, ensureRunnable_preserves_objects] at hTcb'
                  by_cases hNeRecv : tid.toObjId = pair.1.toObjId
                  · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2 st2 pair.1 .ready (some msg) hMsg tcb' (hNeRecv ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hNeTid : tid ≠ pair.1 := fun h => hNeRecv (congrArg ThreadId.toObjId h)
                    have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready (some msg) tid.toObjId hNeRecv hMsg).symm.trans hTcb'
                    intro hRun'
                    have ⟨hRunSt4, _⟩ := (removeRunnable_runnable_mem st4 caller tid).mp hRun'
                    rw [congrArg SchedulerState.runnable hSchedIpc] at hRunSt4
                    rcases ensureRunnable_mem_reverse st2 pair.1 tid hRunSt4 with hOld | hEq
                    · exact hBlockRecv' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                    · exact absurd hEq hNeTid
              · -- blockedOnCallNotRunnable
                intro tid tcb' eid hTcb' hIpcState'
                rw [removeRunnable_preserves_objects] at hTcb'
                by_cases hNeCaller : tid = caller
                · subst hNeCaller; exact removeRunnable_not_mem_self st4 _
                · have hNeCallerObjId : tid.toObjId ≠ caller.toObjId := fun h => hNeCaller (threadId_toObjId_injective h)
                  rw [storeTcbIpcState_preserves_objects_ne _ st4 caller _ tid.toObjId hNeCallerObjId hIpc, ensureRunnable_preserves_objects] at hTcb'
                  by_cases hNeRecv : tid.toObjId = pair.1.toObjId
                  · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2 st2 pair.1 .ready (some msg) hMsg tcb' (hNeRecv ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hNeTid : tid ≠ pair.1 := fun h => hNeRecv (congrArg ThreadId.toObjId h)
                    have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready (some msg) tid.toObjId hNeRecv hMsg).symm.trans hTcb'
                    intro hRun'
                    have ⟨hRunSt4, _⟩ := (removeRunnable_runnable_mem st4 caller tid).mp hRun'
                    rw [congrArg SchedulerState.runnable hSchedIpc] at hRunSt4
                    rcases ensureRunnable_mem_reverse st2 pair.1 tid hRunSt4 with hOld | hEq
                    · exact hBlockCall' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                    · exact absurd hEq hNeTid
              · -- blockedOnReplyNotRunnable
                intro tid tcb' eid rt hTcb' hIpcState'
                rw [removeRunnable_preserves_objects] at hTcb'
                by_cases hNeCaller : tid = caller
                · subst hNeCaller; exact removeRunnable_not_mem_self st4 _
                · have hNeCallerObjId : tid.toObjId ≠ caller.toObjId := fun h => hNeCaller (threadId_toObjId_injective h)
                  rw [storeTcbIpcState_preserves_objects_ne _ st4 caller _ tid.toObjId hNeCallerObjId hIpc, ensureRunnable_preserves_objects] at hTcb'
                  by_cases hNeRecv : tid.toObjId = pair.1.toObjId
                  · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2 st2 pair.1 .ready (some msg) hMsg tcb' (hNeRecv ▸ hTcb')
                    rw [this] at hIpcState'; cases hIpcState'
                  · have hNeTid : tid ≠ pair.1 := fun h => hNeRecv (congrArg ThreadId.toObjId h)
                    have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2 st2 pair.1 .ready (some msg) tid.toObjId hNeRecv hMsg).symm.trans hTcb'
                    intro hRun'
                    have ⟨hRunSt4, _⟩ := (removeRunnable_runnable_mem st4 caller tid).mp hRun'
                    rw [congrArg SchedulerState.runnable hSchedIpc] at hRunSt4
                    rcases ensureRunnable_mem_reverse st2 pair.1 tid hRunSt4 with hOld | hEq
                    · exact hBlockReply' tid tcb' eid rt hTcbPre hIpcState' (show tid ∈ pair.2.scheduler.runnable by rwa [← hSchedMsg])
                    · exact absurd hEq hNeTid
      | none =>
        -- Blocking: Enqueue → storeTcbIpcStateAndMessage → removeRunnable (same as SendDual blocking)
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hSchedEnq := endpointQueueEnqueue_scheduler_eq endpointId false caller st st1 hEnq
          have hContractEnq := contracts_of_same_scheduler_ipcState st st1 hSchedEnq
            (fun tid tcb' h => endpointQueueEnqueue_tcb_ipcState_backward endpointId false caller st st1 tid tcb' hEnq h)
            ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply⟩
          cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            rcases hContractEnq with ⟨hReady', hBlockSend', hBlockRecv', hBlockCall', hBlockReply'⟩
            have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq st1 st2 caller (.blockedOnCall endpointId) (some msg) hMsg
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · intro tid tcb' hTcb' hRun'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = caller
              · subst hNe; exact absurd hRun' (removeRunnable_not_mem_self st2 _)
              · have hNeObjId : tid.toObjId ≠ caller.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 caller _ (some msg) tid.toObjId hNeObjId hMsg).symm.trans hTcb'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 caller tid).mp hRun'
                exact hReady' tid tcb' hTcbPre (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])
            · intro tid tcb' eid hTcb' hIpcState'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = caller
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ caller.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 caller _ (some msg) tid.toObjId hNeObjId hMsg).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 caller tid).mp hRun'
                exact hBlockSend' tid tcb' eid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])
            · intro tid tcb' eid hTcb' hIpcState'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = caller
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ caller.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 caller _ (some msg) tid.toObjId hNeObjId hMsg).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 caller tid).mp hRun'
                exact hBlockRecv' tid tcb' eid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])
            · intro tid tcb' eid hTcb' hIpcState'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = caller
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ caller.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 caller _ (some msg) tid.toObjId hNeObjId hMsg).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 caller tid).mp hRun'
                exact hBlockCall' tid tcb' eid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])
            · intro tid tcb' eid rt hTcb' hIpcState'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = caller
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ caller.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 caller _ (some msg) tid.toObjId hNeObjId hMsg).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 caller tid).mp hRun'
                exact hBlockReply' tid tcb' eid rt hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])

/-- WS-H1/C-01: A Call sender that enters the endpoint call path does not
remain runnable after the operation completes. Both execution paths
(rendezvous and no-rendezvous) end with `removeRunnable ... caller`,
ensuring the caller blocks until an explicit reply. -/
theorem endpointCall_blocked_stays_blocked
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    caller ∉ st'.scheduler.runnable := by
  unfold endpointCall at hStep
  -- WS-H12d: Eliminate bounds-check if-branches (error cases contradict hStep : ... = .ok ...)
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        simp only [hHead] at hStep
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hPop] at hStep
        | ok pair =>
          simp only [hPop] at hStep
          cases hMsg : storeTcbIpcStateAndMessage pair.2 pair.1 .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st'' =>
            simp only [hMsg] at hStep
            cases hIpc : storeTcbIpcState (ensureRunnable st'' pair.1) caller
                (.blockedOnReply endpointId (some pair.1)) with
            | error e => simp [hIpc] at hStep
            | ok st4 =>
              simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hEq⟩ := hStep; subst hEq
              exact removeRunnable_not_mem_self st4 caller
      | none =>
        simp only [hHead] at hStep
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hEnq] at hStep
        | ok st1 =>
          simp only [hEnq] at hStep
          cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact removeRunnable_not_mem_self st2 caller

/-- WS-H12a: endpointReplyRecv preserves ipcInvariant.
Chains storeTcbIpcStateAndMessage + ensureRunnable + endpointReceiveDual preservation. -/
theorem endpointReplyRecv_preserves_ipcInvariant
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcInvariant st)
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg st = .ok ((), st')) :
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
    cases hIpc : tcb.ipcState with
    | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnCall _ =>
      simp [hIpc] at hStep
    | blockedOnReply _ _ =>
      simp only [hIpc] at hStep
      -- Helper: given st1 from storeTcbIpcStateAndMessage, prove via endpointReceiveDual
      suffices ∀ st1, storeTcbIpcStateAndMessage st replyTarget .ready (some msg) = .ok st1 →
          (∀ stR, endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) = .ok stR →
            ipcInvariant stR.2) by
        split at hStep
        · split at hStep
          · revert hStep
            cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
            | error e => simp
            | ok st1 =>
              simp only []
              cases hRecv : endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) with
              | error e => simp
              | ok result =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                exact this st1 hMsg result hRecv
          · simp_all
        · dsimp only at hStep; revert hStep
          cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
          | error e => simp
          | ok st1 =>
            simp only []
            cases hRecv : endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) with
            | error e => simp
            | ok result =>
              simp only [ite_true, Except.ok.injEq, Prod.mk.injEq]
              intro ⟨_, hEq⟩; subst hEq
              exact this st1 hMsg result hRecv
      intro st1 hMsg stR hRecv
      have hInv1 := storeTcbIpcStateAndMessage_preserves_ipcInvariant st st1 replyTarget .ready (some msg) hInv hMsg
      have hInv2 : ipcInvariant (ensureRunnable st1 replyTarget) :=
        fun oid ntfn h => hInv1 oid ntfn (by rwa [ensureRunnable_preserves_objects] at h)
      exact endpointReceiveDual_preserves_ipcInvariant _ stR.2 endpointId receiver stR.1 hInv2 (by
        have : stR = (stR.1, stR.2) := Prod.ext rfl rfl; rw [this] at hRecv; exact hRecv)

/-- WS-H12a: endpointReplyRecv preserves schedulerInvariantBundle.
Chains storeTcbIpcStateAndMessage + ensureRunnable + endpointReceiveDual preservation. -/
theorem endpointReplyRecv_preserves_schedulerInvariantBundle
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : schedulerInvariantBundle st)
    (hCurrReady : currentThreadIpcReady st)
    (hCurrNotHead : currentNotEndpointQueueHead st)
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg st = .ok ((), st')) :
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
    cases hIpc : tcb.ipcState with
    | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnCall _ =>
      simp [hIpc] at hStep
    | blockedOnReply _ _ =>
      simp only [hIpc] at hStep
      suffices ∀ st1, storeTcbIpcStateAndMessage st replyTarget .ready (some msg) = .ok st1 →
          (∀ stR, endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) = .ok stR →
            schedulerInvariantBundle stR.2) by
        split at hStep
        · split at hStep
          · revert hStep
            cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
            | error e => simp
            | ok st1 =>
              simp only []
              cases hRecv : endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) with
              | error e => simp
              | ok result =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                exact this st1 hMsg result hRecv
          · simp_all
        · dsimp only at hStep; revert hStep
          cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
          | error e => simp
          | ok st1 =>
            simp only []
            cases hRecv : endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) with
            | error e => simp
            | ok result =>
              simp only [ite_true, Except.ok.injEq, Prod.mk.injEq]
              intro ⟨_, hEq⟩; subst hEq
              exact this st1 hMsg result hRecv
      intro st1 hMsg stR hRecv
      rcases hInv with ⟨hQCC, hRQU, hCTV⟩
      have hSchedEq := storeTcbIpcStateAndMessage_scheduler_eq st st1 replyTarget .ready (some msg) hMsg
      have hInvMid : schedulerInvariantBundle (ensureRunnable st1 replyTarget) := by
        refine ⟨?_, ?_, ?_⟩
        · unfold queueCurrentConsistent
          rw [ensureRunnable_scheduler_current, hSchedEq]
          cases hCurr : st.scheduler.current with
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
          cases hCurr : st.scheduler.current with
          | none => simp
          | some x =>
            simp only []
            have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by
              simp [currentThreadValid, hCurr] at hCTV; exact hCTV
            by_cases hNeTid : x.toObjId = replyTarget.toObjId
            · have hTargetTcb : ∃ t, st.objects[replyTarget.toObjId]? = some (.tcb t) := hNeTid ▸ hCTV'
              have h := storeTcbIpcStateAndMessage_tcb_exists_at_target st st1 replyTarget .ready (some msg) hMsg hTargetTcb
              rwa [← hNeTid] at h
            · rcases hCTV' with ⟨tcb', hTcbObj⟩
              exact ⟨tcb', (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 replyTarget .ready (some msg) x.toObjId hNeTid hMsg) ▸ hTcbObj⟩
      have hTargetTcbObj := lookupTcb_some_objects st replyTarget tcb hLookup
      exact endpointReceiveDual_preserves_schedulerInvariantBundle _ stR.2 endpointId receiver stR.1 hInvMid
        (by
          unfold currentNotEndpointQueueHead
          rw [ensureRunnable_scheduler_current, congrArg SchedulerState.current hSchedEq]
          cases hCurr' : st.scheduler.current with
          | none => trivial
          | some tid =>
            intro oid ep' hEp'
            rw [ensureRunnable_preserves_objects] at hEp'
            have hOidNe : oid ≠ replyTarget.toObjId := by
              intro h; subst h
              obtain ⟨tcb', hTcb'⟩ := storeTcbIpcStateAndMessage_tcb_exists_at_target st st1 replyTarget .ready (some msg) hMsg ⟨tcb, hTargetTcbObj⟩
              rw [hTcb'] at hEp'; cases hEp'
            have hEp'' : st.objects[oid]? = some (.endpoint ep') := by
              rwa [storeTcbIpcStateAndMessage_preserves_objects_ne st st1 replyTarget .ready (some msg) oid hOidNe hMsg] at hEp'
            have := hCurrNotHead; simp [currentNotEndpointQueueHead, hCurr'] at this
            exact this oid ep' hEp'')
        (by have : stR = (stR.1, stR.2) := Prod.ext rfl rfl; rw [this] at hRecv; exact hRecv)

/-- WS-H12a: endpointReplyRecv preserves ipcSchedulerContractPredicates.
Chains storeTcbIpcStateAndMessage + ensureRunnable + endpointReceiveDual preservation. -/
theorem endpointReplyRecv_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (hContract : ipcSchedulerContractPredicates st)
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hContract with ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply⟩
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
    cases hIpc : tcb.ipcState with
    | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnCall _ =>
      simp [hIpc] at hStep
    | blockedOnReply _ _ =>
      simp only [hIpc] at hStep
      suffices ∀ st1, storeTcbIpcStateAndMessage st replyTarget .ready (some msg) = .ok st1 →
          (∀ stR, endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) = .ok stR →
            ipcSchedulerContractPredicates stR.2) by
        split at hStep
        · split at hStep
          · revert hStep
            cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
            | error e => simp
            | ok st1 =>
              simp only []
              cases hRecv : endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) with
              | error e => simp
              | ok result =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                exact this st1 hMsg result hRecv
          · simp_all
        · dsimp only at hStep; revert hStep
          cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
          | error e => simp
          | ok st1 =>
            simp only []
            cases hRecv : endpointReceiveDual endpointId receiver (ensureRunnable st1 replyTarget) with
            | error e => simp
            | ok result =>
              simp only [ite_true, Except.ok.injEq, Prod.mk.injEq]
              intro ⟨_, hEq⟩; subst hEq
              exact this st1 hMsg result hRecv
      intro st1 hMsg stR hRecv
      have hSchedEq := storeTcbIpcStateAndMessage_scheduler_eq st st1 replyTarget .ready (some msg) hMsg
      have hContractMid : ipcSchedulerContractPredicates (ensureRunnable st1 replyTarget) := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro tid tcb' hTcb' hRun'
          rw [ensureRunnable_preserves_objects] at hTcb'
          by_cases hNe : tid.toObjId = replyTarget.toObjId
          · exact storeTcbIpcStateAndMessage_ipcState_eq st st1 replyTarget .ready (some msg) hMsg tcb' (hNe ▸ hTcb')
          · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 replyTarget .ready (some msg) tid.toObjId hNe hMsg).symm.trans hTcb'
            have hNeTid : tid ≠ replyTarget := fun h => hNe (congrArg ThreadId.toObjId h)
            rcases ensureRunnable_mem_reverse st1 replyTarget tid hRun' with hOld | hEq
            · exact hReady tid tcb' hTcbPre (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
            · exact absurd hEq hNeTid
        · intro tid tcb' eid hTcb' hIpcState'
          rw [ensureRunnable_preserves_objects] at hTcb'
          by_cases hNe : tid.toObjId = replyTarget.toObjId
          · have := storeTcbIpcStateAndMessage_ipcState_eq st st1 replyTarget .ready (some msg) hMsg tcb' (hNe ▸ hTcb')
            rw [this] at hIpcState'; cases hIpcState'
          · have hNeTid : tid ≠ replyTarget := fun h => hNe (congrArg ThreadId.toObjId h)
            have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 replyTarget .ready (some msg) tid.toObjId hNe hMsg).symm.trans hTcb'
            intro hRun'
            rcases ensureRunnable_mem_reverse st1 replyTarget tid hRun' with hOld | hEq
            · exact hBlockSend tid tcb' eid hTcbPre hIpcState' (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
            · exact absurd hEq hNeTid
        · intro tid tcb' eid hTcb' hIpcState'
          rw [ensureRunnable_preserves_objects] at hTcb'
          by_cases hNe : tid.toObjId = replyTarget.toObjId
          · have := storeTcbIpcStateAndMessage_ipcState_eq st st1 replyTarget .ready (some msg) hMsg tcb' (hNe ▸ hTcb')
            rw [this] at hIpcState'; cases hIpcState'
          · have hNeTid : tid ≠ replyTarget := fun h => hNe (congrArg ThreadId.toObjId h)
            have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 replyTarget .ready (some msg) tid.toObjId hNe hMsg).symm.trans hTcb'
            intro hRun'
            rcases ensureRunnable_mem_reverse st1 replyTarget tid hRun' with hOld | hEq
            · exact hBlockRecv tid tcb' eid hTcbPre hIpcState' (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
            · exact absurd hEq hNeTid
        · intro tid tcb' eid hTcb' hIpcState'
          rw [ensureRunnable_preserves_objects] at hTcb'
          by_cases hNe : tid.toObjId = replyTarget.toObjId
          · have := storeTcbIpcStateAndMessage_ipcState_eq st st1 replyTarget .ready (some msg) hMsg tcb' (hNe ▸ hTcb')
            rw [this] at hIpcState'; cases hIpcState'
          · have hNeTid : tid ≠ replyTarget := fun h => hNe (congrArg ThreadId.toObjId h)
            have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 replyTarget .ready (some msg) tid.toObjId hNe hMsg).symm.trans hTcb'
            intro hRun'
            rcases ensureRunnable_mem_reverse st1 replyTarget tid hRun' with hOld | hEq
            · exact hBlockCall tid tcb' eid hTcbPre hIpcState' (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
            · exact absurd hEq hNeTid
        · intro tid tcb' eid rt hTcb' hIpcState'
          rw [ensureRunnable_preserves_objects] at hTcb'
          by_cases hNe : tid.toObjId = replyTarget.toObjId
          · have := storeTcbIpcStateAndMessage_ipcState_eq st st1 replyTarget .ready (some msg) hMsg tcb' (hNe ▸ hTcb')
            rw [this] at hIpcState'; cases hIpcState'
          · have hNeTid : tid ≠ replyTarget := fun h => hNe (congrArg ThreadId.toObjId h)
            have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 replyTarget .ready (some msg) tid.toObjId hNe hMsg).symm.trans hTcb'
            intro hRun'
            rcases ensureRunnable_mem_reverse st1 replyTarget tid hRun' with hOld | hEq
            · exact hBlockReply tid tcb' eid rt hTcbPre hIpcState' (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
            · exact absurd hEq hNeTid
      exact endpointReceiveDual_preserves_ipcSchedulerContractPredicates _ stR.2 endpointId receiver stR.1 hContractMid (by
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
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hContract with ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply⟩
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
    cases hIpc : tcb.ipcState with
    | ready => simp [hIpc] at hStep
    | blockedOnSend _ => simp [hIpc] at hStep
    | blockedOnReceive _ => simp [hIpc] at hStep
    | blockedOnNotification _ => simp [hIpc] at hStep
    | blockedOnCall _ => simp [hIpc] at hStep
    | blockedOnReply epId _ =>
      simp only [hIpc] at hStep
      -- WS-H1/M-02: Branch on replyTarget (authorized replier check)
      -- Both branches share identical 5-conjunct proof after authorization resolves.
      -- Helper: given st1 from storeTcbIpcStateAndMessage, prove the 5 conjuncts.
      suffices ∀ st1, storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st1 →
          ipcSchedulerContractPredicates (ensureRunnable st1 target) by
        split at hStep
        · -- some expected: if replier == expected
          split at hStep
          · -- authorized = true
            revert hStep
            cases hMsg : storeTcbIpcStateAndMessage st target .ready (some msg) with
            | error e => simp
            | ok st1 =>
              simp only [Except.ok.injEq, Prod.mk.injEq]
              intro ⟨_, hEq⟩; subst hEq
              exact this st1 hMsg
          · -- authorized = false
            simp_all
        · -- none: no replyTarget constraint
          dsimp only at hStep
          revert hStep
          cases hMsg : storeTcbIpcStateAndMessage st target .ready (some msg) with
          | error e => simp
          | ok st1 =>
            simp only [ite_true, Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            exact this st1 hMsg
      -- Shared proof body
      intro st1 hMsg
      have hSchedEq := storeTcbIpcStateAndMessage_scheduler_eq st st1 target .ready (some msg) hMsg
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- runnableThreadIpcReady
        intro tid tcb' hTcb' hRun'
        rw [ensureRunnable_preserves_objects] at hTcb'
        by_cases hNe : tid.toObjId = target.toObjId
        · exact storeTcbIpcStateAndMessage_ipcState_eq st st1 target .ready (some msg) hMsg tcb' (hNe ▸ hTcb')
        · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 target .ready (some msg) tid.toObjId hNe hMsg).symm.trans hTcb'
          have hNeTid : tid ≠ target := fun h => hNe (congrArg ThreadId.toObjId h)
          rcases ensureRunnable_mem_reverse st1 target tid hRun' with hOld | hEq
          · exact hReady tid tcb' hTcbPre (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
          · exact absurd hEq hNeTid
      · -- blockedOnSendNotRunnable
        intro tid tcb' eid hTcb' hIpcState'
        rw [ensureRunnable_preserves_objects] at hTcb'
        by_cases hNe : tid.toObjId = target.toObjId
        · have := storeTcbIpcStateAndMessage_ipcState_eq st st1 target .ready (some msg) hMsg tcb' (hNe ▸ hTcb')
          rw [this] at hIpcState'; cases hIpcState'
        · have hNeTid : tid ≠ target := fun h => hNe (congrArg ThreadId.toObjId h)
          have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 target .ready (some msg) tid.toObjId hNe hMsg).symm.trans hTcb'
          intro hRun'
          rcases ensureRunnable_mem_reverse st1 target tid hRun' with hOld | hEq
          · exact hBlockSend tid tcb' eid hTcbPre hIpcState' (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
          · exact absurd hEq hNeTid
      · -- blockedOnReceiveNotRunnable
        intro tid tcb' eid hTcb' hIpcState'
        rw [ensureRunnable_preserves_objects] at hTcb'
        by_cases hNe : tid.toObjId = target.toObjId
        · have := storeTcbIpcStateAndMessage_ipcState_eq st st1 target .ready (some msg) hMsg tcb' (hNe ▸ hTcb')
          rw [this] at hIpcState'; cases hIpcState'
        · have hNeTid : tid ≠ target := fun h => hNe (congrArg ThreadId.toObjId h)
          have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 target .ready (some msg) tid.toObjId hNe hMsg).symm.trans hTcb'
          intro hRun'
          rcases ensureRunnable_mem_reverse st1 target tid hRun' with hOld | hEq
          · exact hBlockRecv tid tcb' eid hTcbPre hIpcState' (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
          · exact absurd hEq hNeTid
      · -- blockedOnCallNotRunnable
        intro tid tcb' eid hTcb' hIpcState'
        rw [ensureRunnable_preserves_objects] at hTcb'
        by_cases hNe : tid.toObjId = target.toObjId
        · have := storeTcbIpcStateAndMessage_ipcState_eq st st1 target .ready (some msg) hMsg tcb' (hNe ▸ hTcb')
          rw [this] at hIpcState'; cases hIpcState'
        · have hNeTid : tid ≠ target := fun h => hNe (congrArg ThreadId.toObjId h)
          have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 target .ready (some msg) tid.toObjId hNe hMsg).symm.trans hTcb'
          intro hRun'
          rcases ensureRunnable_mem_reverse st1 target tid hRun' with hOld | hEq
          · exact hBlockCall tid tcb' eid hTcbPre hIpcState' (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
          · exact absurd hEq hNeTid
      · -- blockedOnReplyNotRunnable
        intro tid tcb' eid rt' hTcb' hIpcState'
        rw [ensureRunnable_preserves_objects] at hTcb'
        by_cases hNe : tid.toObjId = target.toObjId
        · have := storeTcbIpcStateAndMessage_ipcState_eq st st1 target .ready (some msg) hMsg tcb' (hNe ▸ hTcb')
          rw [this] at hIpcState'; cases hIpcState'
        · have hNeTid : tid ≠ target := fun h => hNe (congrArg ThreadId.toObjId h)
          have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 target .ready (some msg) tid.toObjId hNe hMsg).symm.trans hTcb'
          intro hRun'
          rcases ensureRunnable_mem_reverse st1 target tid hRun' with hOld | hEq
          · exact hBlockReply tid tcb' eid rt' hTcbPre hIpcState' (show tid ∈ st.scheduler.runnable by rwa [← hSchedEq])
          · exact absurd hEq hNeTid

