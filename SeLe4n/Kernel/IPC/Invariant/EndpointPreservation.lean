/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.Defs

/-! # AN3-F (IPC LOW #3) — endpoint field-preservation scope note.

The `storeTcbIpcState_*` / `storeTcbIpcStateAndMessage_*` /
`storeTcbQueueLinks_*` preservation family at lines ~200-236 proves
preservation of `ipcInvariant` specifically (an invariant about
notifications, not TCB fields).  A companion "field-preservation"
lemma set — `storeObject_nonTcb_preserves_tcb_ipcState`,
`storeObject_nonTcb_preserves_tcb_queueNext`, etc. — has been derived
via `storeObject_objects_ne` at each call site in `Structural/*.lean`
rather than lifted to a named helper per field.  Rationale: the
derivation is a one-liner at every call site (`rw [storeObject_objects_ne]`)
and lifting it to N × M individual helpers (N = field count, M = kind)
would multiply the public API surface without reducing call-site
complexity.  The preserved-by-frame facts are uniformly recoverable,
so the on-site rewrite is preferred over a named lemma.  See IPC-L3
disposition in the AN3-F work log.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- WS-E4/M-12: Preservation theorems for endpointReply
-- ============================================================================

/-- WS-F1/WS-E4/M-12/WS-H1: endpointReply preserves schedulerInvariantBundle.
Reply stores a TCB (with message) and calls ensureRunnable, similar to
endpointReceive unblocking. Updated for WS-H1 reply-target scoping. -/
theorem endpointReply_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (hInv : schedulerInvariantBundle st)
    (hCurrReady : currentThreadIpcReady st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
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
          cases replyTarget with
          | none => simp at hStep
          | some expected =>
            simp only at hStep
            split at hStep
            · -- authorized = true; proceed with reply
              revert hStep
              cases hTcb : storeTcbIpcStateAndMessage st target .ready (some msg) with
              | error e => simp
              | ok st1 =>
                  simp only [Except.ok.injEq, Prod.mk.injEq]
                  intro ⟨_, hStEq⟩; subst hStEq
                  rcases hInv with ⟨hQueue, hRunUnique, hCurrent⟩
                  have hSchedEq := storeTcbIpcStateAndMessage_scheduler_eq st st1 target .ready (some msg) hTcb
                  refine ⟨?_, ?_, ?_⟩
                  · unfold queueCurrentConsistent
                    rw [ensureRunnable_scheduler_current, hSchedEq]
                    cases hCurr : st.scheduler.current with
                    | none => trivial
                    | some x =>
                      have hNotMem : x ∉ st.scheduler.runnable := by
                        have := hQueue; simp [queueCurrentConsistent, hCurr] at this; exact this
                      have hNe : x ≠ target := by
                        intro hEq
                        have hObj := lookupTcb_some_objects st target tcb hLookup
                        rw [hEq] at hCurr
                        have hReady : tcb.ipcState = .ready := by
                          simp [currentThreadIpcReady, hCurr] at hCurrReady; exact hCurrReady tcb hObj
                        simp [hIpc] at hReady
                      exact ensureRunnable_not_mem_of_not_mem st1 target x (hSchedEq ▸ hNotMem) hNe
                  · exact ensureRunnable_nodup st1 target (hSchedEq ▸ hRunUnique)
                  · show currentThreadValid (ensureRunnable st1 target)
                    unfold currentThreadValid
                    simp only [ensureRunnable_scheduler_current, ensureRunnable_preserves_objects, hSchedEq]
                    cases hCurr : st.scheduler.current with
                    | none => simp
                    | some x =>
                      simp only []
                      have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by
                        simp [currentThreadValid, hCurr] at hCurrent; exact hCurrent
                      by_cases hNeTid : x.toObjId = target.toObjId
                      · have hTargetTcb : ∃ tcb', st.objects[target.toObjId]? = some (.tcb tcb') :=
                          hNeTid ▸ hCTV'
                        have h := storeTcbIpcStateAndMessage_tcb_exists_at_target st st1 target .ready (some msg) hObjInv hTcb hTargetTcb
                        rwa [← hNeTid] at h
                      · rcases hCTV' with ⟨tcb', hTcbObj⟩
                        exact ⟨tcb', (storeTcbIpcStateAndMessage_preserves_objects_ne st st1 target .ready (some msg) x.toObjId hNeTid hObjInv hTcb) ▸ hTcbObj⟩
            · -- authorized = false
              simp_all

/-- WS-F1/WS-E4/M-12/WS-H1: endpointReply preserves ipcInvariant.
Reply modifies only a TCB (no endpoint/notification changes).
Updated for WS-H1 reply-target scoping. -/
theorem endpointReply_preserves_ipcInvariant
    (st st' : SystemState)
    (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (hInv : ipcInvariant st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    ipcInvariant st' := by
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
          cases replyTarget with
          | none => simp at hStep
          | some expected =>
            simp only at hStep
            split at hStep
            · -- authorized = true; proceed with reply
              revert hStep
              cases hTcb : storeTcbIpcStateAndMessage st target .ready (some msg) with
              | error e => simp
              | ok st1 =>
                  simp only [Except.ok.injEq, Prod.mk.injEq]
                  intro ⟨_, hStEq⟩; subst hStEq
                  intro oid ntfn hObj
                  have hObjSt1 : st1.objects[oid]? = some (.notification ntfn) := by
                    rwa [ensureRunnable_preserves_objects st1 target] at hObj
                  exact hInv oid ntfn (storeTcbIpcStateAndMessage_notification_backward st st1 target .ready (some msg) oid ntfn hObjInv hTcb hObjSt1)
            · -- authorized = false
              simp_all

-- ============================================================================
-- WS-F1: Helper — scheduler_unchanged_through_store_tcb_msg
-- Mirrors scheduler_unchanged_through_store_tcb but for storeTcbIpcStateAndMessage.
-- ============================================================================

/-- WS-F1: After storeObject + storeTcbIpcStateAndMessage, the scheduler is unchanged. -/
private theorem scheduler_unchanged_through_store_tcb_msg
    (st st1 st2 : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hStore : storeObject oid obj st = .ok ((), st1))
    (hTcb : storeTcbIpcStateAndMessage st1 tid ipc msg = .ok st2) :
    st2.scheduler = st.scheduler := by
  rw [storeTcbIpcStateAndMessage_scheduler_eq st1 st2 tid ipc msg hTcb,
      storeObject_scheduler_eq st st1 oid obj hStore]

-- ============================================================================
-- WS-F1: Dual-queue endpoint invariant preservation (F-10 remediation)
--
-- TPI-D08: Dual-queue preservation proof infrastructure
--
-- Architecture: endpointSendDual/endpointReceiveDual compose
-- endpointQueuePopHead/endpointQueueEnqueue (private, multi-step storeObject
-- chains) with storeTcbIpcStateAndMessage + removeRunnable/ensureRunnable.
--
-- Structural argument (verified by construction):
-- 1. endpointQueuePopHead/Enqueue modify ONLY sendQ/receiveQ intrusive fields
--    on the target endpoint (using `{ ep with sendQ := q' }` / `{ ep with receiveQ := q' }`).
--    Notification objects are UNCHANGED. Therefore ipcInvariant
--    (notification well-formedness) is preserved.
-- 2. All intermediate storeObject calls target either the endpoint ID or
--    thread TCBs. Objects at other IDs are backward-preserved through
--    storeObject_objects_ne / storeTcbQueueLinks_*_backward chains.
-- 3. No intermediate step modifies the scheduler (storeObject_scheduler_eq,
--    storeTcbQueueLinks_scheduler_eq, storeTcbIpcStateAndMessage_scheduler_eq).
-- 4. IPC state transitions (.ready → .blockedOnSend or .blockedOnReceive)
--    plus removeRunnable/ensureRunnable maintain the scheduler contract
--    predicates via the same blocking_path/handshake_path decomposition
--    used in the legacy proofs.
--
-- These theorems are structurally sound by the argument above. Full
-- mechanical unfolding through the private multi-step chains requires
-- exposing endpointQueuePopHead/endpointQueueEnqueue internals through
-- 3-4 layers of storeObject case splits. Completed in WS-F1.
-- ============================================================================

-- ============================================================================
-- WS-F1: Compositional ipcInvariant preservation helpers
-- ============================================================================

/-- storeTcbQueueLinks preserves ipcInvariant (pure backward transport). -/
private theorem storeTcbQueueLinks_preserves_ipcInvariant
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
    (hInv : ipcInvariant st) (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    ipcInvariant st' := by
  exact fun oid ntfn h => hInv oid ntfn (storeTcbQueueLinks_notification_backward st st' tid prev pprev next oid ntfn hObjInv hStep h)

/-- Storing an endpoint preserves ipcInvariant (which only checks notifications).
    Endpoints are a different object kind, so storing an endpoint cannot affect notifications. -/
theorem storeObject_endpoint_preserves_ipcInvariant
    (st st1 : SystemState) (endpointId : SeLe4n.ObjId) (ep' : Endpoint)
    (hInv : ipcInvariant st) (hObjInv : st.objects.invExt)
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st1)) :
    ipcInvariant st1 := by
  intro oid ntfn hObj
  by_cases hNe : oid = endpointId
  · rw [hNe] at hObj
    rw [storeObject_objects_eq st st1 endpointId (.endpoint ep') hObjInv hStore] at hObj; cases hObj
  · exact hInv oid ntfn (by rwa [storeObject_objects_ne st st1 endpointId oid _ hNe hObjInv hStore] at hObj)

/-- storeTcbIpcStateAndMessage preserves ipcInvariant (pure backward transport). -/
theorem storeTcbIpcStateAndMessage_preserves_ipcInvariant
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hInv : ipcInvariant st) (hObjInv : st.objects.invExt) (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    ipcInvariant st' := by
  exact fun oid ntfn h => hInv oid ntfn (storeTcbIpcStateAndMessage_notification_backward st st' tid ipc msg oid ntfn hObjInv hStep h)

/-- storeTcbIpcState preserves ipcInvariant (pure backward transport). -/
theorem storeTcbIpcState_preserves_ipcInvariant
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hInv : ipcInvariant st) (hObjInv : st.objects.invExt) (hStep : storeTcbIpcState st tid ipc = .ok st') :
    ipcInvariant st' := by
  exact fun oid ntfn h => hInv oid ntfn (storeTcbIpcState_notification_backward st st' tid ipc oid ntfn hObjInv hStep h)

/-- storeTcbPendingMessage preserves ipcInvariant (pure backward transport). -/
private theorem storeTcbPendingMessage_preserves_ipcInvariant
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (hInv : ipcInvariant st) (hObjInv : st.objects.invExt) (hStep : storeTcbPendingMessage st tid msg = .ok st') :
    ipcInvariant st' := by
  exact fun oid ntfn h => hInv oid ntfn (storeTcbPendingMessage_notification_backward st st' tid msg oid ntfn hObjInv hStep h)

/-- endpointQueuePopHead preserves ipcInvariant. PopHead modifies only sendQ/receiveQ
    on the target endpoint and stores TCBs via storeTcbQueueLinks. ipcInvariant checks
    notification well-formedness, which is unchanged by sendQ/receiveQ updates. -/
theorem endpointQueuePopHead_preserves_ipcInvariant
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : ipcInvariant st) (hObjInv : st.objects.invExt)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, _headTcb, st')) :
    ipcInvariant st' := by
  exact fun oid ntfn hObjPost => hInv oid ntfn (endpointQueuePopHead_notification_backward endpointId isReceiveQ st st' tid oid ntfn hObjInv hStep hObjPost)

/-- endpointQueueEnqueue preserves ipcInvariant. Same structural argument as PopHead:
    only sendQ/receiveQ fields and TCB queue links are modified. -/
theorem endpointQueueEnqueue_preserves_ipcInvariant
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (enqueueTid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hInv : ipcInvariant st) (hObjInv : st.objects.invExt)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ enqueueTid st = .ok st') :
    ipcInvariant st' := by
  exact fun oid ntfn hObjPost => hInv oid ntfn (endpointQueueEnqueue_notification_backward endpointId isReceiveQ enqueueTid st st' oid ntfn hObjInv hStep hObjPost)

-- ============================================================================
-- WS-F1: Contract predicate transport infrastructure
-- ============================================================================

/-- WS-F1: If scheduler and TCB ipcStates are backward-preserved, contract
predicates are preserved. This is the key compositional tool for proving
contract predicate preservation through multi-step operations (PopHead, Enqueue,
storeTcbQueueLinks chains) that only modify queue link fields. -/
theorem contracts_of_same_scheduler_ipcState
    (st st' : SystemState)
    (hSched : st'.scheduler = st.scheduler)
    (hIpc : ∀ (tid : SeLe4n.ThreadId) (tcb' : TCB),
        st'.objects[tid.toObjId]? = some (.tcb tcb') →
        ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState)
    (hContract : ipcSchedulerContractPredicates st) :
    ipcSchedulerContractPredicates st' := by
  rcases hContract with ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply, hBlockNotif⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- runnableThreadIpcReady
    intro tid tcb' hTcb' hRun'
    obtain ⟨tcb, hTcb, hIpcEq⟩ := hIpc tid tcb' hTcb'
    rw [← hIpcEq]; exact hReady tid tcb hTcb (show tid ∈ st.scheduler.runnable by rwa [← hSched])
  · -- blockedOnSendNotRunnable
    intro tid tcb' eid hTcb' hIpcState'
    obtain ⟨tcb, hTcb, hIpcEq⟩ := hIpc tid tcb' hTcb'
    have hNotRun := hBlockSend tid tcb eid hTcb (show tcb.ipcState = .blockedOnSend eid by rw [hIpcEq]; exact hIpcState')
    intro hRun'; exact hNotRun (show tid ∈ st.scheduler.runnable by rwa [← hSched])
  · -- blockedOnReceiveNotRunnable
    intro tid tcb' eid hTcb' hIpcState'
    obtain ⟨tcb, hTcb, hIpcEq⟩ := hIpc tid tcb' hTcb'
    have hNotRun := hBlockRecv tid tcb eid hTcb (show tcb.ipcState = .blockedOnReceive eid by rw [hIpcEq]; exact hIpcState')
    intro hRun'; exact hNotRun (show tid ∈ st.scheduler.runnable by rwa [← hSched])
  · -- blockedOnCallNotRunnable (WS-H1)
    intro tid tcb' eid hTcb' hIpcState'
    obtain ⟨tcb, hTcb, hIpcEq⟩ := hIpc tid tcb' hTcb'
    have hNotRun := hBlockCall tid tcb eid hTcb (show tcb.ipcState = .blockedOnCall eid by rw [hIpcEq]; exact hIpcState')
    intro hRun'; exact hNotRun (show tid ∈ st.scheduler.runnable by rwa [← hSched])
  · -- blockedOnReplyNotRunnable (WS-H1)
    intro tid tcb' eid rt hTcb' hIpcState'
    obtain ⟨tcb, hTcb, hIpcEq⟩ := hIpc tid tcb' hTcb'
    have hNotRun := hBlockReply tid tcb eid rt hTcb (show tcb.ipcState = .blockedOnReply eid rt by rw [hIpcEq]; exact hIpcState')
    intro hRun'; exact hNotRun (show tid ∈ st.scheduler.runnable by rwa [← hSched])
  · -- blockedOnNotificationNotRunnable (WS-F6/D2)
    intro tid tcb' nid hTcb' hIpcState'
    obtain ⟨tcb, hTcb, hIpcEq⟩ := hIpc tid tcb' hTcb'
    have hNotRun := hBlockNotif tid tcb nid hTcb (show tcb.ipcState = .blockedOnNotification nid by rw [hIpcEq]; exact hIpcState')
    intro hRun'; exact hNotRun (show tid ∈ st.scheduler.runnable by rwa [← hSched])

/-- WS-F1/TPI-D08: endpointSendDual preserves ipcInvariant.
Dual-queue operations modify only sendQ/receiveQ intrusive queue pointers
and TCB queue links; notification objects are unchanged. See TPI-D08
structural argument above. -/
theorem endpointSendDual_preserves_ipcInvariant
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcInvariant st) (hObjInv : st.objects.invExt)
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    ipcInvariant st' := by
  unfold endpointSendDual at hStep
  -- WS-H12d: Eliminate bounds-check if-branches (error cases contradict hStep : ... = .ok ...)
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        -- Handshake path: PopHead → storeTcbIpcStateAndMessage → ensureRunnable
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInv1 : pair.2.2.objects.invExt :=
            endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          have hInv1 := endpointQueuePopHead_preserves_ipcInvariant endpointId true st pair.2.2 pair.1 hInv hObjInv hPop
          cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hInv2 := storeTcbIpcStateAndMessage_preserves_ipcInvariant pair.2.2 st2 pair.1 .ready (some msg) hInv1 hObjInv1 hMsg
            exact fun oid ntfn h => hInv2 oid ntfn (by rwa [ensureRunnable_preserves_objects] at h)
      | none =>
        -- Blocking path: Enqueue → storeTcbIpcStateAndMessage → removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId false sender st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hObjInv1 : st1.objects.invExt :=
            endpointQueueEnqueue_preserves_objects_invExt endpointId false sender st st1 hObjInv hEnq
          have hInv1 := endpointQueueEnqueue_preserves_ipcInvariant endpointId false sender st st1 hInv hObjInv hEnq
          cases hMsg : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hInv2 := storeTcbIpcStateAndMessage_preserves_ipcInvariant st1 st2 sender (.blockedOnSend endpointId) (some msg) hInv1 hObjInv1 hMsg
            exact fun oid ntfn h => hInv2 oid ntfn (by rwa [removeRunnable_preserves_objects] at h)

/-- WS-H12d/A-09: If `endpointSendDual` succeeds, the message satisfies payload bounds.
The bounds check at the top of `endpointSendDual` ensures that only bounded
messages pass through to the state-modifying paths. -/
theorem endpointSendDual_message_bounded
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    msg.bounded := by
  unfold endpointSendDual at hStep
  -- If bounds checks fail, hStep contradicts .ok
  by_cases hR : maxMessageRegisters < msg.registers.size
  · simp [hR] at hStep
  · by_cases hC : maxExtraCaps < msg.caps.size
    · simp [hR, hC] at hStep
    · exact ⟨Nat.not_lt.mp hR, Nat.not_lt.mp hC⟩

/-- WS-H12d/A-09: If `endpointCall` succeeds, the message satisfies payload bounds. -/
theorem endpointCall_message_bounded
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    msg.bounded := by
  unfold endpointCall at hStep
  by_cases hR : maxMessageRegisters < msg.registers.size
  · simp [hR] at hStep
  · by_cases hC : maxExtraCaps < msg.caps.size
    · simp [hR, hC] at hStep
    · exact ⟨Nat.not_lt.mp hR, Nat.not_lt.mp hC⟩

/-- WS-H12d/A-09: If `endpointReply` succeeds, the reply message satisfies payload bounds. -/
theorem endpointReply_message_bounded
    (st st' : SystemState) (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    msg.bounded := by
  unfold endpointReply at hStep
  by_cases hR : maxMessageRegisters < msg.registers.size
  · simp [hR] at hStep
  · by_cases hC : maxExtraCaps < msg.caps.size
    · simp [hR, hC] at hStep
    · exact ⟨Nat.not_lt.mp hR, Nat.not_lt.mp hC⟩

/-- WS-H12d/A-09: If `endpointReplyRecv` succeeds, the reply message satisfies payload bounds. -/
theorem endpointReplyRecv_message_bounded
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId) (receiver replyTarget : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg st = .ok ((), st')) :
    msg.bounded := by
  unfold endpointReplyRecv at hStep
  by_cases hR : maxMessageRegisters < msg.registers.size
  · simp [hR] at hStep
  · by_cases hC : maxExtraCaps < msg.caps.size
    · simp [hR, hC] at hStep
    · exact ⟨Nat.not_lt.mp hR, Nat.not_lt.mp hC⟩

/-- WS-F1/TPI-D08: endpointSendDual preserves schedulerInvariantBundle. -/
theorem endpointSendDual_preserves_schedulerInvariantBundle
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : schedulerInvariantBundle st)
    (hCurrNotHead : currentNotEndpointQueueHead st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  rcases hInv with ⟨hQCC, hRQU, hCTV⟩
  unfold endpointSendDual at hStep
  -- WS-H12d: Eliminate bounds-check if-branches (error cases contradict hStep : ... = .ok ...)
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        -- Handshake: PopHead → storeTcbIpcStateAndMessage(.ready) → ensureRunnable
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInv1 : pair.2.2.objects.invExt :=
            endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          have hSchedPop := endpointQueuePopHead_scheduler_eq endpointId true st pair.2.2 pair.1 hPop
          cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq pair.2.2 st2 pair.1 .ready (some msg) hMsg
            have hSchedEq : st2.scheduler = st.scheduler := hSchedMsg.trans hSchedPop
            refine ⟨?_, ?_, ?_⟩
            · unfold queueCurrentConsistent
              rw [ensureRunnable_scheduler_current, hSchedEq]
              cases hCurr : st.scheduler.current with
              | none => trivial
              | some x =>
                have hNotMem : x ∉ st.scheduler.runnable := by
                  have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this
                have hNe : x ≠ pair.1 := by
                  have hHeadEq := endpointQueuePopHead_returns_head endpointId true st ep pair.1 pair.2.2 hObj hPop
                  simp at hHeadEq
                  intro hEq; rw [hEq] at hCurr
                  have := hCurrNotHead; simp [currentNotEndpointQueueHead, hCurr] at this
                  exact (this endpointId ep hObj).1 hHeadEq
                exact ensureRunnable_not_mem_of_not_mem st2 pair.1 x (hSchedEq ▸ hNotMem) hNe
            · exact ensureRunnable_nodup st2 pair.1 (hSchedEq ▸ hRQU)
            · show currentThreadValid (ensureRunnable st2 pair.1)
              unfold currentThreadValid
              simp only [ensureRunnable_scheduler_current, ensureRunnable_preserves_objects, hSchedEq]
              cases hCurr : st.scheduler.current with
              | none => simp
              | some x =>
                simp only []
                have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by
                  simp [currentThreadValid, hCurr] at hCTV; exact hCTV
                rcases hCTV' with ⟨tcbX, hTcbX⟩
                obtain ⟨tcb1, hTcb1⟩ := endpointQueuePopHead_tcb_forward endpointId true st pair.2.2 pair.1 x.toObjId tcbX hObjInv hPop hTcbX
                by_cases hNeTid : x.toObjId = pair.1.toObjId
                · have hTargetTcb : ∃ t, pair.2.2.objects[pair.1.toObjId]? = some (.tcb t) := hNeTid ▸ ⟨tcb1, hTcb1⟩
                  have h := storeTcbIpcStateAndMessage_tcb_exists_at_target pair.2.2 st2 pair.1 .ready (some msg) hObjInv1 hMsg hTargetTcb
                  rwa [← hNeTid] at h
                · exact ⟨tcb1, (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 .ready (some msg) x.toObjId hNeTid hObjInv1 hMsg) ▸ hTcb1⟩
      | none =>
        -- Blocking: Enqueue → storeTcbIpcStateAndMessage(.blockedOnSend) → removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId false sender st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hObjInv1 : st1.objects.invExt :=
            endpointQueueEnqueue_preserves_objects_invExt endpointId false sender st st1 hObjInv hEnq
          have hSchedEnq := endpointQueueEnqueue_scheduler_eq endpointId false sender st st1 hEnq
          cases hMsg : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq st1 st2 sender (.blockedOnSend endpointId) (some msg) hMsg
            have hSchedEq : st2.scheduler = st.scheduler := hSchedMsg.trans hSchedEnq
            refine ⟨?_, ?_, ?_⟩
            · unfold queueCurrentConsistent
              rw [removeRunnable_scheduler_current, congrArg SchedulerState.current hSchedEq]
              cases hCurr : st.scheduler.current with
              | none => simp
              | some x =>
                by_cases hEq' : x = sender
                · subst hEq'; simp
                · rw [if_neg (show ¬(some x = some sender) from fun h => hEq' (Option.some.inj h))]
                  show x ∉ (removeRunnable st2 sender).scheduler.runnable
                  have hNotMem : x ∉ st.scheduler.runnable := by
                    have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this
                  exact removeRunnable_not_mem_of_not_mem st2 sender x (hSchedEq ▸ hNotMem)
            · exact removeRunnable_nodup st2 sender (hSchedEq ▸ hRQU)
            · unfold currentThreadValid
              rw [removeRunnable_preserves_objects, removeRunnable_scheduler_current,
                  congrArg SchedulerState.current hSchedEq]
              cases hCurr : st.scheduler.current with
              | none => simp
              | some x =>
                by_cases hEq' : x = sender
                · subst hEq'; simp
                · rw [if_neg (show ¬(some x = some sender) from fun h => hEq' (Option.some.inj h))]
                  show ∃ tcb, st2.objects[x.toObjId]? = some (.tcb tcb)
                  have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by
                    simp [currentThreadValid, hCurr] at hCTV; exact hCTV
                  rcases hCTV' with ⟨tcbX, hTcbX⟩
                  obtain ⟨tcb1, hTcb1⟩ := endpointQueueEnqueue_tcb_forward endpointId false sender st st1 x.toObjId tcbX hObjInv hEnq hTcbX
                  have hNeTid : x.toObjId ≠ sender.toObjId := fun h => hEq' (threadId_toObjId_injective h)
                  exact ⟨tcb1, (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 sender (.blockedOnSend endpointId) (some msg) x.toObjId hNeTid hObjInv1 hMsg) ▸ hTcb1⟩

/-- WS-F1/TPI-D08: endpointSendDual preserves ipcSchedulerContractPredicates. -/
theorem endpointSendDual_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hContract : ipcSchedulerContractPredicates st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hContract with ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply, hBlockNotif⟩
  unfold endpointSendDual at hStep
  -- WS-H12d: Eliminate bounds-check if-branches (error cases contradict hStep : ... = .ok ...)
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        -- Handshake: PopHead → storeTcbIpcStateAndMessage(.ready) → ensureRunnable
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInv1 : pair.2.2.objects.invExt :=
            endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          -- PopHead preserves scheduler and TCB ipcStates → contracts preserved through PopHead
          have hObjInv1 : pair.2.2.objects.invExt :=
            endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          have hSchedPop := endpointQueuePopHead_scheduler_eq endpointId true st pair.2.2 pair.1 hPop
          have hContractPop := contracts_of_same_scheduler_ipcState st pair.2.2 hSchedPop
            (fun tid tcb' h => endpointQueuePopHead_tcb_ipcState_backward endpointId true st pair.2.2 pair.1 tid tcb' hObjInv hPop h)
            ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply, hBlockNotif⟩
          -- Now storeTcbIpcStateAndMessage(.ready, receiver) + ensureRunnable
          cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            rcases hContractPop with ⟨hReady', hBlockSend', hBlockRecv', hBlockCall', hBlockReply', hBlockNotif'⟩
            have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq pair.2.2 st2 pair.1 .ready (some msg) hMsg
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
            · -- runnableThreadIpcReady
              intro tid tcb' hTcb' hRun'
              rw [ensureRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid.toObjId = pair.1.toObjId
              · exact storeTcbIpcStateAndMessage_ipcState_eq pair.2.2 st2 pair.1 .ready (some msg) hObjInv1 hMsg tcb' (hNe ▸ hTcb')
              · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 .ready (some msg) tid.toObjId hNe hObjInv1 hMsg).symm.trans hTcb'
                have hNeTid : tid ≠ pair.1 := fun h => hNe (congrArg ThreadId.toObjId h)
                rcases ensureRunnable_mem_reverse st2 pair.1 tid hRun' with hOld | hEq
                · exact hReady' tid tcb' hTcbPre (show tid ∈ pair.2.2.scheduler.runnable by rwa [← hSchedMsg])
                · exact absurd hEq hNeTid
            · -- blockedOnSendNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              rw [ensureRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid.toObjId = pair.1.toObjId
              · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2.2 st2 pair.1 .ready (some msg) hObjInv1 hMsg tcb' (hNe ▸ hTcb')
                rw [this] at hIpcState'; cases hIpcState'
              · have hNeTid : tid ≠ pair.1 := fun h => hNe (congrArg ThreadId.toObjId h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 .ready (some msg) tid.toObjId hNe hObjInv1 hMsg).symm.trans hTcb'
                intro hRun'
                rcases ensureRunnable_mem_reverse st2 pair.1 tid hRun' with hOld | hEq
                · exact hBlockSend' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.2.scheduler.runnable by rwa [← hSchedMsg])
                · exact absurd hEq hNeTid
            · -- blockedOnReceiveNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              rw [ensureRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid.toObjId = pair.1.toObjId
              · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2.2 st2 pair.1 .ready (some msg) hObjInv1 hMsg tcb' (hNe ▸ hTcb')
                rw [this] at hIpcState'; cases hIpcState'
              · have hNeTid : tid ≠ pair.1 := fun h => hNe (congrArg ThreadId.toObjId h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 .ready (some msg) tid.toObjId hNe hObjInv1 hMsg).symm.trans hTcb'
                intro hRun'
                rcases ensureRunnable_mem_reverse st2 pair.1 tid hRun' with hOld | hEq
                · exact hBlockRecv' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.2.scheduler.runnable by rwa [← hSchedMsg])
                · exact absurd hEq hNeTid
            · -- blockedOnCallNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              rw [ensureRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid.toObjId = pair.1.toObjId
              · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2.2 st2 pair.1 .ready (some msg) hObjInv1 hMsg tcb' (hNe ▸ hTcb')
                rw [this] at hIpcState'; cases hIpcState'
              · have hNeTid : tid ≠ pair.1 := fun h => hNe (congrArg ThreadId.toObjId h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 .ready (some msg) tid.toObjId hNe hObjInv1 hMsg).symm.trans hTcb'
                intro hRun'
                rcases ensureRunnable_mem_reverse st2 pair.1 tid hRun' with hOld | hEq
                · exact hBlockCall' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.2.scheduler.runnable by rwa [← hSchedMsg])
                · exact absurd hEq hNeTid
            · -- blockedOnReplyNotRunnable
              intro tid tcb' eid rt hTcb' hIpcState'
              rw [ensureRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid.toObjId = pair.1.toObjId
              · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2.2 st2 pair.1 .ready (some msg) hObjInv1 hMsg tcb' (hNe ▸ hTcb')
                rw [this] at hIpcState'; cases hIpcState'
              · have hNeTid : tid ≠ pair.1 := fun h => hNe (congrArg ThreadId.toObjId h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 .ready (some msg) tid.toObjId hNe hObjInv1 hMsg).symm.trans hTcb'
                intro hRun'
                rcases ensureRunnable_mem_reverse st2 pair.1 tid hRun' with hOld | hEq
                · exact hBlockReply' tid tcb' eid rt hTcbPre hIpcState' (show tid ∈ pair.2.2.scheduler.runnable by rwa [← hSchedMsg])
                · exact absurd hEq hNeTid
            · -- blockedOnNotificationNotRunnable (WS-F6/D2)
              intro tid tcb' nid hTcb' hIpcState'
              rw [ensureRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid.toObjId = pair.1.toObjId
              · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2.2 st2 pair.1 .ready (some msg) hObjInv1 hMsg tcb' (hNe ▸ hTcb')
                rw [this] at hIpcState'; cases hIpcState'
              · have hNeTid : tid ≠ pair.1 := fun h => hNe (congrArg ThreadId.toObjId h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 .ready (some msg) tid.toObjId hNe hObjInv1 hMsg).symm.trans hTcb'
                intro hRun'
                rcases ensureRunnable_mem_reverse st2 pair.1 tid hRun' with hOld | hEq
                · exact hBlockNotif' tid tcb' nid hTcbPre hIpcState' (show tid ∈ pair.2.2.scheduler.runnable by rwa [← hSchedMsg])
                · exact absurd hEq hNeTid
      | none =>
        -- Blocking: Enqueue → storeTcbIpcStateAndMessage(.blockedOnSend) → removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId false sender st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hObjInv1 : st1.objects.invExt :=
            endpointQueueEnqueue_preserves_objects_invExt endpointId false sender st st1 hObjInv hEnq
          have hSchedEnq := endpointQueueEnqueue_scheduler_eq endpointId false sender st st1 hEnq
          have hContractEnq := contracts_of_same_scheduler_ipcState st st1 hSchedEnq
            (fun tid tcb' h => endpointQueueEnqueue_tcb_ipcState_backward endpointId false sender st st1 tid tcb' hObjInv hEnq h)
            ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply, hBlockNotif⟩
          cases hMsg : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            rcases hContractEnq with ⟨hReady', hBlockSend', hBlockRecv', hBlockCall', hBlockReply', hBlockNotif'⟩
            have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq st1 st2 sender (.blockedOnSend endpointId) (some msg) hMsg
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
            · -- runnableThreadIpcReady
              intro tid tcb' hTcb' hRun'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = sender
              · subst hNe; exact absurd hRun' (removeRunnable_not_mem_self st2 _)
              · have hNeObjId : tid.toObjId ≠ sender.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 sender _ (some msg) tid.toObjId hNeObjId hObjInv1 hMsg).symm.trans hTcb'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 sender tid).mp hRun'
                exact hReady' tid tcb' hTcbPre (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])
            · -- blockedOnSendNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = sender
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ sender.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 sender _ (some msg) tid.toObjId hNeObjId hObjInv1 hMsg).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 sender tid).mp hRun'
                exact hBlockSend' tid tcb' eid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])
            · -- blockedOnReceiveNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = sender
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ sender.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 sender _ (some msg) tid.toObjId hNeObjId hObjInv1 hMsg).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 sender tid).mp hRun'
                exact hBlockRecv' tid tcb' eid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])
            · -- blockedOnCallNotRunnable
              intro tid tcb' eid hTcb' hIpcState'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = sender
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ sender.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 sender _ (some msg) tid.toObjId hNeObjId hObjInv1 hMsg).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 sender tid).mp hRun'
                exact hBlockCall' tid tcb' eid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])
            · -- blockedOnReplyNotRunnable
              intro tid tcb' eid rt hTcb' hIpcState'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = sender
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ sender.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 sender _ (some msg) tid.toObjId hNeObjId hObjInv1 hMsg).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 sender tid).mp hRun'
                exact hBlockReply' tid tcb' eid rt hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])
            · -- blockedOnNotificationNotRunnable (WS-F6/D2)
              intro tid tcb' nid hTcb' hIpcState'
              rw [removeRunnable_preserves_objects] at hTcb'
              by_cases hNe : tid = sender
              · subst hNe; exact removeRunnable_not_mem_self st2 _
              · have hNeObjId : tid.toObjId ≠ sender.toObjId := fun h => hNe (threadId_toObjId_injective h)
                have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st1 st2 sender _ (some msg) tid.toObjId hNeObjId hObjInv1 hMsg).symm.trans hTcb'
                intro hRun'
                have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 sender tid).mp hRun'
                exact hBlockNotif' tid tcb' nid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedMsg])

/-- WS-F1/TPI-D08: endpointReceiveDual preserves ipcInvariant. -/
theorem endpointReceiveDual_preserves_ipcInvariant
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (senderId : SeLe4n.ThreadId)
    (hInv : ipcInvariant st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReceiveDual endpointId receiver st = .ok (senderId, st')) :
    ipcInvariant st' := by
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.sendQ.head with
      | some _ =>
        -- Handshake: PopHead → senderWasCall check → storeTcbIpcStateAndMessage → ...
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInvPop : pair.2.2.objects.invExt :=
            endpointQueuePopHead_preserves_objects_invExt endpointId false st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          have hInv1 := endpointQueuePopHead_preserves_ipcInvariant endpointId false st pair.2.2 pair.1 hInv hObjInv hPop
          -- Branch on senderWasCall (case-split on returned TCB's ipcState)
          cases hSenderIpc : pair.2.1.ipcState with
          | blockedOnCall _ =>
            -- senderWasCall = true, call path
            simp only [hSenderIpc, ite_true] at hStep
            cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 (.blockedOnReply endpointId (some receiver)) none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              have hObjInvMsg : st2.objects.invExt :=
                storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ none hObjInvPop hMsg
              have hInv2 := storeTcbIpcStateAndMessage_preserves_ipcInvariant pair.2.2 st2 pair.1 (.blockedOnReply endpointId (some receiver)) none hInv1 hObjInvPop hMsg
              revert hStep
              -- AK1-D: atomic (.ready, senderMsg) receiver update
              cases hPend : storeTcbIpcStateAndMessage st2 receiver .ready _ with
              | ok st4 =>
                exact fun h => (Prod.mk.inj (Except.ok.inj h)).2 ▸ storeTcbIpcStateAndMessage_preserves_ipcInvariant _ _ receiver _ _ hInv2 hObjInvMsg hPend
              | error _ => simp
          | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnReply _ _ =>
            -- senderWasCall = false, send path
            simp only [hSenderIpc] at hStep
            cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              have hObjInvMsg : st2.objects.invExt :=
                storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ none hObjInvPop hMsg
              have hInv2 := storeTcbIpcStateAndMessage_preserves_ipcInvariant pair.2.2 st2 pair.1 .ready none hInv1 hObjInvPop hMsg
              have hInv3 : ipcInvariant (ensureRunnable st2 pair.1) :=
                fun oid ntfn h => hInv2 oid ntfn (by rwa [ensureRunnable_preserves_objects] at h)
              have hObjInvEns : (ensureRunnable st2 pair.1).objects.invExt := by
                rwa [ensureRunnable_preserves_objects]
              revert hStep
              -- AK1-D: atomic (.ready, senderMsg) receiver update
              cases hPend : storeTcbIpcStateAndMessage (ensureRunnable st2 pair.1) receiver .ready _ with
              | ok st4 =>
                exact fun h => (Prod.mk.inj (Except.ok.inj h)).2 ▸ storeTcbIpcStateAndMessage_preserves_ipcInvariant _ _ receiver _ _ hInv3 hObjInvEns hPend
              | error _ => simp
      | none =>
        -- AI4-A: Blocking: cleanup → Enqueue → storeTcbIpcState → removeRunnable
        -- cleanupPreReceiveDonation only modifies schedContextBinding (TCBs) and
        -- boundThread (SchedContext). ipcInvariant checks notification objects,
        -- which are unchanged by the cleanup.
        -- AK1-A (I-H01): Operational path now uses `cleanupPreReceiveDonationChecked`
        -- for error propagation. Destructure the Except first; on `.ok stClean`
        -- bridge to the defensive variant so existing frame lemmas compose.
        cases hChecked : cleanupPreReceiveDonationChecked st receiver with
        | error _ => simp [hHead, hChecked] at hStep
        | ok stClean =>
          have hBridge : stClean = cleanupPreReceiveDonation st receiver :=
            (cleanupPreReceiveDonationChecked_ok_eq_cleanup st stClean receiver hChecked).symm
          simp only [hHead, hChecked] at hStep
          rw [hBridge] at hStep
          have hObjInvClean := cleanupPreReceiveDonation_preserves_objects_invExt st receiver hObjInv
          have hInvClean : ipcInvariant (cleanupPreReceiveDonation st receiver) :=
            cleanupPreReceiveDonation_frame_helper st receiver hInv
              (fun scId owner st' hRet =>
                fun oid ntfn hObj' => hInv oid ntfn
                  (returnDonatedSchedContext_notification_backward st st' receiver scId owner hObjInv hRet oid ntfn hObj'))
          cases hEnq : endpointQueueEnqueue endpointId true receiver (cleanupPreReceiveDonation st receiver) with
          | error e => simp [hEnq] at hStep
          | ok st1 =>
            simp only [hEnq] at hStep
            have hObjInvEnq : st1.objects.invExt :=
              endpointQueueEnqueue_preserves_objects_invExt endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hEnq
            have hInv1 := endpointQueueEnqueue_preserves_ipcInvariant endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hInvClean hObjInvClean hEnq
            cases hIpc : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
            | error e => simp [hIpc] at hStep
            | ok st2 =>
              simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hEq⟩ := hStep; subst hEq
              have hInv2 := storeTcbIpcState_preserves_ipcInvariant st1 st2 receiver _ hInv1 hObjInvEnq hIpc
              exact fun oid ntfn h => hInv2 oid ntfn (by rwa [removeRunnable_preserves_objects] at h)

/-- WS-F1/TPI-D08: endpointReceiveDual preserves schedulerInvariantBundle. -/
theorem endpointReceiveDual_preserves_schedulerInvariantBundle
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (senderId : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st)
    (hCurrNotHead : currentNotEndpointQueueHead st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReceiveDual endpointId receiver st = .ok (senderId, st')) :
    schedulerInvariantBundle st' := by
  rcases hInv with ⟨hQCC, hRQU, hCTV⟩
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.sendQ.head with
      | some _ =>
        -- Handshake: PopHead → senderWasCall check → storeTcbIpcStateAndMessage → ...
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInv1 : pair.2.2.objects.invExt :=
            endpointQueuePopHead_preserves_objects_invExt endpointId false st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          have hSchedPop := endpointQueuePopHead_scheduler_eq endpointId false st pair.2.2 pair.1 hPop
          -- Branch on senderWasCall (case-split on returned TCB's ipcState)
          cases hSenderIpc : pair.2.1.ipcState with
          | blockedOnCall _ =>
            -- senderWasCall = true, call path
            simp only [hSenderIpc, ite_true] at hStep
            cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 (.blockedOnReply endpointId (some receiver)) none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              have hObjInvMsg : st2.objects.invExt :=
                storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ none hObjInv1 hMsg
              have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq pair.2.2 st2 pair.1 (.blockedOnReply endpointId (some receiver)) none hMsg
              have hSchedEq : st2.scheduler = st.scheduler := hSchedMsg.trans hSchedPop
              revert hStep
              -- AK1-D: atomic (.ready, senderMsg) receiver update
              cases hPend : storeTcbIpcStateAndMessage st2 receiver .ready _ with
              | ok st4 =>
                intro h; have h_eq := (Prod.mk.inj (Except.ok.inj h)).2; subst h_eq
                have hSchedPend := storeTcbIpcStateAndMessage_scheduler_eq _ _ receiver _ _ hPend
                refine ⟨?_, ?_, ?_⟩
                · rw [queueCurrentConsistent]; rw [queueCurrentConsistent] at hQCC; rwa [hSchedPend, hSchedEq]
                · show st4.scheduler.runnable.Nodup
                  rw [show st4.scheduler.runnable = st2.scheduler.runnable from congrArg SchedulerState.runnable hSchedPend, hSchedEq]; exact hRQU
                · unfold currentThreadValid; rw [hSchedPend, hSchedEq]
                  cases hCurr : st.scheduler.current with
                  | none => simp
                  | some x =>
                    simp only []
                    have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by simp [currentThreadValid, hCurr] at hCTV; exact hCTV
                    rcases hCTV' with ⟨tcbX, hTcbX⟩
                    obtain ⟨tcb1, hTcb1⟩ := endpointQueuePopHead_tcb_forward endpointId false st pair.2.2 pair.1 x.toObjId tcbX hObjInv hPop hTcbX
                    by_cases hNeTid : x.toObjId = pair.1.toObjId
                    · have hTargetTcb : ∃ t, pair.2.2.objects[pair.1.toObjId]? = some (.tcb t) := hNeTid ▸ ⟨tcb1, hTcb1⟩
                      have htgt := storeTcbIpcStateAndMessage_tcb_exists_at_target pair.2.2 st2 pair.1 (.blockedOnReply endpointId (some receiver)) none hObjInv1 hMsg hTargetTcb
                      obtain ⟨tcb_tgt, htcb_tgt⟩ := htgt
                      exact storeTcbIpcStateAndMessage_tcb_forward _ _ receiver _ _ x.toObjId tcb_tgt hObjInvMsg hPend (by rwa [← hNeTid] at htcb_tgt)
                    · have h1 := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 (.blockedOnReply endpointId (some receiver)) none x.toObjId hNeTid hObjInv1 hMsg) ▸ hTcb1
                      exact storeTcbIpcStateAndMessage_tcb_forward _ _ receiver _ _ x.toObjId tcb1 hObjInvMsg hPend h1
              | error _ => simp
          | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnReply _ _ =>
            -- senderWasCall = false, send path
            simp only [hSenderIpc] at hStep
            cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq pair.2.2 st2 pair.1 .ready none hMsg
              have hSchedEq : st2.scheduler = st.scheduler := hSchedMsg.trans hSchedPop
              have hInvER : schedulerInvariantBundle (ensureRunnable st2 pair.1) := by
                refine ⟨?_, ?_, ?_⟩
                · unfold queueCurrentConsistent; rw [ensureRunnable_scheduler_current, hSchedEq]
                  cases hCurr : st.scheduler.current with
                  | none => trivial
                  | some x =>
                    have hNotMem : x ∉ st.scheduler.runnable := by
                      have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this
                    have hNe : x ≠ pair.1 := by
                      have hHeadEq := endpointQueuePopHead_returns_head endpointId false st ep pair.1 pair.2.2 hObj hPop
                      simp at hHeadEq
                      intro hEq; rw [hEq] at hCurr
                      have := hCurrNotHead; simp [currentNotEndpointQueueHead, hCurr] at this
                      exact (this endpointId ep hObj).2 hHeadEq
                    exact ensureRunnable_not_mem_of_not_mem st2 pair.1 x (hSchedEq ▸ hNotMem) hNe
                · exact ensureRunnable_nodup st2 pair.1 (hSchedEq ▸ hRQU)
                · show currentThreadValid (ensureRunnable st2 pair.1)
                  unfold currentThreadValid
                  simp only [ensureRunnable_scheduler_current, ensureRunnable_preserves_objects, hSchedEq]
                  cases hCurr : st.scheduler.current with
                  | none => simp
                  | some x =>
                    simp only []
                    have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by simp [currentThreadValid, hCurr] at hCTV; exact hCTV
                    rcases hCTV' with ⟨tcbX, hTcbX⟩
                    obtain ⟨tcb1, hTcb1⟩ := endpointQueuePopHead_tcb_forward endpointId false st pair.2.2 pair.1 x.toObjId tcbX hObjInv hPop hTcbX
                    by_cases hNeTid : x.toObjId = pair.1.toObjId
                    · exact storeTcbIpcStateAndMessage_tcb_exists_at_target pair.2.2 st2 pair.1 .ready none hObjInv1 hMsg (hNeTid ▸ ⟨tcb1, hTcb1⟩) |>.imp fun _ h => by rwa [← hNeTid] at h
                    · exact ⟨tcb1, (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 .ready none x.toObjId hNeTid hObjInv1 hMsg) ▸ hTcb1⟩
              have hObjInvMsg : st2.objects.invExt :=
                storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ none hObjInv1 hMsg
              have hObjInvEns : (ensureRunnable st2 pair.1).objects.invExt := by
                rwa [ensureRunnable_preserves_objects]
              revert hStep
              -- AK1-D: atomic (.ready, senderMsg) receiver update
              cases hPend : storeTcbIpcStateAndMessage (ensureRunnable st2 pair.1) receiver .ready _ with
              | ok st4 =>
                intro h; have h_eq := (Prod.mk.inj (Except.ok.inj h)).2; subst h_eq
                rcases hInvER with ⟨hQCC', hRQU', hCTV'⟩
                have hSchedPend := storeTcbIpcStateAndMessage_scheduler_eq _ _ receiver _ _ hPend
                refine ⟨?_, ?_, ?_⟩
                · rw [queueCurrentConsistent]; rw [queueCurrentConsistent] at hQCC'; rwa [hSchedPend]
                · show st4.scheduler.runnable.Nodup
                  rw [show st4.scheduler.runnable = (ensureRunnable st2 pair.1).scheduler.runnable from congrArg SchedulerState.runnable hSchedPend]; exact hRQU'
                · unfold currentThreadValid; rw [hSchedPend]
                  cases hCurr : (ensureRunnable st2 pair.1).scheduler.current with
                  | none => simp
                  | some x =>
                    simp only []
                    have ⟨tcbX, hTcbX⟩ : ∃ tcb', (ensureRunnable st2 pair.1).objects[x.toObjId]? = some (.tcb tcb') := by simp [currentThreadValid, hCurr] at hCTV'; exact hCTV'
                    exact storeTcbIpcStateAndMessage_tcb_forward _ _ receiver _ _ x.toObjId tcbX hObjInvEns hPend hTcbX
              | error _ => simp
      | none =>
        -- AI4-A: Blocking: cleanup → Enqueue → storeTcbIpcState → removeRunnable
        -- AK1-A (I-H01): Destructure checked variant, bridge to defensive form.
        cases hChecked : cleanupPreReceiveDonationChecked st receiver with
        | error _ => simp [hHead, hChecked] at hStep
        | ok stClean =>
          have hBridge : stClean = cleanupPreReceiveDonation st receiver :=
            (cleanupPreReceiveDonationChecked_ok_eq_cleanup st stClean receiver hChecked).symm
          simp only [hHead, hChecked] at hStep
          rw [hBridge] at hStep
          have hObjInvClean := cleanupPreReceiveDonation_preserves_objects_invExt st receiver hObjInv
          have hSchedClean := cleanupPreReceiveDonation_scheduler_eq st receiver
          cases hEnq : endpointQueueEnqueue endpointId true receiver (cleanupPreReceiveDonation st receiver) with
          | error e => simp [hEnq] at hStep
          | ok st1 =>
            simp only [hEnq] at hStep
            have hObjInvEnq : st1.objects.invExt :=
              endpointQueueEnqueue_preserves_objects_invExt endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hEnq
            have hSchedEnq := endpointQueueEnqueue_scheduler_eq endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hEnq
            cases hIpc : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
            | error e => simp [hIpc] at hStep
            | ok st2 =>
              simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hEq⟩ := hStep; subst hEq
              have hSchedIpc := storeTcbIpcState_scheduler_eq st1 st2 receiver _ hIpc
              have hSchedEq : st2.scheduler = st.scheduler := hSchedIpc.trans (hSchedEnq.trans hSchedClean)
              refine ⟨?_, ?_, ?_⟩
              · unfold queueCurrentConsistent
                rw [removeRunnable_scheduler_current, congrArg SchedulerState.current hSchedEq]
                cases hCurr : st.scheduler.current with
                | none => simp
                | some x =>
                  by_cases hEq' : x = receiver
                  · subst hEq'; simp
                  · rw [if_neg (show ¬(some x = some receiver) from fun h => hEq' (Option.some.inj h))]
                    show x ∉ (removeRunnable st2 receiver).scheduler.runnable
                    have hNotMem : x ∉ st.scheduler.runnable := by
                      have := hQCC; simp [queueCurrentConsistent, hCurr] at this; exact this
                    exact removeRunnable_not_mem_of_not_mem st2 receiver x (hSchedEq ▸ hNotMem)
              · exact removeRunnable_nodup st2 receiver (hSchedEq ▸ hRQU)
              · unfold currentThreadValid
                rw [removeRunnable_preserves_objects, removeRunnable_scheduler_current,
                    congrArg SchedulerState.current hSchedEq]
                cases hCurr : st.scheduler.current with
                | none => simp
                | some x =>
                  by_cases hEq' : x = receiver
                  · subst hEq'; simp
                  · rw [if_neg (show ¬(some x = some receiver) from fun h => hEq' (Option.some.inj h))]
                    show ∃ tcb, st2.objects[x.toObjId]? = some (.tcb tcb)
                    have hCTV' : ∃ tcb', st.objects[x.toObjId]? = some (.tcb tcb') := by
                      simp [currentThreadValid, hCurr] at hCTV; exact hCTV
                    rcases hCTV' with ⟨tcbX, hTcbX⟩
                    -- Forward tcb lookup through cleanup + enqueue
                    -- AI4-A: cleanupPreReceiveDonation stores TCBs at receiver/owner
                    -- and SchedContext at scId — the current thread x ≠ receiver,
                    -- so its TCB is either unchanged or re-stored as a TCB.
                    have hTcbClean : ∃ tcb', (cleanupPreReceiveDonation st receiver).objects[x.toObjId]? = some (.tcb tcb') :=
                      cleanupPreReceiveDonation_tcb_forward st receiver x hObjInv ⟨tcbX, hTcbX⟩
                    obtain ⟨tcbClean, hTcbClean'⟩ := hTcbClean
                    obtain ⟨tcb1, hTcb1⟩ := endpointQueueEnqueue_tcb_forward endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 x.toObjId tcbClean hObjInvClean hEnq hTcbClean'
                    have hNeTid : x.toObjId ≠ receiver.toObjId := fun h => hEq' (threadId_toObjId_injective h)
                    exact ⟨tcb1, (storeTcbIpcState_preserves_objects_ne st1 st2 receiver _ x.toObjId hNeTid hObjInvEnq hIpc) ▸ hTcb1⟩

/-- AK1-D (I-M02): Specialised contracts-preservation lemma for a `.ready`
    write. Unlike `contracts_of_same_scheduler_ipcState`, this helper does
    not require the target's ipcState to be preserved — the target is set
    to `.ready`, which satisfies `runnableThreadIpcReady` and vacuously
    satisfies every `blockedOn*NotRunnable` predicate. For non-target tids,
    ipcState IS preserved (witnessed by `storeTcbIpcStateAndMessage_preserves_objects_ne`).

    Used by `endpointReceiveDual_preserves_ipcSchedulerContractPredicates`
    to discharge the post-rendezvous receiver-side `storeTcbIpcStateAndMessage
    receiver .ready senderMsg` transition without requiring the
    `_tcb_ipcState_backward` lemma (which would be false at the target). -/
theorem storeTcbIpcStateAndMessage_ready_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (target : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st target .ready msg = .ok st')
    (hContract : ipcSchedulerContractPredicates st) :
    ipcSchedulerContractPredicates st' := by
  rcases hContract with ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply, hBlockNotif⟩
  have hSched := storeTcbIpcStateAndMessage_scheduler_eq st st' target .ready msg hStep
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- runnableThreadIpcReady
    intro tid tcb' hTcb' hRun'
    by_cases hEq : tid.toObjId = target.toObjId
    · -- Target tid: post-state ipcState is .ready (forced by the store).
      exact storeTcbIpcStateAndMessage_ipcState_eq st st' target .ready msg hObjInv hStep tcb' (hEq ▸ hTcb')
    · -- Non-target tid: ipcState preserved; pre-state hypothesis applies.
      have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st' target .ready msg tid.toObjId hEq hObjInv hStep).symm.trans hTcb'
      exact hReady tid tcb' hTcbPre (show tid ∈ st.scheduler.runnable by rwa [← hSched])
  · -- blockedOnSendNotRunnable
    intro tid tcb' eid hTcb' hIpcState'
    by_cases hEq : tid.toObjId = target.toObjId
    · -- Target ipcState is .ready, cannot be .blockedOnSend
      have := storeTcbIpcStateAndMessage_ipcState_eq st st' target .ready msg hObjInv hStep tcb' (hEq ▸ hTcb')
      rw [this] at hIpcState'; cases hIpcState'
    · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st' target .ready msg tid.toObjId hEq hObjInv hStep).symm.trans hTcb'
      have := hBlockSend tid tcb' eid hTcbPre hIpcState'
      intro hRun'; exact this (show tid ∈ st.scheduler.runnable by rwa [← hSched])
  · -- blockedOnReceiveNotRunnable
    intro tid tcb' eid hTcb' hIpcState'
    by_cases hEq : tid.toObjId = target.toObjId
    · have := storeTcbIpcStateAndMessage_ipcState_eq st st' target .ready msg hObjInv hStep tcb' (hEq ▸ hTcb')
      rw [this] at hIpcState'; cases hIpcState'
    · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st' target .ready msg tid.toObjId hEq hObjInv hStep).symm.trans hTcb'
      have := hBlockRecv tid tcb' eid hTcbPre hIpcState'
      intro hRun'; exact this (show tid ∈ st.scheduler.runnable by rwa [← hSched])
  · -- blockedOnCallNotRunnable
    intro tid tcb' eid hTcb' hIpcState'
    by_cases hEq : tid.toObjId = target.toObjId
    · have := storeTcbIpcStateAndMessage_ipcState_eq st st' target .ready msg hObjInv hStep tcb' (hEq ▸ hTcb')
      rw [this] at hIpcState'; cases hIpcState'
    · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st' target .ready msg tid.toObjId hEq hObjInv hStep).symm.trans hTcb'
      have := hBlockCall tid tcb' eid hTcbPre hIpcState'
      intro hRun'; exact this (show tid ∈ st.scheduler.runnable by rwa [← hSched])
  · -- blockedOnReplyNotRunnable
    intro tid tcb' eid rt hTcb' hIpcState'
    by_cases hEq : tid.toObjId = target.toObjId
    · have := storeTcbIpcStateAndMessage_ipcState_eq st st' target .ready msg hObjInv hStep tcb' (hEq ▸ hTcb')
      rw [this] at hIpcState'; cases hIpcState'
    · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st' target .ready msg tid.toObjId hEq hObjInv hStep).symm.trans hTcb'
      have := hBlockReply tid tcb' eid rt hTcbPre hIpcState'
      intro hRun'; exact this (show tid ∈ st.scheduler.runnable by rwa [← hSched])
  · -- blockedOnNotificationNotRunnable
    intro tid tcb' nid hTcb' hIpcState'
    by_cases hEq : tid.toObjId = target.toObjId
    · have := storeTcbIpcStateAndMessage_ipcState_eq st st' target .ready msg hObjInv hStep tcb' (hEq ▸ hTcb')
      rw [this] at hIpcState'; cases hIpcState'
    · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne st st' target .ready msg tid.toObjId hEq hObjInv hStep).symm.trans hTcb'
      have := hBlockNotif tid tcb' nid hTcbPre hIpcState'
      intro hRun'; exact this (show tid ∈ st.scheduler.runnable by rwa [← hSched])

/-- WS-F1/TPI-D08: endpointReceiveDual preserves ipcSchedulerContractPredicates. -/
theorem endpointReceiveDual_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (senderId : SeLe4n.ThreadId)
    (hContract : ipcSchedulerContractPredicates st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReceiveDual endpointId receiver st = .ok (senderId, st')) :
    ipcSchedulerContractPredicates st' := by
  rcases hContract with ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply, hBlockNotif⟩
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.sendQ.head with
      | some _ =>
        -- Handshake: PopHead → senderWasCall check → storeTcbIpcStateAndMessage → ...
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hSchedPop := endpointQueuePopHead_scheduler_eq endpointId false st pair.2.2 pair.1 hPop
          have hObjInv1 : pair.2.2.objects.invExt :=
            endpointQueuePopHead_preserves_objects_invExt endpointId false st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          have hContractPop := contracts_of_same_scheduler_ipcState st pair.2.2 hSchedPop
            (fun tid tcb' h => endpointQueuePopHead_tcb_ipcState_backward endpointId false st pair.2.2 pair.1 tid tcb' hObjInv hPop h)
            ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply, hBlockNotif⟩
          -- Establish pre-state TCB for the helper lemma
          have hPreTcb := endpointQueuePopHead_returns_pre_tcb endpointId false st ep pair.1 pair.2.1 pair.2.2 hObj hPop
          -- Branch on senderWasCall (case-split on returned TCB's ipcState)
          cases hSenderIpc : pair.2.1.ipcState with
          | blockedOnCall _ =>
            -- senderWasCall = true, call path
            simp only [hSenderIpc, ite_true] at hStep
            rcases hContractPop with ⟨hReady', hBlockSend', hBlockRecv', hBlockCall', hBlockReply', hBlockNotif'⟩
            -- Establish post-state TCB for pair.1 and its ipcState relation
            obtain ⟨postTcb, hPostTcb⟩ := endpointQueuePopHead_tcb_forward endpointId false st pair.2.2 pair.1 pair.1.toObjId pair.2.1 hObjInv hPop hPreTcb
            obtain ⟨preTcb, hPreTcb2, hIpcRel⟩ := endpointQueuePopHead_tcb_ipcState_backward endpointId false st pair.2.2 pair.1 pair.1 postTcb hObjInv hPop hPostTcb
            have : preTcb = pair.2.1 := by rw [hPreTcb] at hPreTcb2; exact (KernelObject.tcb.inj (Option.some.inj hPreTcb2.symm))
            subst this
            cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 (.blockedOnReply endpointId (some receiver)) none with
              | error e => simp [hMsg] at hStep
              | ok st2 =>
                simp only [hMsg] at hStep
                have hObjInvMsg : st2.objects.invExt :=
                  storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ none hObjInv1 hMsg
                have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq pair.2.2 st2 pair.1 (.blockedOnReply endpointId (some receiver)) none hMsg
                -- Build contracts for st2 (sender set to blockedOnReply, no ensureRunnable)
                have hContractSt2 : ipcSchedulerContractPredicates st2 := by
                  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
                  · intro tid tcb' hTcb' hRun'
                    by_cases hNe : tid.toObjId = pair.1.toObjId
                    · -- tid is the sender (same ObjId); sender had blockedOnCall, so not runnable
                      have hTidEq := ThreadId.toObjId_injective tid pair.1 hNe
                      subst hTidEq
                      exact absurd (show pair.1 ∈ pair.2.2.scheduler.runnable by rwa [← hSchedMsg])
                        (hBlockCall' pair.1 postTcb _ hPostTcb (by rw [← hIpcRel]; exact hSenderIpc))
                    · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 _ none tid.toObjId hNe hObjInv1 hMsg).symm.trans hTcb'
                      exact hReady' tid tcb' hTcbPre (show tid ∈ pair.2.2.scheduler.runnable by rwa [← hSchedMsg])
                  · intro tid tcb' eid hTcb' hIpcState'
                    by_cases hNe : tid.toObjId = pair.1.toObjId
                    · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2.2 st2 pair.1 (.blockedOnReply endpointId (some receiver)) none hObjInv1 hMsg tcb' (hNe ▸ hTcb')
                      rw [this] at hIpcState'; cases hIpcState'
                    · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 _ none tid.toObjId hNe hObjInv1 hMsg).symm.trans hTcb'
                      intro hRun'
                      exact hBlockSend' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.2.scheduler.runnable by rwa [← hSchedMsg])
                  · intro tid tcb' eid hTcb' hIpcState'
                    by_cases hNe : tid.toObjId = pair.1.toObjId
                    · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2.2 st2 pair.1 (.blockedOnReply endpointId (some receiver)) none hObjInv1 hMsg tcb' (hNe ▸ hTcb')
                      rw [this] at hIpcState'; cases hIpcState'
                    · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 _ none tid.toObjId hNe hObjInv1 hMsg).symm.trans hTcb'
                      intro hRun'
                      exact hBlockRecv' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.2.scheduler.runnable by rwa [← hSchedMsg])
                  · intro tid tcb' eid hTcb' hIpcState'
                    by_cases hNe : tid.toObjId = pair.1.toObjId
                    · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2.2 st2 pair.1 (.blockedOnReply endpointId (some receiver)) none hObjInv1 hMsg tcb' (hNe ▸ hTcb')
                      rw [this] at hIpcState'; cases hIpcState'
                    · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 _ none tid.toObjId hNe hObjInv1 hMsg).symm.trans hTcb'
                      intro hRun'
                      exact hBlockCall' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.2.scheduler.runnable by rwa [← hSchedMsg])
                  · intro tid tcb' eid rt hTcb' hIpcState'
                    by_cases hNe : tid.toObjId = pair.1.toObjId
                    · -- tid is the sender; its ipc state in st2 is .blockedOnReply
                      -- The sender had .blockedOnCall in pair.2.2, so was not runnable
                      have hTidEq := ThreadId.toObjId_injective tid pair.1 hNe
                      subst hTidEq
                      intro hRun'
                      have hRunPre : pair.1 ∈ pair.2.2.scheduler.runnable := by rwa [← hSchedMsg]
                      exact hBlockCall' pair.1 postTcb _ hPostTcb (by rw [← hIpcRel]; exact hSenderIpc) hRunPre
                    · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 _ none tid.toObjId hNe hObjInv1 hMsg).symm.trans hTcb'
                      intro hRun'
                      exact hBlockReply' tid tcb' eid rt hTcbPre hIpcState' (show tid ∈ pair.2.2.scheduler.runnable by rwa [← hSchedMsg])
                  · -- blockedOnNotificationNotRunnable (WS-F6/D2)
                    intro tid tcb' nid hTcb' hIpcState'
                    by_cases hNe : tid.toObjId = pair.1.toObjId
                    · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2.2 st2 pair.1 (.blockedOnReply endpointId (some receiver)) none hObjInv1 hMsg tcb' (hNe ▸ hTcb')
                      rw [this] at hIpcState'; cases hIpcState'
                    · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 _ none tid.toObjId hNe hObjInv1 hMsg).symm.trans hTcb'
                      intro hRun'
                      exact hBlockNotif' tid tcb' nid hTcbPre hIpcState' (show tid ∈ pair.2.2.scheduler.runnable by rwa [← hSchedMsg])
                -- storeTcbPendingMessage preserves contracts
                revert hStep
                -- AK1-D: atomic (.ready, senderMsg) receiver update
                cases hPend : storeTcbIpcStateAndMessage st2 receiver .ready _ with
                | ok st4 =>
                  intro h; have h_eq := (Prod.mk.inj (Except.ok.inj h)).2; subst h_eq
                  exact storeTcbIpcStateAndMessage_ready_preserves_ipcSchedulerContractPredicates
                    _ _ receiver _ hObjInvMsg hPend hContractSt2
                | error _ => simp
            | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnReply _ _ =>
              -- senderWasCall = false, send path
              simp only [hSenderIpc] at hStep
              rcases hContractPop with ⟨hReady', hBlockSend', hBlockRecv', hBlockCall', hBlockReply', hBlockNotif'⟩
              cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready none with
              | error e => simp [hMsg] at hStep
              | ok st2 =>
                simp only [hMsg] at hStep
                have hObjInvMsg2 : st2.objects.invExt :=
                  storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ none hObjInv1 hMsg
                have hObjInvEns2 : (ensureRunnable st2 pair.1).objects.invExt := by
                  rwa [ensureRunnable_preserves_objects]
                have hSchedMsg := storeTcbIpcStateAndMessage_scheduler_eq pair.2.2 st2 pair.1 .ready none hMsg
                have hContractER : ipcSchedulerContractPredicates (ensureRunnable st2 pair.1) := by
                  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
                  · intro tid tcb' hTcb' hRun'
                    rw [ensureRunnable_preserves_objects] at hTcb'
                    by_cases hNe : tid.toObjId = pair.1.toObjId
                    · exact storeTcbIpcStateAndMessage_ipcState_eq pair.2.2 st2 pair.1 .ready none hObjInv1 hMsg tcb' (hNe ▸ hTcb')
                    · have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 .ready none tid.toObjId hNe hObjInv1 hMsg).symm.trans hTcb'
                      have hNeTid : tid ≠ pair.1 := fun h => hNe (congrArg ThreadId.toObjId h)
                      rcases ensureRunnable_mem_reverse st2 pair.1 tid hRun' with hOld | hEq
                      · exact hReady' tid tcb' hTcbPre (show tid ∈ pair.2.2.scheduler.runnable by rwa [← hSchedMsg])
                      · exact absurd hEq hNeTid
                  · intro tid tcb' eid hTcb' hIpcState'
                    rw [ensureRunnable_preserves_objects] at hTcb'
                    by_cases hNe : tid.toObjId = pair.1.toObjId
                    · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2.2 st2 pair.1 .ready none hObjInv1 hMsg tcb' (hNe ▸ hTcb')
                      rw [this] at hIpcState'; cases hIpcState'
                    · have hNeTid : tid ≠ pair.1 := fun h => hNe (congrArg ThreadId.toObjId h)
                      have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 .ready none tid.toObjId hNe hObjInv1 hMsg).symm.trans hTcb'
                      intro hRun'; rcases ensureRunnable_mem_reverse st2 pair.1 tid hRun' with hOld | hEq
                      · exact hBlockSend' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.2.scheduler.runnable by rwa [← hSchedMsg])
                      · exact absurd hEq hNeTid
                  · intro tid tcb' eid hTcb' hIpcState'
                    rw [ensureRunnable_preserves_objects] at hTcb'
                    by_cases hNe : tid.toObjId = pair.1.toObjId
                    · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2.2 st2 pair.1 .ready none hObjInv1 hMsg tcb' (hNe ▸ hTcb')
                      rw [this] at hIpcState'; cases hIpcState'
                    · have hNeTid : tid ≠ pair.1 := fun h => hNe (congrArg ThreadId.toObjId h)
                      have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 .ready none tid.toObjId hNe hObjInv1 hMsg).symm.trans hTcb'
                      intro hRun'; rcases ensureRunnable_mem_reverse st2 pair.1 tid hRun' with hOld | hEq
                      · exact hBlockRecv' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.2.scheduler.runnable by rwa [← hSchedMsg])
                      · exact absurd hEq hNeTid
                  · intro tid tcb' eid hTcb' hIpcState'
                    rw [ensureRunnable_preserves_objects] at hTcb'
                    by_cases hNe : tid.toObjId = pair.1.toObjId
                    · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2.2 st2 pair.1 .ready none hObjInv1 hMsg tcb' (hNe ▸ hTcb')
                      rw [this] at hIpcState'; cases hIpcState'
                    · have hNeTid : tid ≠ pair.1 := fun h => hNe (congrArg ThreadId.toObjId h)
                      have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 .ready none tid.toObjId hNe hObjInv1 hMsg).symm.trans hTcb'
                      intro hRun'; rcases ensureRunnable_mem_reverse st2 pair.1 tid hRun' with hOld | hEq
                      · exact hBlockCall' tid tcb' eid hTcbPre hIpcState' (show tid ∈ pair.2.2.scheduler.runnable by rwa [← hSchedMsg])
                      · exact absurd hEq hNeTid
                  · intro tid tcb' eid rt hTcb' hIpcState'
                    rw [ensureRunnable_preserves_objects] at hTcb'
                    by_cases hNe : tid.toObjId = pair.1.toObjId
                    · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2.2 st2 pair.1 .ready none hObjInv1 hMsg tcb' (hNe ▸ hTcb')
                      rw [this] at hIpcState'; cases hIpcState'
                    · have hNeTid : tid ≠ pair.1 := fun h => hNe (congrArg ThreadId.toObjId h)
                      have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 .ready none tid.toObjId hNe hObjInv1 hMsg).symm.trans hTcb'
                      intro hRun'; rcases ensureRunnable_mem_reverse st2 pair.1 tid hRun' with hOld | hEq
                      · exact hBlockReply' tid tcb' eid rt hTcbPre hIpcState' (show tid ∈ pair.2.2.scheduler.runnable by rwa [← hSchedMsg])
                      · exact absurd hEq hNeTid
                  · -- blockedOnNotificationNotRunnable (WS-F6/D2)
                    intro tid tcb' nid hTcb' hIpcState'
                    rw [ensureRunnable_preserves_objects] at hTcb'
                    by_cases hNe : tid.toObjId = pair.1.toObjId
                    · have := storeTcbIpcStateAndMessage_ipcState_eq pair.2.2 st2 pair.1 .ready none hObjInv1 hMsg tcb' (hNe ▸ hTcb')
                      rw [this] at hIpcState'; cases hIpcState'
                    · have hNeTid : tid ≠ pair.1 := fun h => hNe (congrArg ThreadId.toObjId h)
                      have hTcbPre := (storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 .ready none tid.toObjId hNe hObjInv1 hMsg).symm.trans hTcb'
                      intro hRun'; rcases ensureRunnable_mem_reverse st2 pair.1 tid hRun' with hOld | hEq
                      · exact hBlockNotif' tid tcb' nid hTcbPre hIpcState' (show tid ∈ pair.2.2.scheduler.runnable by rwa [← hSchedMsg])
                      · exact absurd hEq hNeTid
                revert hStep
                -- AK1-D: atomic (.ready, senderMsg) receiver update
                cases hPend : storeTcbIpcStateAndMessage (ensureRunnable st2 pair.1) receiver .ready _ with
                | ok st4 =>
                  intro h; have h_eq := (Prod.mk.inj (Except.ok.inj h)).2; subst h_eq
                  exact storeTcbIpcStateAndMessage_ready_preserves_ipcSchedulerContractPredicates
                    _ _ receiver _ hObjInvEns2 hPend hContractER
                | error _ => simp
      | none =>
        -- AI4-A: Blocking: cleanup → Enqueue → storeTcbIpcState(.blockedOnReceive) → removeRunnable
        -- AK1-A (I-H01): Destructure checked variant, bridge to defensive form.
        cases hChecked : cleanupPreReceiveDonationChecked st receiver with
        | error _ => simp [hHead, hChecked] at hStep
        | ok stClean =>
          have hBridge : stClean = cleanupPreReceiveDonation st receiver :=
            (cleanupPreReceiveDonationChecked_ok_eq_cleanup st stClean receiver hChecked).symm
          simp only [hHead, hChecked] at hStep
          rw [hBridge] at hStep
          have hObjInvClean := cleanupPreReceiveDonation_preserves_objects_invExt st receiver hObjInv
          have hSchedClean := cleanupPreReceiveDonation_scheduler_eq st receiver
          -- cleanupPreReceiveDonation preserves ipcSchedulerContractPredicates because
          -- it only modifies schedContextBinding (not ipcState) and scheduler is unchanged.
          have hContractClean : ipcSchedulerContractPredicates (cleanupPreReceiveDonation st receiver) :=
            contracts_of_same_scheduler_ipcState st (cleanupPreReceiveDonation st receiver) hSchedClean
              (fun tid tcb' h => cleanupPreReceiveDonation_tcb_ipcState_backward st receiver hObjInv tid tcb' h)
              ⟨hReady, hBlockSend, hBlockRecv, hBlockCall, hBlockReply, hBlockNotif⟩
          cases hEnq : endpointQueueEnqueue endpointId true receiver (cleanupPreReceiveDonation st receiver) with
          | error e => simp [hEnq] at hStep
          | ok st1 =>
            simp only [hEnq] at hStep
            have hObjInvEnq2 : st1.objects.invExt :=
              endpointQueueEnqueue_preserves_objects_invExt endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hEnq
            have hSchedEnq := endpointQueueEnqueue_scheduler_eq endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hEnq
            rcases hContractClean with ⟨hReady'c, hBlockSend'c, hBlockRecv'c, hBlockCall'c, hBlockReply'c, hBlockNotif'c⟩
            have hContractEnq := contracts_of_same_scheduler_ipcState (cleanupPreReceiveDonation st receiver) st1 hSchedEnq
              (fun tid tcb' h => endpointQueueEnqueue_tcb_ipcState_backward endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 tid tcb' hObjInvClean hEnq h)
              ⟨hReady'c, hBlockSend'c, hBlockRecv'c, hBlockCall'c, hBlockReply'c, hBlockNotif'c⟩
            cases hIpc : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
            | error e => simp [hIpc] at hStep
            | ok st2 =>
              simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hEq⟩ := hStep; subst hEq
              rcases hContractEnq with ⟨hReady', hBlockSend', hBlockRecv', hBlockCall', hBlockReply', hBlockNotif'⟩
              have hSchedIpc := storeTcbIpcState_scheduler_eq st1 st2 receiver _ hIpc
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
              · -- runnableThreadIpcReady
                intro tid tcb' hTcb' hRun'
                rw [removeRunnable_preserves_objects] at hTcb'
                by_cases hNe : tid = receiver
                · subst hNe; exact absurd hRun' (removeRunnable_not_mem_self st2 _)
                · have hNeObjId : tid.toObjId ≠ receiver.toObjId := fun h => hNe (threadId_toObjId_injective h)
                  have hTcbPre := (storeTcbIpcState_preserves_objects_ne st1 st2 receiver _ tid.toObjId hNeObjId hObjInvEnq2 hIpc).symm.trans hTcb'
                  have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 receiver tid).mp hRun'
                  exact hReady' tid tcb' hTcbPre (show tid ∈ st1.scheduler.runnable by rwa [← hSchedIpc])
              · -- blockedOnSendNotRunnable
                intro tid tcb' eid hTcb' hIpcState'
                rw [removeRunnable_preserves_objects] at hTcb'
                by_cases hNe : tid = receiver
                · subst hNe; exact removeRunnable_not_mem_self st2 _
                · have hNeObjId : tid.toObjId ≠ receiver.toObjId := fun h => hNe (threadId_toObjId_injective h)
                  have hTcbPre := (storeTcbIpcState_preserves_objects_ne st1 st2 receiver _ tid.toObjId hNeObjId hObjInvEnq2 hIpc).symm.trans hTcb'
                  intro hRun'
                  have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 receiver tid).mp hRun'
                  exact hBlockSend' tid tcb' eid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedIpc])
              · -- blockedOnReceiveNotRunnable
                intro tid tcb' eid hTcb' hIpcState'
                rw [removeRunnable_preserves_objects] at hTcb'
                by_cases hNe : tid = receiver
                · subst hNe; exact removeRunnable_not_mem_self st2 _
                · have hNeObjId : tid.toObjId ≠ receiver.toObjId := fun h => hNe (threadId_toObjId_injective h)
                  have hTcbPre := (storeTcbIpcState_preserves_objects_ne st1 st2 receiver _ tid.toObjId hNeObjId hObjInvEnq2 hIpc).symm.trans hTcb'
                  intro hRun'
                  have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 receiver tid).mp hRun'
                  exact hBlockRecv' tid tcb' eid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedIpc])
              · -- blockedOnCallNotRunnable
                intro tid tcb' eid hTcb' hIpcState'
                rw [removeRunnable_preserves_objects] at hTcb'
                by_cases hNe : tid = receiver
                · subst hNe; exact removeRunnable_not_mem_self st2 _
                · have hNeObjId : tid.toObjId ≠ receiver.toObjId := fun h => hNe (threadId_toObjId_injective h)
                  have hTcbPre := (storeTcbIpcState_preserves_objects_ne st1 st2 receiver _ tid.toObjId hNeObjId hObjInvEnq2 hIpc).symm.trans hTcb'
                  intro hRun'
                  have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 receiver tid).mp hRun'
                  exact hBlockCall' tid tcb' eid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedIpc])
              · -- blockedOnReplyNotRunnable
                intro tid tcb' eid rt hTcb' hIpcState'
                rw [removeRunnable_preserves_objects] at hTcb'
                by_cases hNe : tid = receiver
                · subst hNe; exact removeRunnable_not_mem_self st2 _
                · have hNeObjId : tid.toObjId ≠ receiver.toObjId := fun h => hNe (threadId_toObjId_injective h)
                  have hTcbPre := (storeTcbIpcState_preserves_objects_ne st1 st2 receiver _ tid.toObjId hNeObjId hObjInvEnq2 hIpc).symm.trans hTcb'
                  intro hRun'
                  have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 receiver tid).mp hRun'
                  exact hBlockReply' tid tcb' eid rt hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedIpc])
              · -- blockedOnNotificationNotRunnable (WS-F6/D2)
                intro tid tcb' nid hTcb' hIpcState'
                rw [removeRunnable_preserves_objects] at hTcb'
                by_cases hNe : tid = receiver
                · subst hNe; exact removeRunnable_not_mem_self st2 _
                · have hNeObjId : tid.toObjId ≠ receiver.toObjId := fun h => hNe (threadId_toObjId_injective h)
                  have hTcbPre := (storeTcbIpcState_preserves_objects_ne st1 st2 receiver _ tid.toObjId hNeObjId hObjInvEnq2 hIpc).symm.trans hTcb'
                  intro hRun'
                  have ⟨hRunSt2, _⟩ := (removeRunnable_runnable_mem st2 receiver tid).mp hRun'
                  exact hBlockNotif' tid tcb' nid hTcbPre hIpcState' (show tid ∈ st1.scheduler.runnable by rwa [← hSchedIpc])

/-- WS-F1/TPI-D08: endpointQueueRemoveDual preserves ipcInvariant.
Arbitrary O(1) removal only modifies TCB queue links and endpoint head/tail pointers
(sendQ/receiveQ); it does not change notification objects. -/
theorem endpointQueueRemoveDual_preserves_ipcInvariant
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isSendQ : Bool) (tid : SeLe4n.ThreadId)
    (hInv : ipcInvariant st) (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isSendQ tid st = .ok ((), st')) :
    ipcInvariant st' := by
  exact fun oid ntfn hObjPost => hInv oid ntfn (endpointQueueRemoveDual_notification_backward st st' endpointId isSendQ tid oid ntfn hObjInv hStep hObjPost)

/-- WS-F1/TPI-D08: endpointQueueRemoveDual preserves schedulerInvariantBundle. -/
theorem endpointQueueRemoveDual_preserves_schedulerInvariantBundle
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isSendQ : Bool) (tid : SeLe4n.ThreadId)
    (hInv : schedulerInvariantBundle st) (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isSendQ tid st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  rcases hInv with ⟨hQCC, hRQU, hCTV⟩
  have hSchedEq := endpointQueueRemoveDual_scheduler_eq st st' endpointId isSendQ tid hStep
  refine ⟨hSchedEq ▸ hQCC, hSchedEq ▸ hRQU, ?_⟩
  unfold currentThreadValid
  rw [hSchedEq]
  cases hCurr : st.scheduler.current with
  | none => trivial
  | some ctid =>
    have hCTV' : ∃ tcb', st.objects[ctid.toObjId]? = some (.tcb tcb') := by
      simp [currentThreadValid, hCurr] at hCTV; exact hCTV
    rcases hCTV' with ⟨tcbC, hTcbC⟩
    exact endpointQueueRemoveDual_tcb_forward st st' endpointId isSendQ tid ctid.toObjId tcbC hObjInv hStep hTcbC

/-- WS-F1/TPI-D08: endpointQueueRemoveDual preserves ipcSchedulerContractPredicates.
endpointQueueRemoveDual only modifies queue link fields via storeObject (endpoint)
and storeTcbQueueLinks. The scheduler is unchanged and all TCB ipcStates are
preserved, so the contract predicates are maintained via
contracts_of_same_scheduler_ipcState. -/
theorem endpointQueueRemoveDual_preserves_ipcSchedulerContractPredicates
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isSendQ : Bool) (tid : SeLe4n.ThreadId)
    (hContract : ipcSchedulerContractPredicates st) (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isSendQ tid st = .ok ((), st')) :
    ipcSchedulerContractPredicates st' :=
  contracts_of_same_scheduler_ipcState st st'
    (endpointQueueRemoveDual_scheduler_eq st st' endpointId isSendQ tid hStep)
    (fun anyTid tcb' h => endpointQueueRemoveDual_tcb_ipcState_backward st st' endpointId isSendQ tid anyTid tcb' hObjInv hStep h)
    hContract

-- ============================================================================
-- M3-E4: ipcUnwrapCaps + WithCaps wrapper preservation theorems
--
-- Key structural property: ipcUnwrapCaps only modifies CNode objects (via
-- cspaceInsertSlot) and CDT fields (via ensureCdtNodeForSlot/addEdge). It
-- does NOT touch endpoint objects, notification objects, TCB queue links,
-- or scheduler state. Therefore all IPC invariants that depend only on
-- these untouched components are trivially preserved.
-- ============================================================================

/-- M3-E4: ipcUnwrapCaps preserves ipcInvariant. For oid ≠ receiverRoot,
notifications are unchanged by `preserves_objects_ne`. For oid = receiverRoot,
case-split on what was at receiverRoot in st: if it was a notification, it's
preserved by `preserves_ntfn_objects`; otherwise, `receiverRoot_not_ntfn`
shows no notification can appear. No precondition needed. -/
theorem ipcUnwrapCaps_preserves_ipcInvariant
    (msg : IpcMessage) (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hInv : ipcInvariant st)
    (hObjInv : st.objects.invExt)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
             = .ok (summary, st')) :
    ipcInvariant st' := by
  intro oid ntfn hObj
  by_cases hNe : oid = receiverRoot
  · -- oid = receiverRoot: rewrite without subst to keep receiverRoot in scope
    rw [hNe] at hObj
    cases hR : st.objects[receiverRoot]? with
    | none =>
      have hNotNtfn : ∀ ntfn, st.objects[receiverRoot]? ≠ some (.notification ntfn) := by
        simp [hR]
      exact absurd hObj (ipcUnwrapCaps_receiverRoot_not_ntfn msg senderRoot receiverRoot
        slotBase grantRight st st' summary hNotNtfn hObjInv hStep ntfn)
    | some obj =>
      cases obj with
      | notification ntfn' =>
        have hPreserved := ipcUnwrapCaps_preserves_ntfn_objects msg senderRoot receiverRoot
          slotBase grantRight st st' summary receiverRoot ntfn' hR hObjInv hStep
        have hEq : KernelObject.notification ntfn' = KernelObject.notification ntfn :=
          Option.some.inj (hPreserved.symm.trans hObj)
        cases hEq; exact hInv receiverRoot ntfn hR
      | cnode _ | tcb _ | endpoint _ | vspaceRoot _ | untyped _ | schedContext _ =>
        have hNotNtfn : ∀ ntfn, st.objects[receiverRoot]? ≠ some (.notification ntfn) := by
          simp [hR]
        exact absurd hObj (ipcUnwrapCaps_receiverRoot_not_ntfn msg senderRoot receiverRoot
          slotBase grantRight st st' summary hNotNtfn hObjInv hStep ntfn)
  · rw [ipcUnwrapCaps_preserves_objects_ne msg senderRoot receiverRoot slotBase
      grantRight st st' summary oid hNe hObjInv hStep] at hObj
    exact hInv oid ntfn hObj

/-- endpointSendDual preserves st.objects.invExt. -/
theorem endpointSendDual_preserves_objects_invExt
    (st stMid : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), stMid)) :
    stMid.objects.invExt := by
  unfold endpointSendDual at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInvPop : pair.2.2.objects.invExt :=
            endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hObjInvMsg : st2.objects.invExt :=
              storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ _ hObjInvPop hMsg
            rwa [ensureRunnable_preserves_objects]
      | none =>
        cases hEnq : endpointQueueEnqueue endpointId false sender st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hObjInvEnq : st1.objects.invExt :=
            endpointQueueEnqueue_preserves_objects_invExt endpointId false sender st st1 hObjInv hEnq
          cases hMsg : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hObjInvMsg : st2.objects.invExt :=
              storeTcbIpcStateAndMessage_preserves_objects_invExt st1 st2 sender _ _ hObjInvEnq hMsg
            rwa [removeRunnable_preserves_objects]

/-- endpointReceiveDual preserves st.objects.invExt. -/
theorem endpointReceiveDual_preserves_objects_invExt
    (st stMid : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver senderId : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReceiveDual endpointId receiver st = .ok (senderId, stMid)) :
    stMid.objects.invExt := by
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.sendQ.head with
      | some _ =>
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInvPop : pair.2.2.objects.invExt :=
            endpointQueuePopHead_preserves_objects_invExt endpointId false st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          cases hSenderIpc : pair.2.1.ipcState with
          | blockedOnCall _ =>
            simp only [hSenderIpc, ite_true] at hStep
            cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 (.blockedOnReply endpointId (some receiver)) none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              have hObjInvMsg : st2.objects.invExt :=
                storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ none hObjInvPop hMsg
              revert hStep
              -- AK1-D: atomic (.ready, senderMsg) receiver update
              cases hPend : storeTcbIpcStateAndMessage st2 receiver .ready _ with
              | ok st4 =>
                intro h
                have h_eq := (Prod.mk.inj (Except.ok.inj h)).2; subst h_eq
                exact storeTcbIpcStateAndMessage_preserves_objects_invExt st2 _ receiver _ _ hObjInvMsg hPend
              | error _ => simp
          | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnReply _ _ =>
            simp only [hSenderIpc] at hStep
            cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              have hObjInvMsg : st2.objects.invExt :=
                storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ none hObjInvPop hMsg
              have hObjInvEns : (ensureRunnable st2 pair.1).objects.invExt := by
                rwa [ensureRunnable_preserves_objects]
              revert hStep
              -- AK1-D: atomic (.ready, senderMsg) receiver update
              cases hPend : storeTcbIpcStateAndMessage (ensureRunnable st2 pair.1) receiver .ready _ with
              | ok st4 =>
                intro h
                have h_eq := (Prod.mk.inj (Except.ok.inj h)).2; subst h_eq
                exact storeTcbIpcStateAndMessage_preserves_objects_invExt (ensureRunnable st2 pair.1) _ receiver _ _ hObjInvEns hPend
              | error _ => simp
      | none =>
        -- AI4-A: cleanup → Enqueue → storeTcbIpcState → removeRunnable
        -- AK1-A (I-H01): Destructure checked variant, bridge to defensive form.
        cases hChecked : cleanupPreReceiveDonationChecked st receiver with
        | error _ => simp [hHead, hChecked] at hStep
        | ok stClean =>
          have hBridge : stClean = cleanupPreReceiveDonation st receiver :=
            (cleanupPreReceiveDonationChecked_ok_eq_cleanup st stClean receiver hChecked).symm
          simp only [hHead, hChecked] at hStep
          rw [hBridge] at hStep
          have hObjInvClean := cleanupPreReceiveDonation_preserves_objects_invExt st receiver hObjInv
          cases hEnq : endpointQueueEnqueue endpointId true receiver (cleanupPreReceiveDonation st receiver) with
          | error e => simp [hEnq] at hStep
          | ok st1 =>
            simp only [hEnq] at hStep
            have hObjInvEnq : st1.objects.invExt :=
              endpointQueueEnqueue_preserves_objects_invExt endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hEnq
            cases hIpc : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
            | error e => simp [hIpc] at hStep
            | ok st2 =>
              simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hEq⟩ := hStep; subst hEq
              have hObjInvIpc : st2.objects.invExt :=
                storeTcbIpcState_preserves_objects_invExt st1 st2 receiver _ hObjInvEnq hIpc
              rwa [removeRunnable_preserves_objects]

/-- M3-E4: endpointSendDualWithCaps preserves ipcInvariant. Every branch
either returns the post-send state (preserved by endpointSendDual) or
passes through ipcUnwrapCaps (preserved by ipcUnwrapCaps_preserves_ipcInvariant,
which requires no precondition). -/
theorem endpointSendDualWithCaps_preserves_ipcInvariant
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (senderCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hInv : ipcInvariant st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointSendDualWithCaps endpointId sender msg endpointRights
             senderCspaceRoot receiverSlotBase st = .ok (summary, st')) :
    ipcInvariant st' := by
  simp only [endpointSendDualWithCaps] at hStep
  cases hSend : endpointSendDual endpointId sender msg st with
  | error e => simp [hSend] at hStep
  | ok pair =>
    rcases pair with ⟨_, stMid⟩
    have hInvMid := endpointSendDual_preserves_ipcInvariant st stMid endpointId sender msg hInv hObjInv hSend
    have hObjInvMid := endpointSendDual_preserves_objects_invExt st stMid endpointId sender msg hObjInv hSend
    simp [hSend] at hStep
    -- AN10-B: post-migration `endpointSendDualWithCaps` reads via
    -- `getEndpoint?`; case-split on the typed helper.
    cases hEp : st.getEndpoint? endpointId with
    | none =>
      -- hasReceiver = false → if-then branch taken
      simp [hEp] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hInvMid
    | some ep =>
      simp [hEp] at hStep
      cases hHead : ep.receiveQ.head with
      | none =>
        -- hasReceiver = false → if-then branch
        simp [hHead] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hInvMid
      | some receiverId =>
        simp [hHead] at hStep
        -- hasReceiver = true, condition reduces to msg.caps.isEmpty
        by_cases hEmpty : msg.caps = #[]
        · simp [hEmpty] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hInvMid
        · simp [hEmpty] at hStep
          cases hLookup : lookupCspaceRoot stMid receiverId with
          | none => simp [hLookup] at hStep -- AK1-I: fail-closed, vacuous
          | some recvRoot =>
            simp [hLookup] at hStep
            exact ipcUnwrapCaps_preserves_ipcInvariant msg senderCspaceRoot recvRoot
              receiverSlotBase _ stMid st' summary hInvMid hObjInvMid hStep

/-- M3-E4: endpointReceiveDualWithCaps preserves ipcInvariant. -/
theorem endpointReceiveDualWithCaps_preserves_ipcInvariant
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (endpointRights : AccessRightSet)
    (receiverCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (senderId : SeLe4n.ThreadId)
    (summary : CapTransferSummary)
    (hInv : ipcInvariant st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReceiveDualWithCaps endpointId receiver endpointRights
             receiverCspaceRoot receiverSlotBase st = .ok ((senderId, summary), st')) :
    ipcInvariant st' := by
  simp only [endpointReceiveDualWithCaps] at hStep
  cases hRecv : endpointReceiveDual endpointId receiver st with
  | error e => simp [hRecv] at hStep
  | ok pair =>
    rcases pair with ⟨sid, stMid⟩
    have hInvMid := endpointReceiveDual_preserves_ipcInvariant st stMid endpointId
      receiver sid hInv hObjInv hRecv
    have hObjInvMid := endpointReceiveDual_preserves_objects_invExt st stMid endpointId
      receiver sid hObjInv hRecv
    simp [hRecv] at hStep
    -- AN10-B: post-migration `endpointReceiveDualWithCaps` reads via
    -- `getTcb?`; case-split on the typed helper.
    cases hTcb : stMid.getTcb? receiver with
    | none => simp [hTcb] at hStep; obtain ⟨⟨_, _⟩, rfl⟩ := hStep; exact hInvMid
    | some receiverTcb =>
      simp [hTcb] at hStep
      cases hMsg : receiverTcb.pendingMessage with
      | none => simp [hMsg] at hStep; obtain ⟨⟨_, _⟩, rfl⟩ := hStep; exact hInvMid
      | some msg =>
        simp [hMsg] at hStep
        -- After simp, the if condition may be on msg.caps.isEmpty or msg.caps = #[]
        split at hStep
        · -- if-then: caps empty, state unchanged
          obtain ⟨⟨_, _⟩, rfl⟩ := hStep; exact hInvMid
        · -- if-else: caps non-empty, ipcUnwrapCaps runs
          -- Case split on lookupCspaceRoot to determine senderRoot value
          cases hLookup : lookupCspaceRoot stMid sid with
          | none =>
            -- U-H13: Missing CSpace root now returns error, contradicting .ok
            simp only [hLookup] at hStep; contradiction
          | some senderRoot =>
            -- senderRoot = senderRoot
            simp only [hLookup] at hStep
            cases hUnwrap : ipcUnwrapCaps msg senderRoot receiverCspaceRoot
                receiverSlotBase (endpointRights.mem .grant) stMid with
            | error e => simp [hUnwrap] at hStep
            | ok pair =>
              rcases pair with ⟨s, stFinal⟩
              simp [hUnwrap] at hStep
              obtain ⟨⟨_, _⟩, rfl⟩ := hStep
              exact ipcUnwrapCaps_preserves_ipcInvariant msg senderRoot receiverCspaceRoot
                receiverSlotBase _ stMid stFinal s hInvMid hObjInvMid hUnwrap

-- ============================================================================
-- V3-G4 (M-PRF-5): waitingThreadsPendingMessageNone preservation
-- for endpoint operations
-- ============================================================================

-- V3-G4 (M-PRF-5): `endpointSendDual`/`endpointReceiveDual` preserve
-- `waitingThreadsPendingMessageNone`.
-- Machine-checked proofs in Structural.lean:
--   `endpointSendDual_preserves_waitingThreadsPendingMessageNone`
--   `endpointReceiveDual_preserves_waitingThreadsPendingMessageNone`
--   `endpointReply_preserves_waitingThreadsPendingMessageNone`

