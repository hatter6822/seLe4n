/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.Defs
import SeLe4n.Kernel.IPC.DualQueue.Transport

/-!
# V3-K: endpointQueueNoDup Preservation Proofs

Preservation proofs for `endpointQueueNoDup` across all IPC operations.
K-1 (no self-loops) follows from `tcbQueueChainAcyclic`. All new work targets K-2
(send/receive queue head disjointness).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

set_option linter.unusedVariables false

-- ============================================================================
-- Section 1: Primitive frame lemmas
-- ============================================================================

/-- V3-K-prim-1: Storing a non-endpoint, non-TCB object preserves endpointQueueNoDup.
Neither endpoint queues nor TCB queueNext fields change. -/
theorem storeObject_non_ep_non_tcb_preserves_endpointQueueNoDup
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hInv : endpointQueueNoDup st)
    (hObjInv : st.objects.invExt)
    (hNotEp : ∀ ep, obj ≠ .endpoint ep)
    (hNotTcb : ∀ tcb, obj ≠ .tcb tcb)
    (hStore : storeObject oid obj st = .ok ((), st')) :
    endpointQueueNoDup st' := by
  intro oid' ep' hEp'
  by_cases hEq : oid' = oid
  · -- Stored object is at oid' = oid, but obj is not an endpoint — contradiction
    have hObj := storeObject_objects_eq st st' oid obj hObjInv hStore
    rw [hEq] at hEp'; rw [hObj] at hEp'; cases hEp'
    exact absurd rfl (hNotEp ep')
  · have hFrame := storeObject_objects_ne st st' oid oid' obj hEq hObjInv hStore
    rw [hFrame] at hEp'
    have ⟨hK1, hK2⟩ := hInv oid' ep' hEp'
    constructor
    · intro tid tcb hTcb'
      by_cases hEqT : tid.toObjId = oid
      · have hObj := storeObject_objects_eq st st' oid obj hObjInv hStore
        rw [hEqT] at hTcb'; rw [hObj] at hTcb'; cases hTcb'
        exact absurd rfl (hNotTcb tcb)
      · have hFrameT := storeObject_objects_ne st st' oid tid.toObjId obj hEqT hObjInv hStore
        rw [hFrameT] at hTcb'
        exact hK1 tid tcb hTcb'
    · exact hK2

/-- V3-K-prim-2: storeTcbQueueLinks preserves endpointQueueNoDup.
Storing a TCB does not modify any endpoint object, so K-2 (queue head disjointness)
transfers directly. K-1 follows from post-state tcbQueueChainAcyclic. -/
theorem storeTcbQueueLinks_preserves_endpointQueueNoDup
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId)
    (hInv : endpointQueueNoDup st)
    (hAcyclic : tcbQueueChainAcyclic st')
    (hObjInv : st.objects.invExt)
    (hStore : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    endpointQueueNoDup st' := by
  intro oid ep hEp
  -- Endpoint objects are unaffected by TCB stores: need oid ≠ tid.toObjId
  have hNe : oid ≠ tid.toObjId := by
    intro hEq; subst hEq
    unfold storeTcbQueueLinks at hStore
    cases hLk : lookupTcb st tid with
    | none => simp [hLk] at hStore
    | some tcb =>
      simp only [hLk] at hStore
      cases hSt : storeObject tid.toObjId (.tcb (tcbWithQueueLinks tcb prev pprev next)) st with
      | error e => simp [hSt] at hStore
      | ok pair =>
        simp only [hSt] at hStore
        have hEqSt := Except.ok.inj hStore; subst hEqSt
        rw [storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hSt] at hEp
        cases hEp
  have hFrame := storeTcbQueueLinks_preserves_objects_ne st st' tid prev pprev next oid hNe hObjInv hStore
  rw [hFrame] at hEp
  have ⟨_, hK2⟩ := hInv oid ep hEp
  exact ⟨fun tid' tcb' hTcb' => tcbQueueChainAcyclic_no_self_loop hAcyclic tid' tcb' hTcb', hK2⟩

/-- V3-K-prim-3: Storing an endpoint preserves endpointQueueNoDup when the new
endpoint's queue heads satisfy disjointness. -/
theorem storeObject_endpoint_preserves_endpointQueueNoDup
    (st st' : SystemState) (oid : SeLe4n.ObjId) (ep' : Endpoint)
    (hInv : endpointQueueNoDup st)
    (hAcyclic : tcbQueueChainAcyclic st')
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid (.endpoint ep') st = .ok ((), st'))
    (hDisjoint : ep'.sendQ.head = none ∨ ep'.receiveQ.head = none ∨
                 ep'.sendQ.head ≠ ep'.receiveQ.head) :
    endpointQueueNoDup st' := by
  intro oid' ep'' hEp'
  by_cases hEq : oid' = oid
  · have hObj := storeObject_objects_eq st st' oid _ hObjInv hStore
    rw [hEq] at hEp'; rw [hObj] at hEp'; cases hEp'
    exact ⟨fun tid tcb hTcb => tcbQueueChainAcyclic_no_self_loop hAcyclic tid tcb hTcb, hDisjoint⟩
  · have hFrame := storeObject_objects_ne st st' oid oid' _ hEq hObjInv hStore
    rw [hFrame] at hEp'
    have ⟨_, hK2⟩ := hInv oid' ep'' hEp'
    exact ⟨fun tid tcb hTcb => tcbQueueChainAcyclic_no_self_loop hAcyclic tid tcb hTcb, hK2⟩

-- ============================================================================
-- Section 2: TCB store primitives + general transfer + scheduler helpers
-- ============================================================================

/-- Pointwise object equality implies endpointQueueNoDup transfer. -/
theorem endpointQueueNoDup_of_objects_eq
    (st st' : SystemState)
    (hLk : ∀ (x : SeLe4n.ObjId), st'.objects[x]? = st.objects[x]?)
    (hInv : endpointQueueNoDup st) :
    endpointQueueNoDup st' := by
  intro oid ep hEp
  rw [hLk] at hEp
  have ⟨hK1, hK2⟩ := hInv oid ep hEp
  exact ⟨fun tid tcb hTcb => by rw [hLk] at hTcb; exact hK1 tid tcb hTcb, hK2⟩

/-- ensureRunnable preserves endpointQueueNoDup (scheduler only, objects unchanged). -/
theorem ensureRunnable_preserves_endpointQueueNoDup
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : endpointQueueNoDup st) :
    endpointQueueNoDup (ensureRunnable st tid) :=
  endpointQueueNoDup_of_objects_eq st (ensureRunnable st tid)
    (fun x => congrArg (·.get? x) (ensureRunnable_preserves_objects st tid)) hInv

/-- removeRunnable preserves endpointQueueNoDup (scheduler only, objects unchanged). -/
theorem removeRunnable_preserves_endpointQueueNoDup
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : endpointQueueNoDup st) :
    endpointQueueNoDup (removeRunnable st tid) :=
  endpointQueueNoDup_of_objects_eq st (removeRunnable st tid)
    (fun x => congrArg (·.get? x) (removeRunnable_preserves_objects st tid)) hInv

/-- Storing a TCB (via storeTcbIpcStateAndMessage) preserves endpointQueueNoDup.
K-2 preserved because endpoint objects are unchanged by TCB stores.
K-1 preserved because { tcb with ipcState, pendingMessage } preserves queueNext. -/
theorem storeTcbIpcStateAndMessage_preserves_endpointQueueNoDup
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipcState : ThreadIpcState) (msg : Option IpcMessage)
    (hInv : endpointQueueNoDup st)
    (hObjInv : st.objects.invExt)
    (hStore : storeTcbIpcStateAndMessage st tid ipcState msg = .ok st') :
    endpointQueueNoDup st' := by
  unfold storeTcbIpcStateAndMessage at hStore
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStore
  | some tcb =>
    simp only [hLookup] at hStore
    cases hSt : storeObject tid.toObjId (.tcb { tcb with ipcState := ipcState, pendingMessage := msg }) st with
    | error e => simp [hSt] at hStore
    | ok pair =>
      simp only [hSt, Except.ok.injEq] at hStore; subst hStore
      have hTcbObj := lookupTcb_some_objects st tid tcb hLookup
      intro oid ep hEp
      have hNe : oid ≠ tid.toObjId := by
        intro h; subst h
        rw [storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hSt] at hEp; cases hEp
      rw [storeObject_objects_ne st pair.2 tid.toObjId oid _ hNe hObjInv hSt] at hEp
      have ⟨hK1, hK2⟩ := hInv oid ep hEp
      constructor
      · intro tid' tcb' hTcb'
        by_cases hEq : tid'.toObjId = tid.toObjId
        · rw [hEq, storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hSt] at hTcb'
          cases hTcb'
          -- queueNext preserved: show tcb.queueNext ≠ some tid'
          exact hK1 tid' tcb (hEq ▸ hTcbObj)
        · rw [storeObject_objects_ne st pair.2 tid.toObjId tid'.toObjId _ hEq hObjInv hSt] at hTcb'
          exact hK1 tid' tcb' hTcb'
      · exact hK2

/-- storeTcbIpcStateAndMessage_fromTcb preserves endpointQueueNoDup. -/
theorem storeTcbIpcStateAndMessage_fromTcb_preserves_endpointQueueNoDup
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (ipcState : ThreadIpcState) (msg : Option IpcMessage)
    (hInv : endpointQueueNoDup st)
    (hObjInv : st.objects.invExt)
    (hLookup : lookupTcb st tid = some tcb)
    (hStore : storeTcbIpcStateAndMessage_fromTcb st tid tcb ipcState msg = .ok st') :
    endpointQueueNoDup st' := by
  rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStore
  exact storeTcbIpcStateAndMessage_preserves_endpointQueueNoDup st st' tid ipcState msg hInv hObjInv hStore

/-- storeTcbIpcState preserves endpointQueueNoDup. -/
theorem storeTcbIpcState_preserves_endpointQueueNoDup
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipcState : ThreadIpcState)
    (hInv : endpointQueueNoDup st)
    (hObjInv : st.objects.invExt)
    (hStore : storeTcbIpcState st tid ipcState = .ok st') :
    endpointQueueNoDup st' := by
  unfold storeTcbIpcState at hStore
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStore
  | some tcb =>
    simp only [hLookup] at hStore
    cases hSt : storeObject tid.toObjId (.tcb { tcb with ipcState := ipcState }) st with
    | error e => simp [hSt] at hStore
    | ok pair =>
      simp only [hSt, Except.ok.injEq] at hStore
      subst hStore
      have hTcbObj := lookupTcb_some_objects st tid tcb hLookup
      intro oid ep hEp
      have hNe : oid ≠ tid.toObjId := by
        intro h; subst h
        rw [storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hSt] at hEp; cases hEp
      rw [storeObject_objects_ne st pair.2 tid.toObjId oid _ hNe hObjInv hSt] at hEp
      have ⟨hK1, hK2⟩ := hInv oid ep hEp
      constructor
      · intro tid' tcb' hTcb'
        by_cases hEq : tid'.toObjId = tid.toObjId
        · rw [hEq, storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hSt] at hTcb'
          cases hTcb'
          exact hK1 tid' tcb (hEq ▸ hTcbObj)
        · rw [storeObject_objects_ne st pair.2 tid.toObjId tid'.toObjId _ hEq hObjInv hSt] at hTcb'
          exact hK1 tid' tcb' hTcb'
      · exact hK2

/-- storeTcbPendingMessage preserves endpointQueueNoDup. -/
theorem storeTcbPendingMessage_preserves_endpointQueueNoDup
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (hInv : endpointQueueNoDup st)
    (hObjInv : st.objects.invExt)
    (hStore : storeTcbPendingMessage st tid msg = .ok st') :
    endpointQueueNoDup st' := by
  unfold storeTcbPendingMessage at hStore
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStore
  | some tcb =>
    simp only [hLookup] at hStore
    cases hSt : storeObject tid.toObjId (.tcb { tcb with pendingMessage := msg }) st with
    | error e => simp [hSt] at hStore
    | ok pair =>
      simp only [hSt, Except.ok.injEq] at hStore
      subst hStore
      have hTcbObj := lookupTcb_some_objects st tid tcb hLookup
      intro oid ep hEp
      have hNe : oid ≠ tid.toObjId := by
        intro h; subst h
        rw [storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hSt] at hEp; cases hEp
      rw [storeObject_objects_ne st pair.2 tid.toObjId oid _ hNe hObjInv hSt] at hEp
      have ⟨hK1, hK2⟩ := hInv oid ep hEp
      constructor
      · intro tid' tcb' hTcb'
        by_cases hEq : tid'.toObjId = tid.toObjId
        · rw [hEq, storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hSt] at hTcb'
          cases hTcb'
          exact hK1 tid' tcb (hEq ▸ hTcbObj)
        · rw [storeObject_objects_ne st pair.2 tid.toObjId tid'.toObjId _ hEq hObjInv hSt] at hTcb'
          exact hK1 tid' tcb' hTcb'
      · exact hK2

-- ============================================================================
-- Section 3: Per-operation preservation proofs
-- ============================================================================

/-- V3-K-op-9a: notificationSignal preserves endpointQueueNoDup.
Notification operations only modify notification objects and TCBs; no endpoint change. -/
theorem notificationSignal_preserves_endpointQueueNoDup
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hInv : endpointQueueNoDup st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    endpointQueueNoDup st' := by
  unfold notificationSignal at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hWaiters : ntfn.waitingThreads with
      | cons waiter rest =>
        -- Wake path: storeObject notification → storeTcbIpcStateAndMessage → ensureRunnable
        simp only [hWaiters] at hStep
        generalize hStore1 : storeObject notificationId _ st = r1 at hStep
        cases r1 with
        | error e => simp at hStep
        | ok pair1 =>
          simp only [] at hStep
          have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair1 hObjInv hStore1
          have hInv1 := storeObject_non_ep_non_tcb_preserves_endpointQueueNoDup
            st pair1.2 notificationId _ hInv hObjInv
            (fun ep => by intro h; cases h) (fun tcb => by intro h; cases h) hStore1
          generalize hMsg : storeTcbIpcStateAndMessage pair1.2 waiter .ready _ = rMsg at hStep
          cases rMsg with
          | error e => simp at hStep
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, rfl⟩ := hStep
            exact ensureRunnable_preserves_endpointQueueNoDup _ _ <|
              storeTcbIpcStateAndMessage_preserves_endpointQueueNoDup _ _ _ _ _ hInv1 hObjInv1 hMsg
      | nil =>
        -- Accumulate path: storeObject notification only
        simp only [hWaiters] at hStep
        exact storeObject_non_ep_non_tcb_preserves_endpointQueueNoDup
          st st' notificationId _ hInv hObjInv
          (fun ep => by intro h; cases h) (fun tcb => by intro h; cases h) hStep

/-- V3-K-op-9b: notificationWait preserves endpointQueueNoDup. -/
theorem notificationWait_preserves_endpointQueueNoDup
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge)
    (hInv : endpointQueueNoDup st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationWait notificationId waiter st = .ok (result, st')) :
    endpointQueueNoDup st' := by
  unfold notificationWait at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hBadge : ntfn.pendingBadge with
      | some badge =>
        -- Consume path: storeObject notification → storeTcbIpcState
        simp only [hBadge] at hStep
        generalize hStore1 : storeObject notificationId _ st = r1 at hStep
        cases r1 with
        | error e => simp at hStep
        | ok pair1 =>
          simp only [] at hStep
          have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair1 hObjInv hStore1
          have hInv1 := storeObject_non_ep_non_tcb_preserves_endpointQueueNoDup
            st pair1.2 notificationId _ hInv hObjInv
            (fun ep => by intro h; cases h) (fun tcb => by intro h; cases h) hStore1
          generalize hIpc : storeTcbIpcState pair1.2 waiter .ready = rIpc at hStep
          cases rIpc with
          | error e => simp at hStep
          | ok pair2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, rfl⟩ := hStep
            exact storeTcbIpcState_preserves_endpointQueueNoDup _ _ _ _ hInv1 hObjInv1 hIpc
      | none =>
        -- Block path: lookupTcb → storeObject notification → storeTcbIpcState_fromTcb → removeRunnable
        simp only [hBadge] at hStep
        cases hLookup : lookupTcb st waiter with
        | none => simp [hLookup] at hStep
        | some tcb =>
          simp only [hLookup] at hStep
          split at hStep
          · simp at hStep
          · generalize hStore1 : storeObject notificationId _ st = r1 at hStep
            cases r1 with
            | error e => simp at hStep
            | ok pair1 =>
              simp only [] at hStep
              have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair1 hObjInv hStore1
              have hInv1 := storeObject_non_ep_non_tcb_preserves_endpointQueueNoDup
                st pair1.2 notificationId _ hInv hObjInv
                (fun ep => by intro h; cases h) (fun tcb => by intro h; cases h) hStore1
              generalize hIpc : storeTcbIpcState_fromTcb pair1.2 waiter _ _ = rIpc at hStep
              cases rIpc with
              | error e => simp at hStep
              | ok pair2 =>
                simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, rfl⟩ := hStep
                have hLookup1 : lookupTcb pair1.2 waiter = some tcb := by
                  have hNe : waiter.toObjId ≠ notificationId := by
                    intro h
                    have hTcbObj := lookupTcb_some_objects st waiter tcb hLookup
                    rw [h] at hTcbObj; rw [hObj] at hTcbObj; cases hTcbObj
                  unfold lookupTcb
                  rw [show waiter.isReserved = false from by
                    unfold lookupTcb at hLookup; split at hLookup <;> simp_all]
                  rw [storeObject_objects_ne st pair1.2 notificationId waiter.toObjId _ hNe hObjInv hStore1]
                  unfold lookupTcb at hLookup
                  split at hLookup <;> simp_all
                rw [storeTcbIpcState_fromTcb_eq hLookup1] at hIpc
                exact removeRunnable_preserves_endpointQueueNoDup _ _ <|
                  storeTcbIpcState_preserves_endpointQueueNoDup _ _ _ _ hInv1 hObjInv1 hIpc

/-- V3-K-op-7: endpointReply preserves endpointQueueNoDup.
Reply only modifies a single TCB and scheduler. -/
theorem endpointReply_preserves_endpointQueueNoDup
    (st st' : SystemState) (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : endpointQueueNoDup st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    endpointQueueNoDup st' := by
  unfold endpointReply at hStep
  -- Message bounds checks come first in endpointReply
  split at hStep
  · simp at hStep
  · split at hStep
    · simp at hStep
    · cases hLookup : lookupTcb st target with
      | none => simp [hLookup] at hStep
      | some tcb =>
        simp only [hLookup] at hStep
        cases hIpc : tcb.ipcState with
        | blockedOnReply epId replyTarget =>
          simp only [hIpc] at hStep
          -- Handle authorization check (match on replyTarget, then if)
          split at hStep
          · -- replyTarget = some expected
            split at hStep
            · -- authorized path
              generalize hMsg : storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) = rMsg at hStep
              cases rMsg with
              | error e => simp at hStep
              | ok st1 =>
                simp at hStep; obtain ⟨_, rfl⟩ := hStep
                exact ensureRunnable_preserves_endpointQueueNoDup _ _ <|
                  storeTcbIpcStateAndMessage_fromTcb_preserves_endpointQueueNoDup
                    st st1 target tcb .ready (some msg) hInv hObjInv hLookup hMsg
            · simp at hStep
          · -- replyTarget = none (authorized = true)
            generalize hMsg : storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) = rMsg at hStep
            cases rMsg with
            | error e => simp at hStep
            | ok st1 =>
              simp at hStep; obtain ⟨_, rfl⟩ := hStep
              exact ensureRunnable_preserves_endpointQueueNoDup _ _ <|
                storeTcbIpcStateAndMessage_fromTcb_preserves_endpointQueueNoDup
                  st st1 target tcb .ready (some msg) hInv hObjInv hLookup hMsg
        | _ => simp [hIpc] at hStep

-- ============================================================================
-- Section 4: Queue operation proofs
-- ============================================================================

/-- V3-K-op-1: endpointQueueEnqueue preserves endpointQueueNoDup.
The opposite queue's head is required to be none (satisfied by all IPC block paths).
K-1 follows from post-state acyclicity. K-2 follows from opposite head = none. -/
theorem endpointQueueEnqueue_preserves_endpointQueueNoDup
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hInv : endpointQueueNoDup st)
    (hDQSI' : dualQueueSystemInvariant st')
    (hObjInv : st.objects.invExt)
    (hOppositeEmpty : ∀ ep, st.objects[endpointId]? = some (.endpoint ep) →
        (if isReceiveQ then ep.sendQ.head else ep.receiveQ.head) = none)
    (hEnqueue : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    endpointQueueNoDup st' := by
  intro oid ep' hEp'
  constructor
  · -- K-1: no self-loops from tcbQueueChainAcyclic
    exact fun tid' tcb hTcb => tcbQueueChainAcyclic_no_self_loop hDQSI'.2.2 tid' tcb hTcb
  · -- K-2: head disjointness
    by_cases hEq : oid = endpointId
    · -- Target endpoint: opposite queue head is none
      -- Unfold to extract the stored endpoint structure
      unfold endpointQueueEnqueue at hEnqueue
      cases hObj : st.objects[endpointId]? with
      | none => simp [hObj] at hEnqueue
      | some obj => cases obj with
        | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hEnqueue
        | endpoint ep =>
          simp only [hObj] at hEnqueue
          have hOppNone := hOppositeEmpty ep hObj
          cases hLookup : lookupTcb st tid with
          | none => simp [hLookup] at hEnqueue
          | some tcb =>
            simp only [hLookup] at hEnqueue
            split at hEnqueue
            · simp at hEnqueue
            · split at hEnqueue
              · simp at hEnqueue
              · -- Past guards, case split on tail
                revert hEnqueue
                cases hTail : (if isReceiveQ then ep.receiveQ else ep.sendQ).tail with
                | none =>
                  -- Empty queue case
                  cases hStore : storeObject endpointId _ st with
                  | error e => simp
                  | ok pair =>
                    simp only []
                    intro hLinks
                    -- After storeObject + storeTcbQueueLinks, endpoint at endpointId has
                    -- the stored ep' which has opposite queue head = none
                    have hObjInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                    -- The endpoint at endpointId in st' is unchanged from st1
                    -- (storeTcbQueueLinks stores a TCB at tid.toObjId ≠ endpointId)
                    have hEpPost := storeTcbQueueLinks_endpoint_backward _ _ tid _ _ _ endpointId ep' hObjInv1 hLinks (hEq ▸ hEp')
                    -- In st1, the endpoint at endpointId is the stored one
                    -- Identify the stored endpoint
                    have hStoreEp := storeObject_objects_eq st pair.2 endpointId _ hObjInv hStore
                    rw [hStoreEp] at hEpPost
                    cases hEpPost
                    -- Now ep' is the one stored by storeObject.
                    -- The opposite queue head is unchanged from ep, hence none.
                    cases isReceiveQ <;> simp_all
                | some tailTid =>
                  -- Non-empty queue case
                  cases hLookupTail : lookupTcb st tailTid with
                  | none => simp [hLookupTail]
                  | some tailTcb =>
                    simp only [hLookupTail]
                    cases hStore : storeObject endpointId _ st with
                    | error e => simp
                    | ok pair =>
                      simp only []
                      cases hLink1 : storeTcbQueueLinks pair.2 tailTid tailTcb.queuePrev tailTcb.queuePPrev (some tid) with
                      | error e => simp
                      | ok st2 =>
                        simp only []
                        intro hLink2
                        -- Track endpoint: storeTcbQueueLinks doesn't change endpoints
                        have hObjInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                        have hObjInv2 := storeTcbQueueLinks_preserves_objects_invExt pair.2 st2 tailTid _ _ _ hObjInv1 hLink1
                        -- Endpoint backward through both storeTcbQueueLinks
                        have hEpBack2 := storeTcbQueueLinks_endpoint_backward _ _ tid _ _ _ endpointId ep' hObjInv2 hLink2 (hEq ▸ hEp')
                        have hEpBack1 := storeTcbQueueLinks_endpoint_backward _ _ tailTid _ _ _ endpointId ep' hObjInv1 hLink1 hEpBack2
                        -- In pair.2, the endpoint is the stored one
                        have hStoreEp := storeObject_objects_eq st pair.2 endpointId _ hObjInv hStore
                        rw [hStoreEp] at hEpBack1
                        cases hEpBack1
                        -- ep' is the stored endpoint. Head of target queue = q.head (unchanged).
                        -- Opposite queue unchanged. K-2 from opposite = none.
                        cases isReceiveQ <;> simp_all
    · -- Other endpoint: frame from pre-state
      have hBack := endpointQueueEnqueue_endpoint_backward_ne endpointId isReceiveQ tid st st' oid ep' hEq hObjInv hEnqueue hEp'
      exact (hInv oid ep' hBack).2

/-- V3-K-op-2: endpointQueuePopHead preserves endpointQueueNoDup.
Uses tcbQueueLinkIntegrity to show the new head ≠ opposite queue head. -/
theorem endpointQueuePopHead_preserves_endpointQueueNoDup
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (headTcb : TCB)
    (hInv : endpointQueueNoDup st)
    (hDQSI : dualQueueSystemInvariant st)
    (hDQSI' : dualQueueSystemInvariant st')
    (hObjInv : st.objects.invExt)
    (hPop : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, headTcb, st')) :
    endpointQueueNoDup st' := by
  intro oid ep' hEp'
  constructor
  · -- K-1: no self-loops
    exact fun tid' tcb hTcb => tcbQueueChainAcyclic_no_self_loop hDQSI'.2.2 tid' tcb hTcb
  · -- K-2: head disjointness
    by_cases hEq : oid = endpointId
    · -- Target endpoint: unfold PopHead with revert pattern to track stored endpoint
      unfold endpointQueuePopHead at hPop; revert hPop
      cases hObj : st.objects[endpointId]? with
      | none => simp
      | some obj => cases obj with
        | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp
        | endpoint ep =>
          simp only []
          cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
          | none => simp
          | some headTid =>
            simp only []
            cases hLookup : lookupTcb st headTid with
            | none => simp
            | some tcb =>
              simp only []
              cases hNext : tcb.queueNext with
              | none =>
                -- Queue becomes empty: q' = { head := none, tail := none }
                simp only []
                cases hStore : storeObject endpointId _ st with
                | error e => simp
                | ok pair =>
                  dsimp only [hStore]
                  cases hClear : storeTcbQueueLinks pair.2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨rfl, _, rfl⟩
                    have hObjInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                    have hEpBack := storeTcbQueueLinks_endpoint_backward _ _ headTid _ _ _ endpointId ep' hObjInv1 hClear (hEq ▸ hEp')
                    have hStoreEp := storeObject_objects_eq st pair.2 endpointId _ hObjInv hStore
                    rw [hStoreEp] at hEpBack; cases hEpBack
                    cases isReceiveQ <;> simp_all
              | some nextTid =>
                -- Head advances: q' = { head := some nextTid, tail := q.tail }
                simp only []
                cases hStore : storeObject endpointId _ st with
                | error e => simp
                | ok pair =>
                  dsimp only [hStore]
                  cases hLookupNext : lookupTcb pair.2 nextTid with
                  | none => simp
                  | some nextTcb =>
                    dsimp only [hLookupNext]
                    cases hLinkNext : storeTcbQueueLinks pair.2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext with
                    | error e => simp
                    | ok st2 =>
                      dsimp only [hLinkNext]
                      cases hClear : storeTcbQueueLinks st2 headTid none none none with
                      | error e => simp
                      | ok st3 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨rfl, _, rfl⟩
                        have hObjInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                        have hObjInv2 := storeTcbQueueLinks_preserves_objects_invExt pair.2 st2 nextTid _ _ _ hObjInv1 hLinkNext
                        have hEpBack3 := storeTcbQueueLinks_endpoint_backward _ _ headTid _ _ _ endpointId ep' hObjInv2 hClear (hEq ▸ hEp')
                        have hEpBack2 := storeTcbQueueLinks_endpoint_backward _ _ nextTid _ _ _ endpointId ep' hObjInv1 hLinkNext hEpBack3
                        have hStoreEp := storeObject_objects_eq st pair.2 endpointId _ hObjInv hStore
                        rw [hStoreEp] at hEpBack2; cases hEpBack2
                        -- tcbQueueLinkIntegrity: nextTid.queuePrev = some headTid
                        -- intrusiveQueueWellFormed: opposite head has queuePrev = none
                        -- Contradiction if nextTid = opposite head
                        have hLinkInt := hDQSI.2.1
                        have hEpWF := hDQSI.1 endpointId ep hObj
                        unfold dualQueueEndpointWellFormed at hEpWF; rw [hObj] at hEpWF
                        have hTcbObj : st.objects[headTid.toObjId]? = some (.tcb tcb) :=
                          lookupTcb_some_objects st headTid tcb hLookup
                        have ⟨nextTcbPre, hNextObj, hNextPrev⟩ := hLinkInt.1 headTid tcb hTcbObj nextTid hNext
                        cases isReceiveQ with
                        | true =>
                          simp only [↓reduceIte] at hHead ⊢
                          -- Target = receiveQ (head → nextTid), opposite = sendQ (unchanged)
                          cases hOppHead : ep.sendQ.head with
                          | none => left; rfl
                          | some oppTid =>
                            right; right
                            have ⟨_, hOppObj, hOppPrev⟩ := hEpWF.1.2.1 oppTid hOppHead
                            intro hContra
                            have : nextTid = oppTid := by cases hContra; rfl
                            subst this
                            rw [hOppObj] at hNextObj; cases hNextObj
                            rw [hNextPrev] at hOppPrev; exact absurd hOppPrev (by simp)
                        | false =>
                          -- Target = sendQ (head → nextTid), opposite = receiveQ (unchanged)
                          -- Reduce `if false = true then ... else ...`
                          simp only [if_neg (show ¬(false = true) from by decide)] at hHead ⊢
                          cases hOppHead : ep.receiveQ.head with
                          | none => right; left; rfl
                          | some oppTid =>
                            right; right
                            have ⟨_, hOppObj, hOppPrev⟩ := hEpWF.2.2.1 oppTid hOppHead
                            intro hContra
                            have : nextTid = oppTid := by cases hContra; rfl
                            subst this
                            rw [hOppObj] at hNextObj; cases hNextObj
                            rw [hNextPrev] at hOppPrev; exact absurd hOppPrev (by simp)
    · -- Other endpoint: frame via backward transport
      have hBack := endpointQueuePopHead_endpoint_backward_ne endpointId isReceiveQ st st' tid oid ep' hEq hObjInv hPop hEp'
      exact (hInv oid ep' hBack).2

end SeLe4n.Kernel
