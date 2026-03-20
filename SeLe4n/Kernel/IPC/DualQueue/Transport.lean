/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.DualQueue.Core

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- WS-F1: Transport lemmas for endpointQueuePopHead
-- ============================================================================

/-- WS-F1: endpointQueuePopHead does not modify the scheduler. -/
theorem endpointQueuePopHead_scheduler_eq
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, _headTcb, st')) :
    st'.scheduler = st.scheduler := by
  unfold endpointQueuePopHead at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep; revert hStep
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp
      | some headTid =>
        simp only []
        cases hLookup : lookupTcb st headTid with
        | none => simp
        | some headTcb =>
          simp only []
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair => simp only []; cases hNext : headTcb.queueNext with
            | none =>
              simp only []
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, _, hEq⟩; subst hEq
                exact (storeTcbQueueLinks_scheduler_eq _ _ headTid none none none hFinal).trans
                  (storeObject_scheduler_eq _ _ endpointId _ hStore)
            | some nextTid =>
              simp only []
              cases hLookupNext : lookupTcb pair.2 nextTid with
              | none => simp
              | some nextTcb =>
                simp only []
                cases hLink : storeTcbQueueLinks pair.2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp
                | ok st2 =>
                  simp only []
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, _, hEq⟩; subst hEq
                    exact (storeTcbQueueLinks_scheduler_eq _ _ headTid none none none hFinal).trans
                      ((storeTcbQueueLinks_scheduler_eq _ _ nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext hLink).trans
                        (storeObject_scheduler_eq _ _ endpointId _ hStore))

/-- WS-F1: endpointQueuePopHead backward-preserves endpoints at oid ≠ endpointId. -/
theorem endpointQueuePopHead_endpoint_backward_ne
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hNe : oid ≠ endpointId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, _headTcb, st'))
    (hEp : st'.objects[oid]? = some (.endpoint ep)) :
    st.objects[oid]? = some (.endpoint ep) := by
  unfold endpointQueuePopHead at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint epOrig =>
      simp only [hObj] at hStep; revert hStep
      cases hHead : (if isReceiveQ then epOrig.receiveQ else epOrig.sendQ).head with
      | none => simp
      | some headTid =>
        simp only []
        cases hLookup : lookupTcb st headTid with
        | none => simp
        | some headTcb =>
          simp only []
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair => simp only []; cases hNext : headTcb.queueNext with
            | none =>
              simp only []
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, _, hEq⟩; subst hEq
                have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                have h1 := storeTcbQueueLinks_endpoint_backward _ _ headTid none none none oid ep hInv1 hFinal hEp
                rwa [storeObject_objects_ne st pair.2 endpointId oid _ hNe hObjInv hStore] at h1
            | some nextTid =>
              simp only []
              cases hLookupNext : lookupTcb pair.2 nextTid with
              | none => simp
              | some nextTcb =>
                simp only []
                cases hLink : storeTcbQueueLinks pair.2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp
                | ok st2 =>
                  simp only []
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, _, hEq⟩; subst hEq
                    have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                    have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext hInv1 hLink
                    have h3 := storeTcbQueueLinks_endpoint_backward _ _ headTid none none none oid ep hInv2 hFinal hEp
                    have h2 := storeTcbQueueLinks_endpoint_backward _ _ nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext oid ep hInv1 hLink h3
                    rwa [storeObject_objects_ne st pair.2 endpointId oid _ hNe hObjInv hStore] at h2

/-- WS-L3/L3-C: endpointQueuePopHead forward-preserves endpoints. If an endpoint
exists at oid before popHead, some endpoint still exists there after. -/
theorem endpointQueuePopHead_endpoint_forward
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (headTcb : TCB) (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, headTcb, st'))
    (hEp : st.objects[oid]? = some (.endpoint ep)) :
    ∃ ep', st'.objects[oid]? = some (.endpoint ep') := by
  unfold endpointQueuePopHead at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint epOrig =>
      simp only [hObj] at hStep; revert hStep
      cases hHead : (if isReceiveQ then epOrig.receiveQ else epOrig.sendQ).head with
      | none => simp
      | some headTid =>
        simp only []; cases hLookup : lookupTcb st headTid with
        | none => simp
        | some headTcbR =>
          simp only []
          cases headTcbR.queueNext with
          | none =>
            simp only []
            cases hStore : storeObject endpointId _ st with
            | error e => simp
            | ok pair =>
              dsimp only [hStore]; cases hLink : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, _, hEq⟩; subst hEq
                -- Endpoint at oid survives storeObject (at endpointId) then storeTcbQueueLinks (at headTid)
                have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                have hEpSt1 : ∃ ep1, pair.2.objects[oid]? = some (.endpoint ep1) := by
                  by_cases h : oid = endpointId
                  · subst h; exact ⟨_, storeObject_objects_eq' st oid _ pair hObjInv hStore⟩
                  · exact ⟨ep, by rw [storeObject_objects_ne st pair.2 endpointId oid _ h hObjInv hStore]; exact hEp⟩
                obtain ⟨ep1, hEp1⟩ := hEpSt1
                exact storeTcbQueueLinks_endpoint_forward _ _ headTid none none none oid ep1 hInv1 hLink hEp1
          | some nextTid =>
            simp only []
            cases hStore : storeObject endpointId _ st with
            | error e => simp
            | ok pair =>
              dsimp only [hStore]
              cases hLookupN : lookupTcb pair.2 nextTid with
              | none => simp
              | some nextTcb =>
                dsimp only [hLookupN]
                cases hLink1 : storeTcbQueueLinks pair.2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp
                | ok st2 =>
                  dsimp only [hLink1]
                  cases hLink2 : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, _, hEq⟩; subst hEq
                    -- Chain: storeObject → storeTcbQueueLinks (nextTid) → storeTcbQueueLinks (headTid)
                    have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                    have hEpSt1 : ∃ ep1, pair.2.objects[oid]? = some (.endpoint ep1) := by
                      by_cases h : oid = endpointId
                      · subst h; exact ⟨_, storeObject_objects_eq' st oid _ pair hObjInv hStore⟩
                      · exact ⟨ep, by rw [storeObject_objects_ne st pair.2 endpointId oid _ h hObjInv hStore]; exact hEp⟩
                    obtain ⟨ep1, hEp1⟩ := hEpSt1
                    have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid none _ nextTcb.queueNext hInv1 hLink1
                    obtain ⟨ep2, hEp2⟩ := storeTcbQueueLinks_endpoint_forward _ _ nextTid none _ nextTcb.queueNext oid ep1 hInv1 hLink1 hEp1
                    exact storeTcbQueueLinks_endpoint_forward _ _ headTid none none none oid ep2 hInv2 hLink2 hEp2

/-- WS-F1: endpointQueuePopHead backward-preserves notifications. -/
theorem endpointQueuePopHead_notification_backward
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, _headTcb, st'))
    (hNtfn : st'.objects[oid]? = some (.notification ntfn)) :
    st.objects[oid]? = some (.notification ntfn) := by
  unfold endpointQueuePopHead at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep; revert hStep
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp
      | some headTid =>
        simp only []
        cases hLookup : lookupTcb st headTid with
        | none => simp
        | some headTcb =>
          simp only []
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair => simp only []; cases hNext : headTcb.queueNext with
            | none =>
              simp only []
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, _, hEq⟩; subst hEq
                have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                have h1 := storeTcbQueueLinks_notification_backward _ _ headTid none none none oid ntfn hInv1 hFinal hNtfn
                by_cases hEqId : oid = endpointId
                · subst hEqId; rw [storeObject_objects_eq' st oid _ pair hObjInv hStore] at h1; cases h1
                · rwa [storeObject_objects_ne st pair.2 endpointId oid _ hEqId hObjInv hStore] at h1
            | some nextTid =>
              simp only []
              cases hLookupNext : lookupTcb pair.2 nextTid with
              | none => simp
              | some nextTcb =>
                simp only []
                cases hLink : storeTcbQueueLinks pair.2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp
                | ok st2 =>
                  simp only []
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, _, hEq⟩; subst hEq
                    have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                    have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext hInv1 hLink
                    have h3 := storeTcbQueueLinks_notification_backward _ _ headTid none none none oid ntfn hInv2 hFinal hNtfn
                    have h2 := storeTcbQueueLinks_notification_backward _ _ nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext oid ntfn hInv1 hLink h3
                    by_cases hEqId : oid = endpointId
                    · subst hEqId; rw [storeObject_objects_eq' st oid _ pair hObjInv hStore] at h2; cases h2
                    · rwa [storeObject_objects_ne st pair.2 endpointId oid _ hEqId hObjInv hStore] at h2

/-- WS-F1: endpointQueuePopHead forward-preserves TCB existence. If a TCB exists
at oid in the pre-state, some TCB exists at oid in the post-state. -/
theorem endpointQueuePopHead_tcb_forward
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (oid : SeLe4n.ObjId) (tcb : TCB)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, _headTcb, st'))
    (hTcb : st.objects[oid]? = some (.tcb tcb)) :
    ∃ tcb', st'.objects[oid]? = some (.tcb tcb') := by
  unfold endpointQueuePopHead at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep; revert hStep
      have hNe : oid ≠ endpointId := by intro h; subst h; rw [hTcb] at hObj; cases hObj
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp
      | some headTid =>
        simp only []
        cases hLookup : lookupTcb st headTid with
        | none => simp
        | some headTcb =>
          simp only []
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            simp only []
            have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
            have hTcb1 : pair.2.objects[oid]? = some (.tcb tcb) := by
              rw [storeObject_objects_ne st pair.2 endpointId oid _ hNe hObjInv hStore]; exact hTcb
            cases hNext : headTcb.queueNext with
            | none =>
              simp only []
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, _, hEq⟩; subst hEq
                exact storeTcbQueueLinks_tcb_forward pair.2 st3 headTid none none none oid tcb hInv1 hFinal hTcb1
            | some nextTid =>
              simp only []
              cases hLookupNext : lookupTcb pair.2 nextTid with
              | none => simp
              | some nextTcb =>
                simp only []
                cases hLink : storeTcbQueueLinks pair.2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp
                | ok st2 =>
                  simp only []
                  have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _ hInv1 hLink
                  obtain ⟨tcb2, hTcb2⟩ := storeTcbQueueLinks_tcb_forward pair.2 st2 nextTid _ _ _ oid tcb hInv1 hLink hTcb1
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, _, hEq⟩; subst hEq
                    exact storeTcbQueueLinks_tcb_forward st2 st3 headTid none none none oid tcb2 hInv2 hFinal hTcb2

/-- WS-F1: endpointQueuePopHead backward-preserves TCB ipcStates. For any TCB
in the post-state, a TCB with the same ipcState exists in the pre-state. -/
theorem endpointQueuePopHead_tcb_ipcState_backward
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (anyTid : SeLe4n.ThreadId) (tcb' : TCB)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, _headTcb, st'))
    (hTcb' : st'.objects[anyTid.toObjId]? = some (.tcb tcb')) :
    ∃ tcb, st.objects[anyTid.toObjId]? = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState := by
  unfold endpointQueuePopHead at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep; revert hStep
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp
      | some headTid =>
        simp only []
        cases hLookup : lookupTcb st headTid with
        | none => simp
        | some headTcb =>
          simp only []
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            simp only []
            cases hNext : headTcb.queueNext with
            | none =>
              simp only []
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, _, hEq⟩; subst hEq
                have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                obtain ⟨tcb1, hTcb1, hIpc1⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ headTid none none none hInv1 hFinal anyTid tcb' hTcb'
                by_cases hEqEp : anyTid.toObjId = endpointId
                · rw [hEqEp] at hTcb1; rw [storeObject_objects_eq' st endpointId _ pair hObjInv hStore] at hTcb1; cases hTcb1
                · rw [storeObject_objects_ne st pair.2 endpointId anyTid.toObjId _ hEqEp hObjInv hStore] at hTcb1
                  exact ⟨tcb1, hTcb1, hIpc1⟩
            | some nextTid =>
              simp only []
              cases hLookupNext : lookupTcb pair.2 nextTid with
              | none => simp
              | some nextTcb =>
                simp only []
                cases hLink : storeTcbQueueLinks pair.2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp
                | ok st2 =>
                  simp only []
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, _, hEq⟩; subst hEq
                    have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                    have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _ hInv1 hLink
                    obtain ⟨tcb2, hTcb2, hIpc2⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ headTid none none none hInv2 hFinal anyTid tcb' hTcb'
                    obtain ⟨tcb1, hTcb1, hIpc1⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ nextTid _ _ _ hInv1 hLink anyTid tcb2 hTcb2
                    by_cases hEqEp : anyTid.toObjId = endpointId
                    · rw [hEqEp] at hTcb1; rw [storeObject_objects_eq' st endpointId _ pair hObjInv hStore] at hTcb1; cases hTcb1
                    · rw [storeObject_objects_ne st pair.2 endpointId anyTid.toObjId _ hEqEp hObjInv hStore] at hTcb1
                      exact ⟨tcb1, hTcb1, hIpc1.trans hIpc2⟩

-- ============================================================================
-- WS-F1: Transport lemmas for endpointQueueEnqueue
-- ============================================================================

/-- WS-F1: endpointQueueEnqueue does not modify the scheduler. -/
theorem endpointQueueEnqueue_scheduler_eq
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (st st' : SystemState)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    st'.scheduler = st.scheduler := by
  unfold endpointQueueEnqueue at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hLookup : lookupTcb st tid with
      | none => simp [hLookup] at hStep
      | some tcb =>
        simp only [hLookup] at hStep
        split at hStep
        · simp at hStep
        · split at hStep
          · simp at hStep
          · revert hStep
            cases hTail : (if isReceiveQ then ep.receiveQ else ep.sendQ).tail with
            | none =>
              cases hStore : storeObject endpointId _ st with
              | error e => simp
              | ok pair =>
                simp only []
                intro hStep
                exact (storeTcbQueueLinks_scheduler_eq _ _ tid _ _ _ hStep).trans
                  (storeObject_scheduler_eq _ _ endpointId _ hStore)
            | some tailTid =>
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
                    intro hStep
                    exact (storeTcbQueueLinks_scheduler_eq _ _ tid _ _ _ hStep).trans
                      ((storeTcbQueueLinks_scheduler_eq _ _ tailTid _ _ _ hLink1).trans
                        (storeObject_scheduler_eq _ _ endpointId _ hStore))

/-- WS-F1: endpointQueueEnqueue backward-preserves endpoints at oid ≠ endpointId. -/
theorem endpointQueueEnqueue_endpoint_backward_ne
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (enqueueTid : SeLe4n.ThreadId) (st st' : SystemState)
    (oid : SeLe4n.ObjId) (ep : Endpoint) (hNe : oid ≠ endpointId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ enqueueTid st = .ok st')
    (hEp : st'.objects[oid]? = some (.endpoint ep)) :
    st.objects[oid]? = some (.endpoint ep) := by
  unfold endpointQueueEnqueue at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint epOrig =>
      simp only [hObj] at hStep
      cases hLookup : lookupTcb st enqueueTid with
      | none => simp [hLookup] at hStep
      | some tcb =>
        simp only [hLookup] at hStep
        split at hStep
        · simp at hStep
        · split at hStep
          · simp at hStep
          · revert hStep
            cases hTail : (if isReceiveQ then epOrig.receiveQ else epOrig.sendQ).tail with
            | none =>
              cases hStore : storeObject endpointId _ st with
              | error e => simp
              | ok pair =>
                simp only []
                intro hStep
                have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                have h1 := storeTcbQueueLinks_endpoint_backward _ _ enqueueTid _ _ _ oid ep hInv1 hStep hEp
                rwa [storeObject_objects_ne st pair.2 endpointId oid _ hNe hObjInv hStore] at h1
            | some tailTid =>
              cases hLookupTail : lookupTcb st tailTid with
              | none => simp [hLookupTail]
              | some tailTcb =>
                simp only [hLookupTail]
                cases hStore : storeObject endpointId _ st with
                | error e => simp
                | ok pair =>
                  simp only []
                  cases hLink1 : storeTcbQueueLinks pair.2 tailTid tailTcb.queuePrev tailTcb.queuePPrev (some enqueueTid) with
                  | error e => simp
                  | ok st2 =>
                    simp only []
                    intro hStep
                    have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                    have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ tailTid _ _ _ hInv1 hLink1
                    have h3 := storeTcbQueueLinks_endpoint_backward _ _ enqueueTid _ _ _ oid ep hInv2 hStep hEp
                    have h2 := storeTcbQueueLinks_endpoint_backward _ _ tailTid _ _ _ oid ep hInv1 hLink1 h3
                    rwa [storeObject_objects_ne st pair.2 endpointId oid _ hNe hObjInv hStore] at h2

/-- WS-L3/L3-C: endpointQueueEnqueue forward-preserves endpoints. -/
theorem endpointQueueEnqueue_endpoint_forward
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (enqueueTid : SeLe4n.ThreadId) (st st' : SystemState)
    (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ enqueueTid st = .ok st')
    (hEp : st.objects[oid]? = some (.endpoint ep)) :
    ∃ ep', st'.objects[oid]? = some (.endpoint ep') := by
  unfold endpointQueueEnqueue at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint epOrig =>
      simp only [hObj] at hStep; revert hStep
      cases hLookup : lookupTcb st enqueueTid with
      | none => simp
      | some tcb =>
        simp only []
        -- The function checks ipcState = .ready and queue fields; split on the if branches
        split
        · simp -- ipcState ≠ .ready → error
        · split
          · simp -- queue links present → error
          ·
            cases (if isReceiveQ then epOrig.receiveQ else epOrig.sendQ).tail with
            | none =>
              simp only []
              cases hStore : storeObject endpointId _ st with
              | error e => simp
              | ok pair =>
                simp only []; intro hLink
                have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                have hEpSt1 : ∃ ep1, pair.2.objects[oid]? = some (.endpoint ep1) := by
                  by_cases h : oid = endpointId
                  · subst h; exact ⟨_, storeObject_objects_eq' st oid _ pair hObjInv hStore⟩
                  · exact ⟨ep, by rw [storeObject_objects_ne st pair.2 endpointId oid _ h hObjInv hStore]; exact hEp⟩
                obtain ⟨ep1, hEp1⟩ := hEpSt1
                exact storeTcbQueueLinks_endpoint_forward _ _ enqueueTid none _ none oid ep1 hInv1 hLink hEp1
            | some tailTid =>
              simp only []
              cases hLookupT : lookupTcb st tailTid with
              | none => simp
              | some tailTcb =>
                simp only []
                cases hStore : storeObject endpointId _ st with
                | error e => simp
                | ok pair =>
                  simp only []
                  cases hLink1 : storeTcbQueueLinks pair.2 tailTid _ _ (some enqueueTid) with
                  | error e => simp
                  | ok st2 =>
                    simp only []; intro hLink2
                    have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                    have hEpSt1 : ∃ ep1, pair.2.objects[oid]? = some (.endpoint ep1) := by
                      by_cases h : oid = endpointId
                      · subst h; exact ⟨_, storeObject_objects_eq' st oid _ pair hObjInv hStore⟩
                      · exact ⟨ep, by rw [storeObject_objects_ne st pair.2 endpointId oid _ h hObjInv hStore]; exact hEp⟩
                    obtain ⟨ep1, hEp1⟩ := hEpSt1
                    have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ tailTid _ _ _ hInv1 hLink1
                    obtain ⟨ep2, hEp2⟩ := storeTcbQueueLinks_endpoint_forward _ _ tailTid _ _ _ oid ep1 hInv1 hLink1 hEp1
                    exact storeTcbQueueLinks_endpoint_forward _ _ enqueueTid _ _ none oid ep2 hInv2 hLink2 hEp2

/-- WS-F1: endpointQueueEnqueue backward-preserves notifications. -/
theorem endpointQueueEnqueue_notification_backward
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (enqueueTid : SeLe4n.ThreadId) (st st' : SystemState)
    (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ enqueueTid st = .ok st')
    (hNtfn : st'.objects[oid]? = some (.notification ntfn)) :
    st.objects[oid]? = some (.notification ntfn) := by
  unfold endpointQueueEnqueue at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hLookup : lookupTcb st enqueueTid with
      | none => simp [hLookup] at hStep
      | some tcb =>
        simp only [hLookup] at hStep
        split at hStep
        · simp at hStep
        · split at hStep
          · simp at hStep
          · revert hStep
            cases hTail : (if isReceiveQ then ep.receiveQ else ep.sendQ).tail with
            | none =>
              cases hStore : storeObject endpointId _ st with
              | error e => simp
              | ok pair =>
                simp only []
                intro hStep
                have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                have h1 := storeTcbQueueLinks_notification_backward _ _ enqueueTid _ _ _ oid ntfn hInv1 hStep hNtfn
                by_cases hEqId : oid = endpointId
                · subst hEqId; rw [storeObject_objects_eq' st oid _ pair hObjInv hStore] at h1; cases h1
                · rwa [storeObject_objects_ne st pair.2 endpointId oid _ hEqId hObjInv hStore] at h1
            | some tailTid =>
              cases hLookupTail : lookupTcb st tailTid with
              | none => simp [hLookupTail]
              | some tailTcb =>
                simp only [hLookupTail]
                cases hStore : storeObject endpointId _ st with
                | error e => simp
                | ok pair =>
                  simp only []
                  cases hLink1 : storeTcbQueueLinks pair.2 tailTid tailTcb.queuePrev tailTcb.queuePPrev (some enqueueTid) with
                  | error e => simp
                  | ok st2 =>
                    simp only []
                    intro hStep
                    have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                    have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ tailTid _ _ _ hInv1 hLink1
                    have h3 := storeTcbQueueLinks_notification_backward _ _ enqueueTid _ _ _ oid ntfn hInv2 hStep hNtfn
                    have h2 := storeTcbQueueLinks_notification_backward _ _ tailTid _ _ _ oid ntfn hInv1 hLink1 h3
                    by_cases hEqId : oid = endpointId
                    · subst hEqId; rw [storeObject_objects_eq' st oid _ pair hObjInv hStore] at h2; cases h2
                    · rwa [storeObject_objects_ne st pair.2 endpointId oid _ hEqId hObjInv hStore] at h2

/-- WS-F1: endpointQueueEnqueue forward-preserves TCB existence. -/
theorem endpointQueueEnqueue_tcb_forward
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (enqueueTid : SeLe4n.ThreadId) (st st' : SystemState)
    (oid : SeLe4n.ObjId) (tcb : TCB)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ enqueueTid st = .ok st')
    (hTcb : st.objects[oid]? = some (.tcb tcb)) :
    ∃ tcb', st'.objects[oid]? = some (.tcb tcb') := by
  unfold endpointQueueEnqueue at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      have hNe : oid ≠ endpointId := by intro h; subst h; rw [hTcb] at hObj; cases hObj
      cases hLookup : lookupTcb st enqueueTid with
      | none => simp [hLookup] at hStep
      | some tcbE =>
        simp only [hLookup] at hStep
        split at hStep
        · simp at hStep
        · split at hStep
          · simp at hStep
          · revert hStep
            cases hTail : (if isReceiveQ then ep.receiveQ else ep.sendQ).tail with
            | none =>
              cases hStore : storeObject endpointId _ st with
              | error e => simp
              | ok pair =>
                simp only []; intro hStep
                have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                have hTcb1 : pair.2.objects[oid]? = some (.tcb tcb) := by
                  rw [storeObject_objects_ne st pair.2 endpointId oid _ hNe hObjInv hStore]; exact hTcb
                exact storeTcbQueueLinks_tcb_forward pair.2 st' enqueueTid _ _ _ oid tcb hInv1 hStep hTcb1
            | some tailTid =>
              cases hLookupTail : lookupTcb st tailTid with
              | none => simp [hLookupTail]
              | some tailTcb =>
                simp only [hLookupTail]
                cases hStore : storeObject endpointId _ st with
                | error e => simp
                | ok pair =>
                  simp only []
                  have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                  have hTcb1 : pair.2.objects[oid]? = some (.tcb tcb) := by
                    rw [storeObject_objects_ne st pair.2 endpointId oid _ hNe hObjInv hStore]; exact hTcb
                  cases hLink1 : storeTcbQueueLinks pair.2 tailTid tailTcb.queuePrev tailTcb.queuePPrev (some enqueueTid) with
                  | error e => simp
                  | ok st2 =>
                    simp only []; intro hStep
                    have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ tailTid _ _ _ hInv1 hLink1
                    obtain ⟨tcb2, hTcb2⟩ := storeTcbQueueLinks_tcb_forward pair.2 st2 tailTid _ _ _ oid tcb hInv1 hLink1 hTcb1
                    exact storeTcbQueueLinks_tcb_forward st2 st' enqueueTid _ _ _ oid tcb2 hInv2 hStep hTcb2

/-- WS-F1: endpointQueueEnqueue backward-preserves TCB ipcStates. -/
theorem endpointQueueEnqueue_tcb_ipcState_backward
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (enqueueTid : SeLe4n.ThreadId) (st st' : SystemState)
    (anyTid : SeLe4n.ThreadId) (tcb' : TCB)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ enqueueTid st = .ok st')
    (hTcb' : st'.objects[anyTid.toObjId]? = some (.tcb tcb')) :
    ∃ tcb, st.objects[anyTid.toObjId]? = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState := by
  unfold endpointQueueEnqueue at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hLookup : lookupTcb st enqueueTid with
      | none => simp [hLookup] at hStep
      | some tcbE =>
        simp only [hLookup] at hStep
        split at hStep
        · simp at hStep
        · split at hStep
          · simp at hStep
          · revert hStep
            cases hTail : (if isReceiveQ then ep.receiveQ else ep.sendQ).tail with
            | none =>
              cases hStore : storeObject endpointId _ st with
              | error e => simp
              | ok pair =>
                simp only []; intro hStep
                have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                obtain ⟨tcb1, hTcb1, hIpc1⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ enqueueTid _ _ _ hInv1 hStep anyTid tcb' hTcb'
                by_cases hEqEp : anyTid.toObjId = endpointId
                · rw [hEqEp] at hTcb1; rw [storeObject_objects_eq' st endpointId _ pair hObjInv hStore] at hTcb1; cases hTcb1
                · rw [storeObject_objects_ne st pair.2 endpointId anyTid.toObjId _ hEqEp hObjInv hStore] at hTcb1
                  exact ⟨tcb1, hTcb1, hIpc1⟩
            | some tailTid =>
              cases hLookupTail : lookupTcb st tailTid with
              | none => simp [hLookupTail]
              | some tailTcb =>
                simp only [hLookupTail]
                cases hStore : storeObject endpointId _ st with
                | error e => simp
                | ok pair =>
                  simp only []
                  cases hLink1 : storeTcbQueueLinks pair.2 tailTid tailTcb.queuePrev tailTcb.queuePPrev (some enqueueTid) with
                  | error e => simp
                  | ok st2 =>
                    simp only []; intro hStep
                    have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                    have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ tailTid _ _ _ hInv1 hLink1
                    obtain ⟨tcb3, hTcb3, hIpc3⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ enqueueTid _ _ _ hInv2 hStep anyTid tcb' hTcb'
                    obtain ⟨tcb2, hTcb2, hIpc2⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ tailTid _ _ _ hInv1 hLink1 anyTid tcb3 hTcb3
                    by_cases hEqEp : anyTid.toObjId = endpointId
                    · rw [hEqEp] at hTcb2; rw [storeObject_objects_eq' st endpointId _ pair hObjInv hStore] at hTcb2; cases hTcb2
                    · rw [storeObject_objects_ne st pair.2 endpointId anyTid.toObjId _ hEqEp hObjInv hStore] at hTcb2
                      exact ⟨tcb2, hTcb2, hIpc2.trans hIpc3⟩

/-- WS-E8/M-02: Remove an arbitrary waiter from an intrusive endpoint queue in O(1).

Uses per-node `queuePPrev` metadata (pointer-to-previous-link) so unlinking
requires no queue traversal. -/
def endpointQueueRemoveDual
    (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) : Kernel Unit :=
  fun st =>
    match st.objects[endpointId]? with
    | some (.endpoint ep) =>
        let q := if isReceiveQ then ep.receiveQ else ep.sendQ
        match lookupTcb st tid with
        | none => .error .objectNotFound
        | some tcb =>
            match tcb.queuePPrev with
            | none => .error .endpointQueueEmpty
            | some pprev =>
                if q.head.isNone || q.tail.isNone then
                  .error .illegalState
                else
                  let pprevConsistent : Bool :=
                    match pprev with
                    | .endpointHead => q.head = some tid && tcb.queuePrev.isNone
                    | .tcbNext prevTid => q.head ≠ some tid && tcb.queuePrev = some prevTid
                  if !pprevConsistent then
                    .error .illegalState
                  else
                    let applyPrev : Except KernelError SystemState :=
                      match pprev with
                      | .endpointHead =>
                          let q' : IntrusiveQueue := { head := tcb.queueNext, tail := q.tail }
                          let ep' : Endpoint := if isReceiveQ then { ep with receiveQ := q' } else { ep with sendQ := q' }
                          match storeObject endpointId (.endpoint ep') st with
                          | .error e => .error e
                          | .ok ((), st1) => .ok st1
                      | .tcbNext prevTid =>
                          match lookupTcb st prevTid with
                          | none => .error .objectNotFound
                          | some prevTcb =>
                              if prevTcb.queueNext ≠ some tid then
                                .error .illegalState
                              else
                                match storeTcbQueueLinks st prevTid prevTcb.queuePrev prevTcb.queuePPrev tcb.queueNext with
                                | .error e => .error e
                                | .ok st1 => .ok st1
                    match applyPrev with
                  | .error e => .error e
                  | .ok st1 =>
                      let newTail : Option SeLe4n.ThreadId :=
                        match tcb.queueNext with
                        | some _ => q.tail
                        | none =>
                            match pprev with
                            | .endpointHead => none
                            | .tcbNext prevTid => some prevTid
                      let st2Result : Except KernelError SystemState :=
                        match tcb.queueNext with
                        | none => .ok st1
                        | some nextTid =>
                            match lookupTcb st1 nextTid with
                            | none => .error .objectNotFound
                            | some nextTcb => storeTcbQueueLinks st1 nextTid (tcb.queuePrev) (some pprev) nextTcb.queueNext
                      match st2Result with
                      | .error e => .error e
                      | .ok st2 =>
                          let q' : IntrusiveQueue :=
                            if q.head = some tid then
                              { head := tcb.queueNext, tail := newTail }
                            else
                              { head := q.head, tail := newTail }
                          let ep' : Endpoint := if isReceiveQ then { ep with receiveQ := q' } else { ep with sendQ := q' }
                          match storeObject endpointId (.endpoint ep') st2 with
                          | .error e => .error e
                          | .ok ((), st3) =>
                              match storeTcbQueueLinks st3 tid none none none with
                              | .error e => .error e
                              | .ok st4 => .ok ((), st4)
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

/-- WS-F1: endpointQueueRemoveDual does not modify the scheduler.
The function only calls storeObject and storeTcbQueueLinks, both of which
preserve the scheduler. -/
theorem endpointQueueRemoveDual_scheduler_eq
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  unfold endpointQueueRemoveDual at hStep; revert hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp
    | endpoint ep =>
      simp only []
      cases hLookup : lookupTcb st tid with
      | none => simp
      | some tcb =>
        simp only []
        cases hPPrev : tcb.queuePPrev with
        | none => simp
        | some pprev =>
          simp only []
          generalize (if isReceiveQ then ep.receiveQ else ep.sendQ) = q
          split
          · simp
          · cases pprev with
            | endpointHead =>
              simp only []
              split
              · simp
              · cases hStore1 : storeObject endpointId _ st with
                | error e => simp
                | ok pair1 =>
                simp only []; cases hNext : tcb.queueNext with
                | none =>
                  simp only []
                  cases hStore2 : storeObject endpointId _ pair1.2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only []; cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    exact (storeTcbQueueLinks_scheduler_eq _ _ tid _ _ _ hFinal).trans
                      ((storeObject_scheduler_eq _ _ endpointId _ hStore2).trans
                        (storeObject_scheduler_eq _ _ endpointId _ hStore1))
                | some nextTid =>
                  simp only []
                  cases hLookupN : lookupTcb pair1.2 nextTid with
                  | none => simp
                  | some nextTcb =>
                  simp only []; cases hLink : storeTcbQueueLinks pair1.2 nextTid _ _ nextTcb.queueNext with
                  | error e => simp
                  | ok st2 =>
                  simp only []; cases hStore2 : storeObject endpointId _ st2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only []; cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    exact (storeTcbQueueLinks_scheduler_eq _ _ tid _ _ _ hFinal).trans
                      ((storeObject_scheduler_eq _ _ endpointId _ hStore2).trans
                        ((storeTcbQueueLinks_scheduler_eq _ _ nextTid _ _ _ hLink).trans
                          (storeObject_scheduler_eq _ _ endpointId _ hStore1)))
            | tcbNext prevTid =>
              dsimp only
              split
              · simp
              · cases hLookupP : lookupTcb st prevTid with
                | none => simp
                | some prevTcb =>
                dsimp only [hLookupP]; split
                · simp
                · -- split introduced heq✝ : (if ... then .error else match storeTcbQueueLinks ... with ...) = .ok st''✝
                  -- and the goal uses st''✝. Resolve heq✝ to extract the actual state.
                  rename_i _ _ _ stAp heqAp
                  split at heqAp
                  · simp at heqAp
                  · cases hLink0 : storeTcbQueueLinks st prevTid prevTcb.queuePrev prevTcb.queuePPrev tcb.queueNext with
                    | error e => simp [hLink0] at heqAp
                    | ok stPrev =>
                    simp [hLink0] at heqAp; subst heqAp
                    -- Now stAp = stPrev, goal uses stPrev
                    cases hNext : tcb.queueNext with
                    | none =>
                      dsimp only [hNext]
                      cases hStore2 : storeObject endpointId _ stPrev with
                      | error e => simp
                      | ok pair2 =>
                      dsimp only [hStore2]; cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                      | error e => simp
                      | ok st4 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        exact (storeTcbQueueLinks_scheduler_eq _ _ tid _ _ _ hFinal).trans
                          ((storeObject_scheduler_eq _ _ endpointId _ hStore2).trans
                            (storeTcbQueueLinks_scheduler_eq _ _ prevTid _ _ _ hLink0))
                    | some nextTid =>
                      dsimp only [hNext]
                      cases hLookupN : lookupTcb stPrev nextTid with
                      | none => simp
                      | some nextTcb =>
                      dsimp only [hLookupN]; cases hLink1 : storeTcbQueueLinks stPrev nextTid _ _ nextTcb.queueNext with
                      | error e => simp
                      | ok st2 =>
                      dsimp only [hLink1]; cases hStore2 : storeObject endpointId _ st2 with
                      | error e => simp
                      | ok pair2 =>
                      dsimp only [hStore2]; cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                      | error e => simp
                      | ok st4 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        exact (storeTcbQueueLinks_scheduler_eq _ _ tid _ _ _ hFinal).trans
                          ((storeObject_scheduler_eq _ _ endpointId _ hStore2).trans
                            ((storeTcbQueueLinks_scheduler_eq _ _ nextTid _ _ _ hLink1).trans
                              (storeTcbQueueLinks_scheduler_eq _ _ prevTid _ _ _ hLink0)))


/-- WS-F1: Forward TCB transport for endpointQueueRemoveDual.
If a TCB exists at `oid` before the operation, a TCB still exists at `oid` after.
Queue link fields may change but the object remains a TCB. -/
theorem endpointQueueRemoveDual_tcb_forward
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isSendQ : Bool) (tid : SeLe4n.ThreadId) (oid : SeLe4n.ObjId) (tcb : TCB)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isSendQ tid st = .ok ((), st'))
    (hTcb : st.objects[oid]? = some (.tcb tcb)) :
    ∃ tcb', st'.objects[oid]? = some (.tcb tcb') := by
  unfold endpointQueueRemoveDual at hStep; revert hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp
    | endpoint ep =>
      simp only []
      have hNe : oid ≠ endpointId := by intro h; subst h; rw [hTcb] at hObj; cases hObj
      cases hLookup : lookupTcb st tid with
      | none => simp
      | some tcbTid =>
        simp only []
        cases hPPrev : tcbTid.queuePPrev with
        | none => simp
        | some pprev =>
          simp only []
          generalize (if isSendQ then ep.receiveQ else ep.sendQ) = q
          split
          · simp
          · cases pprev with
            | endpointHead =>
              simp only []
              split
              · simp
              · cases hStore1 : storeObject endpointId _ st with
                | error e => simp
                | ok pair1 =>
                simp only []
                have hInvS1 := storeObject_preserves_objects_invExt' st endpointId _ pair1 hObjInv hStore1
                have hTcb1 : pair1.2.objects[oid]? = some (.tcb tcb) := by
                  rw [storeObject_objects_ne st pair1.2 endpointId oid _ hNe hObjInv hStore1]; exact hTcb
                cases hNext : tcbTid.queueNext with
                | none =>
                  simp only []
                  cases hStore2 : storeObject endpointId _ pair1.2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only []
                  have hInvS2 := storeObject_preserves_objects_invExt' pair1.2 endpointId _ pair2 hInvS1 hStore2
                  have hTcb2 : pair2.2.objects[oid]? = some (.tcb tcb) := by
                    rw [storeObject_objects_ne pair1.2 pair2.2 endpointId oid _ hNe hInvS1 hStore2]; exact hTcb1
                  cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    exact storeTcbQueueLinks_tcb_forward pair2.2 st4 tid none none none oid tcb hInvS2 hFinal hTcb2
                | some nextTid =>
                  simp only []
                  cases hLookupN : lookupTcb pair1.2 nextTid with
                  | none => simp
                  | some nextTcb =>
                  simp only []; cases hLink : storeTcbQueueLinks pair1.2 nextTid _ _ nextTcb.queueNext with
                  | error e => simp
                  | ok st2 =>
                  simp only []
                  have hInvL := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _ hInvS1 hLink
                  obtain ⟨tcb2, hTcb2⟩ := storeTcbQueueLinks_tcb_forward pair1.2 st2 nextTid _ _ _ oid tcb hInvS1 hLink hTcb1
                  cases hStore2 : storeObject endpointId _ st2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only []
                  have hInvS2 := storeObject_preserves_objects_invExt' st2 endpointId _ pair2 hInvL hStore2
                  have hTcb3 : pair2.2.objects[oid]? = some (.tcb tcb2) := by
                    rw [storeObject_objects_ne st2 pair2.2 endpointId oid _ hNe hInvL hStore2]; exact hTcb2
                  cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    exact storeTcbQueueLinks_tcb_forward pair2.2 st4 tid none none none oid tcb2 hInvS2 hFinal hTcb3
            | tcbNext prevTid =>
              dsimp only
              split
              · simp
              · cases hLookupP : lookupTcb st prevTid with
                | none => simp
                | some prevTcb =>
                dsimp only [hLookupP]; split
                · simp
                · rename_i _ _ _ stAp heqAp
                  split at heqAp
                  · simp at heqAp
                  · cases hLink0 : storeTcbQueueLinks st prevTid prevTcb.queuePrev prevTcb.queuePPrev tcbTid.queueNext with
                    | error e => simp [hLink0] at heqAp
                    | ok stPrev =>
                    simp [hLink0] at heqAp; subst heqAp
                    have hInvP := storeTcbQueueLinks_preserves_objects_invExt _ _ prevTid _ _ _ hObjInv hLink0
                    obtain ⟨tcb0, hTcb0⟩ := storeTcbQueueLinks_tcb_forward st stPrev prevTid _ _ _ oid tcb hObjInv hLink0 hTcb
                    cases hNext : tcbTid.queueNext with
                    | none =>
                      dsimp only [hNext]
                      cases hStore2 : storeObject endpointId _ stPrev with
                      | error e => simp
                      | ok pair2 =>
                      dsimp only [hStore2]
                      have hInvS2 := storeObject_preserves_objects_invExt' stPrev endpointId _ pair2 hInvP hStore2
                      have hTcb1 : pair2.2.objects[oid]? = some (.tcb tcb0) := by
                        rw [storeObject_objects_ne stPrev pair2.2 endpointId oid _ hNe hInvP hStore2]; exact hTcb0
                      cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                      | error e => simp
                      | ok st4 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        exact storeTcbQueueLinks_tcb_forward pair2.2 st4 tid none none none oid tcb0 hInvS2 hFinal hTcb1
                    | some nextTid =>
                      dsimp only [hNext]
                      cases hLookupN : lookupTcb stPrev nextTid with
                      | none => simp
                      | some nextTcb =>
                      dsimp only [hLookupN]; cases hLink1 : storeTcbQueueLinks stPrev nextTid _ _ nextTcb.queueNext with
                      | error e => simp
                      | ok st2 =>
                      dsimp only [hLink1]
                      have hInvL1 := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _ hInvP hLink1
                      obtain ⟨tcb1, hTcb1⟩ := storeTcbQueueLinks_tcb_forward stPrev st2 nextTid _ _ _ oid tcb0 hInvP hLink1 hTcb0
                      cases hStore2 : storeObject endpointId _ st2 with
                      | error e => simp
                      | ok pair2 =>
                      dsimp only [hStore2]
                      have hInvS2 := storeObject_preserves_objects_invExt' st2 endpointId _ pair2 hInvL1 hStore2
                      have hTcb2 : pair2.2.objects[oid]? = some (.tcb tcb1) := by
                        rw [storeObject_objects_ne st2 pair2.2 endpointId oid _ hNe hInvL1 hStore2]; exact hTcb1
                      cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                      | error e => simp
                      | ok st4 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        exact storeTcbQueueLinks_tcb_forward pair2.2 st4 tid none none none oid tcb1 hInvS2 hFinal hTcb2

/-- WS-F1: Backward endpoint transport for endpointQueueRemoveDual (non-target endpoint).
If an endpoint exists at `oid ≠ endpointId` in the post-state, it existed unchanged in the pre-state. -/
theorem endpointQueueRemoveDual_endpoint_backward_ne
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId) (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hNe : oid ≠ endpointId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hEp : st'.objects[oid]? = some (.endpoint ep)) :
    st.objects[oid]? = some (.endpoint ep) := by
  unfold endpointQueueRemoveDual at hStep; revert hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp
    | endpoint epOrig =>
      simp only []
      cases hLookup : lookupTcb st tid with
      | none => simp
      | some tcbTid =>
        simp only []
        cases hPPrev : tcbTid.queuePPrev with
        | none => simp
        | some pprev =>
          simp only []
          generalize (if isReceiveQ then epOrig.receiveQ else epOrig.sendQ) = q
          split
          · simp
          · cases pprev with
            | endpointHead =>
              simp only []
              split
              · simp
              · cases hStore1 : storeObject endpointId _ st with
                | error e => simp
                | ok pair1 =>
                simp only []
                have hInvS1 := storeObject_preserves_objects_invExt' st endpointId _ pair1 hObjInv hStore1
                cases hNext : tcbTid.queueNext with
                | none =>
                  simp only []
                  cases hStore2 : storeObject endpointId _ pair1.2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only []
                  have hInvS2 := storeObject_preserves_objects_invExt' pair1.2 endpointId _ pair2 hInvS1 hStore2
                  cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    have h1 := storeTcbQueueLinks_endpoint_backward _ _ tid none none none oid ep hInvS2 hFinal hEp
                    rw [storeObject_objects_ne pair1.2 pair2.2 endpointId oid _ hNe hInvS1 hStore2] at h1
                    rwa [storeObject_objects_ne st pair1.2 endpointId oid _ hNe hObjInv hStore1] at h1
                | some nextTid =>
                  simp only []
                  cases hLookupN : lookupTcb pair1.2 nextTid with
                  | none => simp
                  | some nextTcb =>
                  simp only []; cases hLink : storeTcbQueueLinks pair1.2 nextTid _ _ nextTcb.queueNext with
                  | error e => simp
                  | ok st2 =>
                  simp only []
                  have hInvL := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _ hInvS1 hLink
                  cases hStore2 : storeObject endpointId _ st2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only []
                  have hInvS2 := storeObject_preserves_objects_invExt' st2 endpointId _ pair2 hInvL hStore2
                  cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    have h1 := storeTcbQueueLinks_endpoint_backward _ _ tid none none none oid ep hInvS2 hFinal hEp
                    rw [storeObject_objects_ne st2 pair2.2 endpointId oid _ hNe hInvL hStore2] at h1
                    have h2 := storeTcbQueueLinks_endpoint_backward _ _ nextTid _ _ _ oid ep hInvS1 hLink h1
                    rwa [storeObject_objects_ne st pair1.2 endpointId oid _ hNe hObjInv hStore1] at h2
            | tcbNext prevTid =>
              dsimp only
              split
              · simp
              · cases hLookupP : lookupTcb st prevTid with
                | none => simp
                | some prevTcb =>
                dsimp only [hLookupP]; split
                · simp
                · rename_i _ _ _ stAp heqAp
                  split at heqAp
                  · simp at heqAp
                  · cases hLink0 : storeTcbQueueLinks st prevTid prevTcb.queuePrev prevTcb.queuePPrev tcbTid.queueNext with
                    | error e => simp [hLink0] at heqAp
                    | ok stPrev =>
                    simp [hLink0] at heqAp; subst heqAp
                    have hInvP := storeTcbQueueLinks_preserves_objects_invExt _ _ prevTid _ _ _ hObjInv hLink0
                    cases hNext : tcbTid.queueNext with
                    | none =>
                      dsimp only [hNext]
                      cases hStore2 : storeObject endpointId _ stPrev with
                      | error e => simp
                      | ok pair2 =>
                      dsimp only [hStore2]
                      have hInvS2 := storeObject_preserves_objects_invExt' stPrev endpointId _ pair2 hInvP hStore2
                      cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                      | error e => simp
                      | ok st4 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        have h1 := storeTcbQueueLinks_endpoint_backward _ _ tid none none none oid ep hInvS2 hFinal hEp
                        rw [storeObject_objects_ne stPrev pair2.2 endpointId oid _ hNe hInvP hStore2] at h1
                        exact storeTcbQueueLinks_endpoint_backward _ _ prevTid _ _ _ oid ep hObjInv hLink0 h1
                    | some nextTid =>
                      dsimp only [hNext]
                      cases hLookupN : lookupTcb stPrev nextTid with
                      | none => simp
                      | some nextTcb =>
                      dsimp only [hLookupN]; cases hLink1 : storeTcbQueueLinks stPrev nextTid _ _ nextTcb.queueNext with
                      | error e => simp
                      | ok st2 =>
                      dsimp only [hLink1]
                      have hInvL1 := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _ hInvP hLink1
                      cases hStore2 : storeObject endpointId _ st2 with
                      | error e => simp
                      | ok pair2 =>
                      dsimp only [hStore2]
                      have hInvS2 := storeObject_preserves_objects_invExt' st2 endpointId _ pair2 hInvL1 hStore2
                      cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                      | error e => simp
                      | ok st4 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        have h1 := storeTcbQueueLinks_endpoint_backward _ _ tid none none none oid ep hInvS2 hFinal hEp
                        rw [storeObject_objects_ne st2 pair2.2 endpointId oid _ hNe hInvL1 hStore2] at h1
                        have h2 := storeTcbQueueLinks_endpoint_backward _ _ nextTid _ _ _ oid ep hInvP hLink1 h1
                        exact storeTcbQueueLinks_endpoint_backward _ _ prevTid _ _ _ oid ep hObjInv hLink0 h2

/-- WS-F1: Backward notification transport for endpointQueueRemoveDual.
If a notification exists at `oid` in the post-state, it existed unchanged in the pre-state. -/
theorem endpointQueueRemoveDual_notification_backward
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId) (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hNtfn : st'.objects[oid]? = some (.notification ntfn)) :
    st.objects[oid]? = some (.notification ntfn) := by
  unfold endpointQueueRemoveDual at hStep; revert hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp
    | endpoint epOrig =>
      simp only []
      cases hLookup : lookupTcb st tid with
      | none => simp
      | some tcbTid =>
        simp only []
        cases hPPrev : tcbTid.queuePPrev with
        | none => simp
        | some pprev =>
          simp only []
          generalize (if isReceiveQ then epOrig.receiveQ else epOrig.sendQ) = q
          split
          · simp
          · cases pprev with
            | endpointHead =>
              simp only []
              split
              · simp
              · cases hStore1 : storeObject endpointId _ st with
                | error e => simp
                | ok pair1 =>
                simp only []
                have hInvS1 := storeObject_preserves_objects_invExt' st endpointId _ pair1 hObjInv hStore1
                cases hNext : tcbTid.queueNext with
                | none =>
                  simp only []
                  cases hStore2 : storeObject endpointId _ pair1.2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only []
                  have hInvS2 := storeObject_preserves_objects_invExt' pair1.2 endpointId _ pair2 hInvS1 hStore2
                  cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    have h1 := storeTcbQueueLinks_notification_backward _ _ tid none none none oid ntfn hInvS2 hFinal hNtfn
                    by_cases hEqId : oid = endpointId
                    · subst hEqId; rw [storeObject_objects_eq' pair1.2 oid _ pair2 hInvS1 hStore2] at h1; cases h1
                    · rw [storeObject_objects_ne pair1.2 pair2.2 endpointId oid _ hEqId hInvS1 hStore2] at h1
                      rwa [storeObject_objects_ne st pair1.2 endpointId oid _ hEqId hObjInv hStore1] at h1
                | some nextTid =>
                  simp only []
                  cases hLookupN : lookupTcb pair1.2 nextTid with
                  | none => simp
                  | some nextTcb =>
                  simp only []; cases hLink : storeTcbQueueLinks pair1.2 nextTid _ _ nextTcb.queueNext with
                  | error e => simp
                  | ok st2 =>
                  simp only []
                  have hInvL := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _ hInvS1 hLink
                  cases hStore2 : storeObject endpointId _ st2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only []
                  have hInvS2 := storeObject_preserves_objects_invExt' st2 endpointId _ pair2 hInvL hStore2
                  cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    have h1 := storeTcbQueueLinks_notification_backward _ _ tid none none none oid ntfn hInvS2 hFinal hNtfn
                    by_cases hEqId : oid = endpointId
                    · subst hEqId; rw [storeObject_objects_eq' st2 oid _ pair2 hInvL hStore2] at h1; cases h1
                    · rw [storeObject_objects_ne st2 pair2.2 endpointId oid _ hEqId hInvL hStore2] at h1
                      have h2 := storeTcbQueueLinks_notification_backward _ _ nextTid _ _ _ oid ntfn hInvS1 hLink h1
                      rwa [storeObject_objects_ne st pair1.2 endpointId oid _ hEqId hObjInv hStore1] at h2
            | tcbNext prevTid =>
              dsimp only
              split
              · simp
              · cases hLookupP : lookupTcb st prevTid with
                | none => simp
                | some prevTcb =>
                dsimp only [hLookupP]; split
                · simp
                · rename_i _ _ _ stAp heqAp
                  split at heqAp
                  · simp at heqAp
                  · cases hLink0 : storeTcbQueueLinks st prevTid prevTcb.queuePrev prevTcb.queuePPrev tcbTid.queueNext with
                    | error e => simp [hLink0] at heqAp
                    | ok stPrev =>
                    simp [hLink0] at heqAp; subst heqAp
                    have hInvP := storeTcbQueueLinks_preserves_objects_invExt _ _ prevTid _ _ _ hObjInv hLink0
                    cases hNext : tcbTid.queueNext with
                    | none =>
                      dsimp only [hNext]
                      cases hStore2 : storeObject endpointId _ stPrev with
                      | error e => simp
                      | ok pair2 =>
                      dsimp only [hStore2]
                      have hInvS2 := storeObject_preserves_objects_invExt' stPrev endpointId _ pair2 hInvP hStore2
                      cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                      | error e => simp
                      | ok st4 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        have h1 := storeTcbQueueLinks_notification_backward _ _ tid none none none oid ntfn hInvS2 hFinal hNtfn
                        by_cases hEqId : oid = endpointId
                        · subst hEqId; rw [storeObject_objects_eq' stPrev oid _ pair2 hInvP hStore2] at h1; cases h1
                        · rw [storeObject_objects_ne stPrev pair2.2 endpointId oid _ hEqId hInvP hStore2] at h1
                          exact storeTcbQueueLinks_notification_backward _ _ prevTid _ _ _ oid ntfn hObjInv hLink0 h1
                    | some nextTid =>
                      dsimp only [hNext]
                      cases hLookupN : lookupTcb stPrev nextTid with
                      | none => simp
                      | some nextTcb =>
                      dsimp only [hLookupN]; cases hLink1 : storeTcbQueueLinks stPrev nextTid _ _ nextTcb.queueNext with
                      | error e => simp
                      | ok st2 =>
                      dsimp only [hLink1]
                      have hInvL1 := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _ hInvP hLink1
                      cases hStore2 : storeObject endpointId _ st2 with
                      | error e => simp
                      | ok pair2 =>
                      dsimp only [hStore2]
                      have hInvS2 := storeObject_preserves_objects_invExt' st2 endpointId _ pair2 hInvL1 hStore2
                      cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                      | error e => simp
                      | ok st4 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        have h1 := storeTcbQueueLinks_notification_backward _ _ tid none none none oid ntfn hInvS2 hFinal hNtfn
                        by_cases hEqId : oid = endpointId
                        · subst hEqId; rw [storeObject_objects_eq' st2 oid _ pair2 hInvL1 hStore2] at h1; cases h1
                        · rw [storeObject_objects_ne st2 pair2.2 endpointId oid _ hEqId hInvL1 hStore2] at h1
                          have h2 := storeTcbQueueLinks_notification_backward _ _ nextTid _ _ _ oid ntfn hInvP hLink1 h1
                          exact storeTcbQueueLinks_notification_backward _ _ prevTid _ _ _ oid ntfn hObjInv hLink0 h2

/-- WS-F1/TPI-D08: Backward TCB ipcState transport for endpointQueueRemoveDual.
endpointQueueRemoveDual only calls storeObject (for endpoints) and
storeTcbQueueLinks (which preserves ipcState). Therefore any TCB
present in the post-state has the same ipcState as in the pre-state. -/
theorem endpointQueueRemoveDual_tcb_ipcState_backward
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (anyTid : SeLe4n.ThreadId) (tcb' : TCB)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st'))
    (hTcb' : st'.objects[anyTid.toObjId]? = some (.tcb tcb')) :
    ∃ tcb, st.objects[anyTid.toObjId]? = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState := by
  unfold endpointQueueRemoveDual at hStep; revert hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp
    | endpoint ep =>
      simp only []
      cases hLookup : lookupTcb st tid with
      | none => simp
      | some tcbTid =>
        simp only []
        cases hPPrev : tcbTid.queuePPrev with
        | none => simp
        | some pprev =>
          simp only []
          generalize (if isReceiveQ then ep.receiveQ else ep.sendQ) = q
          split
          · simp
          · cases pprev with
            | endpointHead =>
              simp only []
              split
              · simp
              · cases hStore1 : storeObject endpointId _ st with
                | error e => simp
                | ok pair1 =>
                simp only []
                have hInvS1 := storeObject_preserves_objects_invExt' st endpointId _ pair1 hObjInv hStore1
                cases hNext : tcbTid.queueNext with
                | none =>
                  simp only []
                  cases hStore2 : storeObject endpointId _ pair1.2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only []
                  have hInvS2 := storeObject_preserves_objects_invExt' pair1.2 endpointId _ pair2 hInvS1 hStore2
                  cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    obtain ⟨tcb3, hTcb3, hIpc3⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ tid _ _ _ hInvS2 hFinal anyTid tcb' hTcb'
                    by_cases hEqEp : anyTid.toObjId = endpointId
                    · rw [hEqEp, storeObject_objects_eq' pair1.2 endpointId _ pair2 hInvS1 hStore2] at hTcb3; cases hTcb3
                    · rw [storeObject_objects_ne _ _ endpointId anyTid.toObjId _ hEqEp hInvS1 hStore2] at hTcb3
                      rw [storeObject_objects_ne _ _ endpointId anyTid.toObjId _ hEqEp hObjInv hStore1] at hTcb3
                      exact ⟨tcb3, hTcb3, hIpc3⟩
                | some nextTid =>
                  simp only []
                  cases hLookupN : lookupTcb pair1.2 nextTid with
                  | none => simp
                  | some nextTcb =>
                  simp only []; cases hLink : storeTcbQueueLinks pair1.2 nextTid _ _ nextTcb.queueNext with
                  | error e => simp
                  | ok st2 =>
                  simp only []
                  have hInvL := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _ hInvS1 hLink
                  cases hStore2 : storeObject endpointId _ st2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only []
                  have hInvS2 := storeObject_preserves_objects_invExt' st2 endpointId _ pair2 hInvL hStore2
                  cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    obtain ⟨tcb4, hTcb4, hIpc4⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ tid _ _ _ hInvS2 hFinal anyTid tcb' hTcb'
                    by_cases hEqEp : anyTid.toObjId = endpointId
                    · rw [hEqEp, storeObject_objects_eq' st2 endpointId _ pair2 hInvL hStore2] at hTcb4; cases hTcb4
                    · rw [storeObject_objects_ne _ _ endpointId anyTid.toObjId _ hEqEp hInvL hStore2] at hTcb4
                      obtain ⟨tcb2, hTcb2, hIpc2⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ nextTid _ _ _ hInvS1 hLink anyTid tcb4 hTcb4
                      rw [storeObject_objects_ne _ _ endpointId anyTid.toObjId _ hEqEp hObjInv hStore1] at hTcb2
                      exact ⟨tcb2, hTcb2, hIpc2.trans hIpc4⟩
            | tcbNext prevTid =>
              dsimp only
              split
              · simp
              · cases hLookupP : lookupTcb st prevTid with
                | none => simp
                | some prevTcb =>
                dsimp only [hLookupP]; split
                · simp
                · rename_i _ _ _ stAp heqAp
                  split at heqAp
                  · simp at heqAp
                  · cases hLink0 : storeTcbQueueLinks st prevTid prevTcb.queuePrev prevTcb.queuePPrev tcbTid.queueNext with
                    | error e => simp [hLink0] at heqAp
                    | ok stPrev =>
                    simp [hLink0] at heqAp; subst heqAp
                    have hInvP := storeTcbQueueLinks_preserves_objects_invExt _ _ prevTid _ _ _ hObjInv hLink0
                    cases hNext : tcbTid.queueNext with
                    | none =>
                      dsimp only [hNext]
                      cases hStore2 : storeObject endpointId _ stPrev with
                      | error e => simp
                      | ok pair2 =>
                      dsimp only [hStore2]
                      have hInvS2 := storeObject_preserves_objects_invExt' stPrev endpointId _ pair2 hInvP hStore2
                      cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                      | error e => simp
                      | ok st4 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        obtain ⟨tcb3, hTcb3, hIpc3⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ tid _ _ _ hInvS2 hFinal anyTid tcb' hTcb'
                        by_cases hEqEp : anyTid.toObjId = endpointId
                        · rw [hEqEp, storeObject_objects_eq' stPrev endpointId _ pair2 hInvP hStore2] at hTcb3; cases hTcb3
                        · rw [storeObject_objects_ne _ _ endpointId anyTid.toObjId _ hEqEp hInvP hStore2] at hTcb3
                          obtain ⟨tcb1, hTcb1, hIpc1⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ prevTid _ _ _ hObjInv hLink0 anyTid tcb3 hTcb3
                          exact ⟨tcb1, hTcb1, hIpc1.trans hIpc3⟩
                    | some nextTid =>
                      dsimp only [hNext]
                      cases hLookupN : lookupTcb stPrev nextTid with
                      | none => simp
                      | some nextTcb =>
                      dsimp only [hLookupN]; cases hLink1 : storeTcbQueueLinks stPrev nextTid _ _ nextTcb.queueNext with
                      | error e => simp
                      | ok st2 =>
                      dsimp only [hLink1]
                      have hInvL1 := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _ hInvP hLink1
                      cases hStore2 : storeObject endpointId _ st2 with
                      | error e => simp
                      | ok pair2 =>
                      dsimp only [hStore2]
                      have hInvS2 := storeObject_preserves_objects_invExt' st2 endpointId _ pair2 hInvL1 hStore2
                      cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                      | error e => simp
                      | ok st4 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        obtain ⟨tcb4, hTcb4, hIpc4⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ tid _ _ _ hInvS2 hFinal anyTid tcb' hTcb'
                        by_cases hEqEp : anyTid.toObjId = endpointId
                        · rw [hEqEp, storeObject_objects_eq' st2 endpointId _ pair2 hInvL1 hStore2] at hTcb4; cases hTcb4
                        · rw [storeObject_objects_ne _ _ endpointId anyTid.toObjId _ hEqEp hInvL1 hStore2] at hTcb4
                          obtain ⟨tcb2, hTcb2, hIpc2⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ nextTid _ _ _ hInvP hLink1 anyTid tcb4 hTcb4
                          obtain ⟨tcb1, hTcb1, hIpc1⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ prevTid _ _ _ hObjInv hLink0 anyTid tcb2 hTcb2
                          exact ⟨tcb1, hTcb1, hIpc1.trans (hIpc2.trans hIpc4)⟩

/-- WS-F1/WS-E4/M-01: Send to endpoint using intrusive dual-queue semantics
with IPC message transfer.

Sender checks the intrusive receive queue first. If a receiver is waiting,
rendezvous: transfer `msg` to receiver's TCB and unblock receiver.
Otherwise, enqueue sender in intrusive sendQ, store `msg` in sender's
TCB for later retrieval, and block.

Badge propagation: if `msg.badge` is set, it is carried through to the
receiver, modeling seL4 badge delivery through endpoint capabilities. -/
def endpointSendDual (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) : Kernel Unit :=
  fun st =>
    -- WS-H12d/A-09: Enforce message payload bounds at send boundary
    if msg.registers.size > maxMessageRegisters then .error .ipcMessageTooLarge
    else if msg.caps.size > maxExtraCaps then .error .ipcMessageTooManyCaps
    else
    match st.objects[endpointId]? with
    | some (.endpoint ep) =>
        match ep.receiveQ.head with
        | some _ =>
            -- WS-L1/L1-A: PopHead now returns (ThreadId × TCB × SystemState)
            match endpointQueuePopHead endpointId true st with
            | .error e => .error e
            | .ok (receiver, _tcb, st') =>
                -- WS-F1: Transfer message to receiver and unblock
                match storeTcbIpcStateAndMessage st' receiver .ready (some msg) with
                | .error e => .error e
                | .ok st'' => .ok ((), ensureRunnable st'' receiver)
        | none =>
            match endpointQueueEnqueue endpointId false sender st with
            | .error e => .error e
            | .ok st' =>
                -- WS-F1: Store message in sender's TCB while blocked
                match storeTcbIpcStateAndMessage st' sender (.blockedOnSend endpointId) (some msg) with
                | .error e => .error e
                | .ok st'' => .ok ((), removeRunnable st'' sender)
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

/-- WS-F1/WS-E4/M-01: Receive from endpoint using intrusive dual-queue semantics
with IPC message transfer.

Checks intrusive sendQ first. If a sender is waiting, dequeue it, extract
the pending message from the sender's TCB, deliver it into the receiver's
TCB (pendingMessage), clear the sender's pending message, and unblock sender.
Otherwise, enqueue receiver in intrusive receiveQ and block.

WS-H1/C-01: When the dequeued sender is in `blockedOnCall` state, the sender
transitions to `blockedOnReply` (not `.ready`), preserving the Call contract.
The receiver's ThreadId is recorded as the `replyTarget` so only the authorized
server can reply. Plain `blockedOnSend` senders transition to `.ready` as before.

Returns the sender's ThreadId. The transferred message is available in the
receiver's TCB.pendingMessage after the operation (matching seL4's model
where the message lands in the receiver's IPC buffer). -/
def endpointReceiveDual (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    : Kernel SeLe4n.ThreadId :=
  fun st =>
    match st.objects[endpointId]? with
    | some (.endpoint ep) =>
        match ep.sendQ.head with
        | some _ =>
            -- WS-L1/L1-A: PopHead returns pre-dequeue TCB; read fields directly
            match endpointQueuePopHead endpointId false st with
            | .error e => .error e
            | .ok (sender, senderTcb, st') =>
                -- WS-L1/L1-A: Read pendingMessage and ipcState directly from
                -- returned TCB instead of redundant lookupTcb. These fields are
                -- unchanged by PopHead (only queue links are modified).
                let (senderMsg, senderWasCall) :=
                  (senderTcb.pendingMessage, match senderTcb.ipcState with
                    | .blockedOnCall _ => true
                    | _ => false)
                if senderWasCall then
                  -- Call path: sender transitions to blockedOnReply, NOT ready
                  match storeTcbIpcStateAndMessage st' sender
                      (.blockedOnReply endpointId (some receiver)) none with
                  | .error e => .error e
                  | .ok st'' =>
                      -- WS-F1: Deliver message to receiver's TCB.
                      match storeTcbPendingMessage st'' receiver senderMsg with
                      | .ok st''' => .ok (sender, st''')
                      | .error e => .error e
                else
                  -- Send path: sender transitions to ready as before
                  match storeTcbIpcStateAndMessage st' sender .ready none with
                  | .error e => .error e
                  | .ok st'' =>
                      let st''' := ensureRunnable st'' sender
                      -- WS-F1: Deliver message to receiver's TCB.
                      match storeTcbPendingMessage st''' receiver senderMsg with
                      | .ok st4 => .ok (sender, st4)
                      | .error e => .error e
        | none =>
            match endpointQueueEnqueue endpointId true receiver st with
            | .error e => .error e
            | .ok st' =>
                match storeTcbIpcState st' receiver (.blockedOnReceive endpointId) with
                | .error e => .error e
                | .ok st'' => .ok (receiver, removeRunnable st'' receiver)
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

-- ============================================================================
-- WS-E4/M-12: Reply operations for bidirectional IPC
-- ============================================================================

/-- WS-F1/WS-E4/M-12: Call operation — send then block for reply, with message transfer.

If a receiver is queued: handshake with receiver (transfer `msg`), then block caller for reply.
WS-H1/M-02: The caller's `blockedOnReply` records the receiver's ThreadId as `replyTarget`.
If no receiver queued: enqueue caller as sender with message stored in TCB.
WS-H1/C-01: The caller is enqueued with `blockedOnCall` (not `blockedOnSend`) so that
when a receiver later dequeues, the caller transitions to `blockedOnReply` instead of `.ready`. -/
def endpointCall (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) : Kernel Unit :=
  fun st =>
    -- WS-H12d/A-09: Enforce message payload bounds at send boundary
    if msg.registers.size > maxMessageRegisters then .error .ipcMessageTooLarge
    else if msg.caps.size > maxExtraCaps then .error .ipcMessageTooManyCaps
    else
    match st.objects[endpointId]? with
    | some (.endpoint ep) =>
        match ep.receiveQ.head with
        | some _ =>
            -- WS-L1/L1-A: PopHead now returns (ThreadId × TCB × SystemState)
            match endpointQueuePopHead endpointId true st with
            | .error e => .error e
            | .ok (receiver, _tcb, st') =>
                -- WS-F1: Transfer message to receiver and unblock
                match storeTcbIpcStateAndMessage st' receiver .ready (some msg) with
                | .error e => .error e
                | .ok st'' =>
                    let st''' := ensureRunnable st'' receiver
                    -- WS-H1/M-02: Caller blocks waiting for reply; record receiver as replyTarget
                    match storeTcbIpcState st''' caller (.blockedOnReply endpointId (some receiver)) with
                    | .error e => .error e
                    | .ok st4 => .ok ((), removeRunnable st4 caller)
        | none =>
            match endpointQueueEnqueue endpointId false caller st with
            | .error e => .error e
            | .ok st' =>
                -- WS-H1/C-01: Store message and mark as blockedOnCall (not blockedOnSend)
                match storeTcbIpcStateAndMessage st' caller (.blockedOnCall endpointId) (some msg) with
                | .error e => .error e
                | .ok st'' => .ok ((), removeRunnable st'' caller)
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

/-- WS-F1/WS-E4/M-12: Reply to a thread blocked on reply, with message transfer.

Unblocks the target thread by setting its IPC state to ready, delivers the reply
`msg` into the target's TCB, and adds it to the runnable queue.
Fails if the target is not in blockedOnReply state.
WS-H1/M-02: Validates the `replier` matches the `replyTarget` recorded in the
target's `blockedOnReply` state. If `replyTarget` is `some serverId` and
`replier ≠ serverId`, the operation fails with `replyCapInvalid`, preventing
confused-deputy attacks where unauthorized threads reply to blocked callers. -/
def endpointReply (replier : SeLe4n.ThreadId) (target : SeLe4n.ThreadId)
    (msg : IpcMessage) : Kernel Unit :=
  fun st =>
    -- WS-H12d/A-09: Enforce message payload bounds at send boundary
    if msg.registers.size > maxMessageRegisters then .error .ipcMessageTooLarge
    else if msg.caps.size > maxExtraCaps then .error .ipcMessageTooManyCaps
    else
    match lookupTcb st target with
    | none => .error .objectNotFound
    | some tcb =>
        match tcb.ipcState with
        | .blockedOnReply _ replyTarget =>
            -- WS-H1/M-02: Validate replier is the authorized server
            let authorized := match replyTarget with
              | some expected => replier == expected
              | none => true
            if authorized then
              -- WS-L1/L1-B: Use _fromTcb to avoid redundant lookupTcb on same state
              match storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) with
              | .error e => .error e
              | .ok st' => .ok ((), ensureRunnable st' target)
            else .error .replyCapInvalid
        | _ => .error .replyCapInvalid

/-- WS-H12a: endpointReplyRecv now uses endpointReceiveDual instead of legacy
endpointAwaitReceive. After completing the reply, the receiver enters the
dual-queue receive path: if a sender is already waiting, an immediate
rendezvous occurs; otherwise the receiver enqueues on receiveQ. -/
def endpointReplyRecv
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (replyTarget : SeLe4n.ThreadId)
    (msg : IpcMessage) : Kernel Unit :=
  fun st =>
    -- WS-H12d/A-09: Enforce message payload bounds at send boundary
    if msg.registers.size > maxMessageRegisters then .error .ipcMessageTooLarge
    else if msg.caps.size > maxExtraCaps then .error .ipcMessageTooManyCaps
    else
    match lookupTcb st replyTarget with
    | none => .error .objectNotFound
    | some tcb =>
        match tcb.ipcState with
        | .blockedOnReply _ expectedReplier =>
            -- WS-H1/M-02: Validate receiver is the authorized replier
            let authorized := match expectedReplier with
              | some expected => receiver == expected
              | none => true
            if authorized then
              -- WS-L1/L1-B: Use _fromTcb to avoid redundant lookupTcb on same state
              match storeTcbIpcStateAndMessage_fromTcb st replyTarget tcb .ready (some msg) with
              | .error e => .error e
              | .ok st' =>
                  let st'' := ensureRunnable st' replyTarget
                  -- WS-H12a: Full dual-queue receive path after reply
                  match endpointReceiveDual endpointId receiver st'' with
                  | .error e => .error e
                  | .ok (_, st''') => .ok ((), st''')
            else .error .replyCapInvalid
        | _ => .error .replyCapInvalid


-- ============================================================================
-- WS-L3/L3-D: Tail consistency theorems for endpointQueueRemoveDual
-- ============================================================================

/-- WS-L3/L3-D1: When removing a non-tail thread (queueNext = some _) from a
dual queue, the post-state endpoint queue tail equals the pre-state tail.
The newTail computation in endpointQueueRemoveDual returns q.tail unchanged
when tcb.queueNext is Some. -/
theorem endpointQueueRemoveDual_preserves_tail_of_nonTail
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId) (ep : Endpoint) (tcbR : TCB)
    (nextTid : SeLe4n.ThreadId)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hTcb : lookupTcb st tid = some tcbR)
    (hNonTail : tcbR.queueNext = some nextTid)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    ∃ ep', st'.objects[endpointId]? = some (.endpoint ep') ∧
      (if isReceiveQ then ep'.receiveQ.tail else ep'.sendQ.tail) =
      (if isReceiveQ then ep.receiveQ.tail else ep.sendQ.tail) := by
  unfold endpointQueueRemoveDual at hStep; revert hStep
  rw [hObj]; simp only []
  rw [hTcb]; simp only []
  cases hPPrev : tcbR.queuePPrev with
  | none => simp
  | some pprev =>
    simp only []
    generalize hQ : (if isReceiveQ then ep.receiveQ else ep.sendQ) = q
    split
    · simp
    · cases pprev with
      | endpointHead =>
        simp only []
        split
        · simp
        · cases hStore1 : storeObject endpointId _ st with
          | error e => simp
          | ok pair1 =>
          simp only []; simp only [hNonTail]
          cases hLookupN : lookupTcb pair1.2 nextTid with
          | none => simp
          | some nextTcb =>
          simp only []; cases hLink : storeTcbQueueLinks pair1.2 nextTid _ _ nextTcb.queueNext with
          | error e => simp
          | ok st2 =>
          simp only []; cases hStore2 : storeObject endpointId _ st2 with
          | error e => simp
          | ok pair2 =>
          simp only []; cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
          | error e => simp
          | ok st4 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            have hNeTidEp : endpointId ≠ tid.toObjId :=
              fun h => by rw [h] at hObj; rw [lookupTcb_some_objects st tid tcbR hTcb] at hObj; cases hObj
            have hInvS1 := storeObject_preserves_objects_invExt' st endpointId _ pair1 hObjInv hStore1
            have hInvL := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _ hInvS1 hLink
            have hInvS2 := storeObject_preserves_objects_invExt' st2 endpointId _ pair2 hInvL hStore2
            rw [storeTcbQueueLinks_preserves_objects_ne _ _ tid _ _ _ endpointId hNeTidEp hInvS2 hFinal,
                storeObject_objects_eq' st2 endpointId _ pair2 hInvL hStore2]
            refine ⟨_, rfl, ?_⟩
            cases isReceiveQ <;> simp_all
      | tcbNext prevTid =>
        dsimp only
        split
        · simp
        · cases hLookupP : lookupTcb st prevTid with
          | none => simp
          | some prevTcb =>
          dsimp only [hLookupP]; split
          · simp
          · rename_i _ _ _ stAp heqAp
            split at heqAp
            · simp at heqAp
            · cases hLink0 : storeTcbQueueLinks st prevTid prevTcb.queuePrev prevTcb.queuePPrev tcbR.queueNext with
              | error e => simp [hLink0] at heqAp
              | ok stPrev =>
              simp [hLink0] at heqAp; subst heqAp
              simp only [hNonTail]
              cases hLookupN : lookupTcb stPrev nextTid with
              | none => simp
              | some nextTcb =>
              dsimp only [hLookupN]; cases hLink1 : storeTcbQueueLinks stPrev nextTid _ _ nextTcb.queueNext with
              | error e => simp
              | ok st2 =>
              dsimp only [hLink1]; cases hStore2 : storeObject endpointId _ st2 with
              | error e => simp
              | ok pair2 =>
              dsimp only [hStore2]; cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
              | error e => simp
              | ok st4 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                have hNeTidEp : endpointId ≠ tid.toObjId :=
                  fun h => by rw [h] at hObj; rw [lookupTcb_some_objects st tid tcbR hTcb] at hObj; cases hObj
                have hInvP := storeTcbQueueLinks_preserves_objects_invExt _ _ prevTid _ _ _ hObjInv hLink0
                have hInvL1 := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _ hInvP hLink1
                have hInvS2 := storeObject_preserves_objects_invExt' st2 endpointId _ pair2 hInvL1 hStore2
                rw [storeTcbQueueLinks_preserves_objects_ne _ _ tid _ _ _ endpointId hNeTidEp hInvS2 hFinal,
                    storeObject_objects_eq' st2 endpointId _ pair2 hInvL1 hStore2]
                refine ⟨_, rfl, ?_⟩
                cases isReceiveQ <;> simp_all

/-- WS-L3/L3-D2: Complete characterization of tail behavior when removing
the tail thread (queueNext = none). The new tail is either:
- `none` when pprev = endpointHead (thread was sole element)
- `some prevTid` when pprev = tcbNext prevTid (predecessor becomes tail) -/
theorem endpointQueueRemoveDual_tail_update
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId) (ep : Endpoint) (tcbR : TCB)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hTcb : lookupTcb st tid = some tcbR)
    (hIsTail : tcbR.queueNext = none)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    ∃ ep', st'.objects[endpointId]? = some (.endpoint ep') ∧
      (if isReceiveQ then ep'.receiveQ.tail else ep'.sendQ.tail) =
      match tcbR.queuePPrev with
      | some .endpointHead => none
      | some (.tcbNext prevTid) => some prevTid
      | none => none := by
  unfold endpointQueueRemoveDual at hStep; revert hStep
  rw [hObj]; simp only []
  rw [hTcb]; simp only []
  cases hPPrev : tcbR.queuePPrev with
  | none => simp
  | some pprev =>
    simp only []
    generalize hQ : (if isReceiveQ then ep.receiveQ else ep.sendQ) = q
    split
    · simp
    · cases pprev with
      | endpointHead =>
        simp only []
        split
        · simp
        · cases hStore1 : storeObject endpointId _ st with
          | error e => simp
          | ok pair1 =>
          simp only []; simp only [hIsTail]
          cases hStore2 : storeObject endpointId _ pair1.2 with
          | error e => simp
          | ok pair2 =>
          simp only []; cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
          | error e => simp
          | ok st4 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hEq⟩; subst hEq
            have hNeTidEp : endpointId ≠ tid.toObjId :=
              fun h => by rw [h] at hObj; rw [lookupTcb_some_objects st tid tcbR hTcb] at hObj; cases hObj
            have hInvS1 := storeObject_preserves_objects_invExt' st endpointId _ pair1 hObjInv hStore1
            have hInvS2 := storeObject_preserves_objects_invExt' pair1.2 endpointId _ pair2 hInvS1 hStore2
            rw [storeTcbQueueLinks_preserves_objects_ne _ _ tid _ _ _ endpointId hNeTidEp hInvS2 hFinal,
                storeObject_objects_eq' pair1.2 endpointId _ pair2 hInvS1 hStore2]
            refine ⟨_, rfl, ?_⟩
            cases isReceiveQ <;> simp_all
      | tcbNext prevTid =>
        dsimp only
        split
        · simp
        · cases hLookupP : lookupTcb st prevTid with
          | none => simp
          | some prevTcb =>
          dsimp only [hLookupP]; split
          · simp
          · rename_i _ _ _ stAp heqAp
            split at heqAp
            · simp at heqAp
            · cases hLink0 : storeTcbQueueLinks st prevTid prevTcb.queuePrev prevTcb.queuePPrev tcbR.queueNext with
              | error e => simp [hLink0] at heqAp
              | ok stPrev =>
              simp [hLink0] at heqAp; subst heqAp
              simp only [hIsTail]
              cases hStore2 : storeObject endpointId _ stPrev with
              | error e => simp
              | ok pair2 =>
              dsimp only [hStore2]; cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
              | error e => simp
              | ok st4 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                have hNeTidEp : endpointId ≠ tid.toObjId :=
                  fun h => by rw [h] at hObj; rw [lookupTcb_some_objects st tid tcbR hTcb] at hObj; cases hObj
                have hInvP := storeTcbQueueLinks_preserves_objects_invExt _ _ prevTid _ _ _ hObjInv hLink0
                have hInvS2 := storeObject_preserves_objects_invExt' stPrev endpointId _ pair2 hInvP hStore2
                rw [storeTcbQueueLinks_preserves_objects_ne _ _ tid _ _ _ endpointId hNeTidEp hInvS2 hFinal,
                    storeObject_objects_eq' stPrev endpointId _ pair2 hInvP hStore2]
                refine ⟨_, rfl, ?_⟩
                cases isReceiveQ <;> simp_all

-- ============================================================================
-- WS-L3/L3-A: Enqueue-dequeue round-trip theorems
-- ============================================================================

/-- WS-L3/L3-A1: After enqueue into an empty queue, the endpoint queue has
head = some tid and tail = some tid. -/
theorem endpointQueueEnqueue_empty_sets_head
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (st st' : SystemState)
    (ep : Endpoint)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hEmptyTail : (if isReceiveQ then ep.receiveQ else ep.sendQ).tail = none)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    ∃ ep', st'.objects[endpointId]? = some (.endpoint ep') ∧
      (if isReceiveQ then ep'.receiveQ else ep'.sendQ).head = some tid ∧
      (if isReceiveQ then ep'.receiveQ else ep'.sendQ).tail = some tid := by
  unfold endpointQueueEnqueue at hStep; revert hStep
  rw [hObj]; simp only []
  cases hLookup : lookupTcb st tid with
  | none => simp
  | some tcb =>
    simp only []
    split
    · simp
    · split
      · simp
      · generalize hQ : (if isReceiveQ then ep.receiveQ else ep.sendQ) = q
        rw [show q.tail = none from by rw [← hQ]; exact hEmptyTail]
        simp only []
        cases hStore : storeObject endpointId _ st with
        | error e => simp
        | ok pair =>
          simp only []
          cases hLink : storeTcbQueueLinks pair.2 tid none (some QueuePPrev.endpointHead) none with
          | error e => simp
          | ok st2 =>
            simp only [Except.ok.injEq]
            intro hEq; subst hEq
            have hNe : endpointId ≠ tid.toObjId := fun h => by
              rw [h] at hObj; rw [lookupTcb_some_objects st tid tcb hLookup] at hObj; cases hObj
            have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
            have hEpPost := storeTcbQueueLinks_preserves_objects_ne _ _ tid _ _ _ endpointId hNe hInv1 hLink
            rw [hEpPost, storeObject_objects_eq' st endpointId _ pair hObjInv hStore]
            refine ⟨_, rfl, ?_, ?_⟩ <;> cases isReceiveQ <;> simp_all

/-- WS-L3/L3-A2: After enqueue into an empty queue, the enqueued TCB has
queueNext = none (single-element queue). -/
theorem endpointQueueEnqueue_empty_queueNext_none
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (st st' : SystemState)
    (ep : Endpoint)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hEmptyTail : (if isReceiveQ then ep.receiveQ else ep.sendQ).tail = none)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    ∃ tcb', st'.objects[tid.toObjId]? = some (.tcb tcb') ∧ tcb'.queueNext = none := by
  unfold endpointQueueEnqueue at hStep; revert hStep
  rw [hObj]; simp only []
  cases hLookup : lookupTcb st tid with
  | none => simp
  | some tcb =>
    simp only []
    split
    · simp
    · split
      · simp
      · generalize hQ : (if isReceiveQ then ep.receiveQ else ep.sendQ) = q
        rw [show q.tail = none from by rw [← hQ]; exact hEmptyTail]
        simp only []
        cases hStore : storeObject endpointId _ st with
        | error e => simp
        | ok pair =>
          simp only []
          cases hLink : storeTcbQueueLinks pair.2 tid none (some QueuePPrev.endpointHead) none with
          | error e => simp
          | ok st2 =>
            simp only [Except.ok.injEq]
            intro hEq; subst hEq
            -- The store wrote tcbWithQueueLinks tcb none (some .endpointHead) none
            -- so the resulting TCB has queueNext = none by definition
            have hTcbForward := storeTcbQueueLinks_tcb_forward pair.2 st2 tid none
              (some QueuePPrev.endpointHead) none
            -- We need: the TCB at tid.toObjId has queueNext = none
            -- lookupTcb succeeded during enqueue, so tid exists in pair.2
            have hNe : endpointId ≠ tid.toObjId := fun h => by
              rw [h] at hObj; rw [lookupTcb_some_objects st tid tcb hLookup] at hObj; cases hObj
            have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
            have hTcbInPair : ∃ tcbP, pair.2.objects[tid.toObjId]? = some (.tcb tcbP) := by
              rw [storeObject_objects_ne _ _ endpointId tid.toObjId _ hNe.symm hObjInv hStore]
              exact ⟨tcb, lookupTcb_some_objects st tid tcb hLookup⟩
            obtain ⟨tcbP, hTcbP⟩ := hTcbInPair
            obtain ⟨tcb'', hTcb''⟩ := hTcbForward tid.toObjId tcbP hInv1 hLink hTcbP
            -- tcb'' is tcbWithQueueLinks tcbP none (some .endpointHead) none
            -- Its queueNext is none by definition of tcbWithQueueLinks
            -- But we need to extract queueNext = none. Let's unfold.
            unfold storeTcbQueueLinks at hLink
            cases hLookup2 : lookupTcb pair.2 tid with
            | none => simp [hLookup2] at hLink
            | some tcb2 =>
              rw [hLookup2] at hLink; simp only at hLink
              cases hStore2 : storeObject tid.toObjId (.tcb (tcbWithQueueLinks tcb2 none (some QueuePPrev.endpointHead) none)) pair.2 with
              | error e => rw [hStore2] at hLink; simp at hLink
              | ok pair2 =>
                rw [hStore2] at hLink
                have hEq2 := Except.ok.inj hLink; subst hEq2
                rw [storeObject_objects_eq _ _ tid.toObjId _ hInv1 hStore2]
                exact ⟨_, rfl, rfl⟩

/-- Helper: If `st.objects[tid.toObjId]?` contains a TCB and tid is not reserved,
then `lookupTcb st tid` succeeds. -/
private theorem lookupTcb_of_objects
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hObj : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hNotReserved : ¬tid.isReserved) :
    lookupTcb st tid = some tcb := by
  unfold lookupTcb
  cases hRes : tid.isReserved
  · simp [hObj]
  · simp_all

/-- Helper: If `endpointQueueEnqueue` succeeds with tid, then tid is not reserved. -/
private theorem tid_not_reserved_of_enqueue
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (st st' : SystemState)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    ¬tid.isReserved := by
  unfold endpointQueueEnqueue at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hLookup : lookupTcb st tid with
      | none => simp [hLookup] at hStep
      | some tcb =>
        unfold lookupTcb at hLookup
        cases hRes : tid.isReserved with
        | false => simp
        | true => simp [hRes] at hLookup

/-- WS-L3/L3-A3: Composed round-trip theorem: if a thread is enqueued into an
empty queue and then popHead is called on the same queue, popHead succeeds
returning the same thread. -/
theorem endpointQueueEnqueue_then_popHead_succeeds
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (st st' : SystemState) (ep : Endpoint)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hEmptyTail : (if isReceiveQ then ep.receiveQ else ep.sendQ).tail = none)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    ∃ tcb'' st'', endpointQueuePopHead endpointId isReceiveQ st' = .ok (tid, tcb'', st'') := by
  obtain ⟨ep', hEp', hHead', _⟩ := endpointQueueEnqueue_empty_sets_head
    endpointId isReceiveQ tid st st' ep hObj hEmptyTail hObjInv hStep
  obtain ⟨tcb', hTcb', hNextNone⟩ := endpointQueueEnqueue_empty_queueNext_none
    endpointId isReceiveQ tid st st' ep hObj hEmptyTail hObjInv hStep
  have hNotReserved := tid_not_reserved_of_enqueue endpointId isReceiveQ tid st st' hStep
  have hLookup' := lookupTcb_of_objects st' tid tcb' hTcb' hNotReserved
  have hNe : tid.toObjId ≠ endpointId := fun h => by
    rw [h] at hTcb'; rw [hEp'] at hTcb'; cases hTcb'
  -- Unfold endpointQueuePopHead and step through computationally
  unfold endpointQueuePopHead
  -- Step 1: endpoint lookup → ep'
  rw [hEp']
  -- Step 2: queue head → some tid
  -- After match reduces, q = if isReceiveQ then ep'.receiveQ else ep'.sendQ
  -- and hHead' tells us q.head = some tid
  simp only [hHead']
  -- Step 3: lookupTcb → some tcb'
  rw [hLookup']
  -- Step 4: queueNext = none, so q' = {}, single element path
  simp only [hNextNone]
  -- Step 5: storeObject always succeeds
  -- The ep constructed in popHead: if isReceiveQ then { ep' with receiveQ := {} }
  --                                 else { ep' with sendQ := {} }
  -- storeObject endpointId (.endpoint ...) st' produces some ((), st1)
  have hObjInv' := endpointQueueEnqueue_preserves_objects_invExt endpointId isReceiveQ tid st st' hObjInv hStep
  cases hStoreEp : storeObject endpointId _ st' with
  | error e => exfalso; unfold storeObject at hStoreEp; cases hStoreEp
  | ok pair =>
    obtain ⟨u, st1⟩ := pair
    -- Step 6: since next = none, st2Result = .ok st1 (no next TCB update)
    -- storeTcbQueueLinks needs lookupTcb st1 tid to succeed
    -- TCB survives because tid.toObjId ≠ endpointId
    have hStoreEp' : storeObject endpointId _ st' = .ok (u, st1) := hStoreEp
    have hTcbSt1 : st1.objects[tid.toObjId]? = some (.tcb tcb') := by
      rw [storeObject_objects_ne' st' endpointId tid.toObjId _ (u, st1) hNe hObjInv' hStoreEp']
      exact hTcb'
    have hLookupSt1 := lookupTcb_of_objects st1 tid tcb' hTcbSt1 hNotReserved
    -- Step 7: storeTcbQueueLinks succeeds
    -- Reduce the match on Except.ok to expose storeTcbQueueLinks body
    simp only []
    -- Inline storeTcbQueueLinks: lookupTcb succeeds, storeObject always ok
    unfold storeTcbQueueLinks
    rw [hLookupSt1]; simp only []
    -- Now match on storeObject result
    cases hStore2 : storeObject tid.toObjId _ st1 with
    | error e => exfalso; unfold storeObject at hStore2; cases hStore2
    | ok pair2 =>
      obtain ⟨_, st2⟩ := pair2
      simp only []
      exact ⟨tcb', st2, rfl⟩

end SeLe4n.Kernel
