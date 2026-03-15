/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Operations

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- WS-E4/M-01: Dual-queue endpoint operations (send/receive queue separation)
-- ============================================================================

def tcbWithQueueLinks
    (tcb : TCB)
    (prev : Option SeLe4n.ThreadId)
    (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId) : TCB :=
  { tcb with queuePrev := prev, queuePPrev := pprev, queueNext := next }

def storeTcbQueueLinks
    (st : SystemState)
    (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId)
    (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId) : Except KernelError SystemState :=
  match lookupTcb st tid with
  | none => .error .objectNotFound
  | some tcb =>
      match storeObject tid.toObjId (.tcb (tcbWithQueueLinks tcb prev pprev next)) st with
      | .error e => .error e
      | .ok ((), st') => .ok st'

/-- WS-F1: storeTcbQueueLinks preserves objects at IDs other than tid.toObjId. -/
theorem storeTcbQueueLinks_preserves_objects_ne
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
    (oid : SeLe4n.ObjId) (hNe : oid ≠ tid.toObjId)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    st'.objects[oid]? = st.objects[oid]? := by
  unfold storeTcbQueueLinks at hStep
  cases hTcb : lookupTcb st tid with
  | none => simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb (tcbWithQueueLinks tcb prev pprev next)) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq : pair.snd = st' := Except.ok.inj hStep; subst hEq
      exact storeObject_objects_ne st pair.2 tid.toObjId oid _ hNe hStore

/-- WS-F1: storeTcbQueueLinks does not modify the scheduler. -/
theorem storeTcbQueueLinks_scheduler_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    st'.scheduler = st.scheduler := by
  unfold storeTcbQueueLinks at hStep
  cases hTcb : lookupTcb st tid with
  | none => simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb (tcbWithQueueLinks tcb prev pprev next)) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep; subst hEq
      exact storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore

/-- WS-F1: storeTcbQueueLinks backward endpoint preservation. -/
theorem storeTcbQueueLinks_endpoint_backward
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
    (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st')
    (hEp : st'.objects[oid]? = some (.endpoint ep)) :
    st.objects[oid]? = some (.endpoint ep) := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq; unfold storeTcbQueueLinks at hStep
    cases hLookup : lookupTcb st tid with
    | none => simp [hLookup] at hStep
    | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb (tcbWithQueueLinks tcb prev pprev next)) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        simp only [hStore] at hStep
        have := Except.ok.inj hStep; subst this
        rw [storeObject_objects_eq st pair.2 tid.toObjId _ hStore] at hEp; cases hEp
  · rw [storeTcbQueueLinks_preserves_objects_ne st st' tid prev pprev next oid hEq hStep] at hEp; exact hEp

/-- WS-F1: storeTcbQueueLinks backward notification preservation. -/
theorem storeTcbQueueLinks_notification_backward
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
    (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st')
    (hNtfn : st'.objects[oid]? = some (.notification ntfn)) :
    st.objects[oid]? = some (.notification ntfn) := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq; unfold storeTcbQueueLinks at hStep
    cases hLookup : lookupTcb st tid with
    | none => simp [hLookup] at hStep
    | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb (tcbWithQueueLinks tcb prev pprev next)) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        simp only [hStore] at hStep
        have := Except.ok.inj hStep; subst this
        rw [storeObject_objects_eq st pair.2 tid.toObjId _ hStore] at hNtfn; cases hNtfn
  · rw [storeTcbQueueLinks_preserves_objects_ne st st' tid prev pprev next oid hEq hStep] at hNtfn; exact hNtfn

/-- WS-F1: For any TCB in the post-storeTcbQueueLinks state, a TCB with the same
ipcState exists in the pre-state. At non-target ObjIds the TCB is identical;
at the target, only queue link fields change. -/
theorem storeTcbQueueLinks_tcb_ipcState_backward
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st')
    (anyTid : SeLe4n.ThreadId) (tcb' : TCB)
    (hTcb' : st'.objects[anyTid.toObjId]? = some (.tcb tcb')) :
    ∃ tcb, st.objects[anyTid.toObjId]? = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState := by
  by_cases hEq : anyTid.toObjId = tid.toObjId
  · -- Target: queue links changed but ipcState preserved
    unfold storeTcbQueueLinks at hStep
    cases hLookup : lookupTcb st tid with
    | none => simp [hLookup] at hStep
    | some origTcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb (tcbWithQueueLinks origTcb prev pprev next)) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        simp only [hStore] at hStep
        have := Except.ok.inj hStep; subst this
        rw [hEq, storeObject_objects_eq st pair.2 tid.toObjId _ hStore] at hTcb'
        simp at hTcb'; subst hTcb'
        -- (tcbWithQueueLinks origTcb ...).ipcState = origTcb.ipcState by defn
        exact ⟨origTcb, hEq ▸ lookupTcb_some_objects st tid origTcb hLookup, rfl⟩
  · -- Non-target: object unchanged
    rw [storeTcbQueueLinks_preserves_objects_ne st st' tid prev pprev next anyTid.toObjId hEq hStep] at hTcb'
    exact ⟨tcb', hTcb', rfl⟩

/-- WS-F1: storeTcbQueueLinks forward-preserves TCB existence. If a TCB exists
at oid in the pre-state, some TCB exists at oid in the post-state. -/
theorem storeTcbQueueLinks_tcb_forward
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
    (oid : SeLe4n.ObjId) (tcb : TCB)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st')
    (hTcb : st.objects[oid]? = some (.tcb tcb)) :
    ∃ tcb', st'.objects[oid]? = some (.tcb tcb') := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq; unfold storeTcbQueueLinks at hStep
    cases hLookup : lookupTcb st tid with
    | none => simp [hLookup] at hStep
    | some origTcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb (tcbWithQueueLinks origTcb prev pprev next)) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        simp only [hStore] at hStep; have := Except.ok.inj hStep; subst this
        exact ⟨_, storeObject_objects_eq st pair.2 tid.toObjId _ hStore⟩
  · exact ⟨tcb, by rw [storeTcbQueueLinks_preserves_objects_ne st st' tid prev pprev next oid hEq hStep]; exact hTcb⟩

-- WS-L1/L1-A: Return type includes pre-dequeue TCB. Non-queue fields
-- (ipcState, pendingMessage, priority, domain) are accurate; queue link
-- fields (queuePrev, queuePPrev, queueNext) are stale (cleared in post-state).
def endpointQueuePopHead
    (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool)
    (st : SystemState) : Except KernelError (SeLe4n.ThreadId × TCB × SystemState) :=
  match st.objects[endpointId]? with
  | some (.endpoint ep) =>
      let q := if isReceiveQ then ep.receiveQ else ep.sendQ
      match q.head with
      | none => .error .endpointQueueEmpty
      | some tid =>
          match lookupTcb st tid with
          | none => .error .objectNotFound
          | some headTcb =>
              let next := headTcb.queueNext
              let q' : IntrusiveQueue :=
                match next with
                | some nextTid => { head := some nextTid, tail := q.tail }
                | none => {}
              let ep' : Endpoint := if isReceiveQ then { ep with receiveQ := q' } else { ep with sendQ := q' }
              match storeObject endpointId (.endpoint ep') st with
              | .error e => .error e
              | .ok ((), st1) =>
                  let st2Result :=
                    match next with
                    | none => Except.ok st1
                    | some nextTid =>
                        match lookupTcb st1 nextTid with
                        | none => Except.error KernelError.objectNotFound
                        | some nextTcb => storeTcbQueueLinks st1 nextTid none (some .endpointHead) nextTcb.queueNext
                  match st2Result with
                  | .error e => .error e
                  | .ok st2 =>
                      match storeTcbQueueLinks st2 tid none none none with
                      | .error e => .error e
                      | .ok st3 => .ok (tid, headTcb, st3)
  | some _ => .error .invalidCapability
  | none => .error .objectNotFound

def endpointQueueEnqueue
    (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId)
    (st : SystemState) : Except KernelError SystemState :=
  match st.objects[endpointId]? with
  | some (.endpoint ep) =>
      match lookupTcb st tid with
      | none => .error .objectNotFound
      | some tcb =>
          if tcb.ipcState ≠ .ready then
            .error .alreadyWaiting
          else if tcb.queuePPrev.isSome || tcb.queuePrev.isSome || tcb.queueNext.isSome then
            .error .illegalState
          else
            let q := if isReceiveQ then ep.receiveQ else ep.sendQ
            match q.tail with
            | none =>
                let q' : IntrusiveQueue := { head := some tid, tail := some tid }
                let ep' : Endpoint := if isReceiveQ then { ep with receiveQ := q' } else { ep with sendQ := q' }
                match storeObject endpointId (.endpoint ep') st with
                | .error e => .error e
                | .ok ((), st1) => storeTcbQueueLinks st1 tid none (some .endpointHead) none
            | some tailTid =>
                match lookupTcb st tailTid with
                | none => .error .objectNotFound
                | some tailTcb =>
                    let q' : IntrusiveQueue := { head := q.head, tail := some tid }
                    let ep' : Endpoint := if isReceiveQ then { ep with receiveQ := q' } else { ep with sendQ := q' }
                    match storeObject endpointId (.endpoint ep') st with
                    | .error e => .error e
                    | .ok ((), st1) =>
                        match storeTcbQueueLinks st1 tailTid tailTcb.queuePrev tailTcb.queuePPrev (some tid) with
                        | .error e => .error e
                        | .ok st2 => storeTcbQueueLinks st2 tid (some tailTid) (some (.tcbNext tailTid)) none
  | some _ => .error .invalidCapability
  | none => .error .objectNotFound

