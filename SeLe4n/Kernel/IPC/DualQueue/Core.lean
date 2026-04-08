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
    (hObjInv : st.objects.invExt)
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
      exact storeObject_objects_ne' st tid.toObjId oid _ pair hNe hObjInv hStore

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
    (hObjInv : st.objects.invExt)
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
        rw [storeObject_objects_eq' st tid.toObjId _ pair hObjInv hStore] at hEp; cases hEp
  · rw [storeTcbQueueLinks_preserves_objects_ne st st' tid prev pprev next oid hEq hObjInv hStep] at hEp; exact hEp

/-- WS-F1: storeTcbQueueLinks backward notification preservation. -/
theorem storeTcbQueueLinks_notification_backward
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
    (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hObjInv : st.objects.invExt)
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
        rw [storeObject_objects_eq' st tid.toObjId _ pair hObjInv hStore] at hNtfn; cases hNtfn
  · rw [storeTcbQueueLinks_preserves_objects_ne st st' tid prev pprev next oid hEq hObjInv hStep] at hNtfn; exact hNtfn

/-- WS-F1: For any TCB in the post-storeTcbQueueLinks state, a TCB with the same
ipcState exists in the pre-state. At non-target ObjIds the TCB is identical;
at the target, only queue link fields change. -/
theorem storeTcbQueueLinks_tcb_ipcState_backward
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
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
        rw [hEq, storeObject_objects_eq' st tid.toObjId _ pair hObjInv hStore] at hTcb'
        simp at hTcb'; subst hTcb'
        exact ⟨origTcb, hEq ▸ lookupTcb_some_objects st tid origTcb hLookup, rfl⟩
  · -- Non-target: object unchanged
    rw [storeTcbQueueLinks_preserves_objects_ne st st' tid prev pprev next anyTid.toObjId hEq hObjInv hStep] at hTcb'
    exact ⟨tcb', hTcb', rfl⟩

/-- `storeTcbQueueLinks` preserves `pendingMessage` for all TCBs. At the target,
`tcbWithQueueLinks` only modifies queue link fields; at non-targets, the object
is unchanged. -/
theorem storeTcbQueueLinks_tcb_pendingMessage_backward
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st')
    (anyTid : SeLe4n.ThreadId) (tcb' : TCB)
    (hTcb' : st'.objects[anyTid.toObjId]? = some (.tcb tcb')) :
    ∃ tcb, st.objects[anyTid.toObjId]? = some (.tcb tcb) ∧ tcb.pendingMessage = tcb'.pendingMessage := by
  by_cases hEq : anyTid.toObjId = tid.toObjId
  · -- Target: queue links changed but pendingMessage preserved
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
        rw [hEq, storeObject_objects_eq' st tid.toObjId _ pair hObjInv hStore] at hTcb'
        simp at hTcb'; subst hTcb'
        exact ⟨origTcb, hEq ▸ lookupTcb_some_objects st tid origTcb hLookup, rfl⟩
  · -- Non-target: object unchanged
    rw [storeTcbQueueLinks_preserves_objects_ne st st' tid prev pprev next anyTid.toObjId hEq hObjInv hStep] at hTcb'
    exact ⟨tcb', hTcb', rfl⟩

/-- WS-F1: storeTcbQueueLinks forward-preserves TCB existence. If a TCB exists
at oid in the pre-state, some TCB exists at oid in the post-state. -/
theorem storeTcbQueueLinks_tcb_forward
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
    (oid : SeLe4n.ObjId) (tcb : TCB)
    (hObjInv : st.objects.invExt)
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
        exact ⟨_, storeObject_objects_eq' st tid.toObjId _ pair hObjInv hStore⟩
  · exact ⟨tcb, by rw [storeTcbQueueLinks_preserves_objects_ne st st' tid prev pprev next oid hEq hObjInv hStep]; exact hTcb⟩

/-- WS-L3/L3-C: storeTcbQueueLinks forward-preserves endpoint existence.
An endpoint at any ObjId in the pre-state survives storeTcbQueueLinks. -/
theorem storeTcbQueueLinks_endpoint_forward
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
    (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st')
    (hEp : st.objects[oid]? = some (.endpoint ep)) :
    ∃ ep', st'.objects[oid]? = some (.endpoint ep') := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq; unfold storeTcbQueueLinks at hStep
    cases hLookup : lookupTcb st tid with
    | none => simp [hLookup] at hStep
    | some tcb =>
      rw [lookupTcb_some_objects st tid tcb hLookup] at hEp; cases hEp
  · exact ⟨ep, by rw [storeTcbQueueLinks_preserves_objects_ne st st' tid prev pprev next oid hEq hObjInv hStep]; exact hEp⟩

/-- storeTcbQueueLinks preserves objects.invExt. -/
theorem storeTcbQueueLinks_preserves_objects_invExt
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    st'.objects.invExt := by
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
      exact storeObject_preserves_objects_invExt' st tid.toObjId _ pair hObjInv hStore

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

/-- WS-L1/L1-A (AD2-A): Convenience wrapper that returns the *post-state* TCB
    with cleared queue links, avoiding the stale-snapshot footgun.
    `endpointQueuePopHead` returns the pre-dequeue TCB whose queue link fields
    (queuePrev, queuePPrev, queueNext) are stale — they reflect the pre-state,
    not the post-state where links have been cleared. Use this variant when the
    caller needs accurate queue link fields from the post-state.
    Non-queue fields (ipcState, pendingMessage, priority, domain) are identical
    in both variants. -/
def endpointQueuePopHeadFresh
    (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool)
    (st : SystemState) : Except KernelError (SeLe4n.ThreadId × TCB × SystemState) :=
  match endpointQueuePopHead endpointId isReceiveQ st with
  | .ok (tid, _staleTcb, st') =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb freshTcb) => .ok (tid, freshTcb, st')
    | _ => .error .objectNotFound  -- unreachable: popHead stores cleared TCB
  | .error e => .error e

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

/-- endpointQueuePopHead preserves objects.invExt. -/
theorem endpointQueuePopHead_preserves_objects_invExt
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (headTcb : TCB)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, headTcb, st')) :
    st'.objects.invExt := by
  unfold endpointQueuePopHead at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp [hHead] at hStep
      | some headTid =>
        simp only [hHead] at hStep
        cases hLookup : lookupTcb st headTid with
        | none => simp [hLookup] at hStep
        | some tcb =>
          simp only [hLookup] at hStep
          revert hStep
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
            cases hNext : tcb.queueNext with
            | none =>
              simp only []
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, _, rfl⟩
                exact storeTcbQueueLinks_preserves_objects_invExt _ _ headTid _ _ _ hInv1 hFinal
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
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, _, rfl⟩
                    exact storeTcbQueueLinks_preserves_objects_invExt _ _ headTid _ _ _ hInv2 hFinal

/-- endpointQueueEnqueue preserves objects.invExt. -/
theorem endpointQueueEnqueue_preserves_objects_invExt
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    st'.objects.invExt := by
  unfold endpointQueueEnqueue at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hStep
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
            cases (if isReceiveQ then ep.receiveQ else ep.sendQ).tail with
            | none =>
              cases hStore : storeObject endpointId _ st with
              | error e => simp
              | ok pair =>
                simp only []
                have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                intro hStep
                exact storeTcbQueueLinks_preserves_objects_invExt _ _ tid _ _ _ hInv1 hStep
            | some tailTid =>
              cases hLookupT : lookupTcb st tailTid
              · simp [hLookupT]
              · rename_i tailTcb
                simp only [hLookupT]
                cases hStore : storeObject endpointId _ st
                · simp
                · rename_i pair
                  simp only []
                  have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                  cases hLink1 : storeTcbQueueLinks pair.2 tailTid _ _ (some tid)
                  · simp
                  · rename_i st2
                    simp only []
                    have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ tailTid _ _ _ hInv1 hLink1
                    intro hStep
                    exact storeTcbQueueLinks_preserves_objects_invExt _ _ tid _ _ _ hInv2 hStep

-- ============================================================================
-- Z6-D: Mid-queue thread removal for timeout unblocking
-- ============================================================================

/-- Z6-D1/D2: Remove a specific thread from an endpoint's send or receive queue.

Unlike `endpointQueuePopHead` which only dequeues the head, this operation
removes an arbitrary thread from anywhere in the queue (head, middle, or tail).
Used by `timeoutThread` to unblock a timed-out thread that may not be at the
head of the wait queue.

This is the pure-function counterpart to `endpointQueueRemoveDual` (Transport.lean).
`endpointQueueRemoveDual` uses `queuePPrev` back-pointers and `storeObject` with
full consistency validation. This function uses direct `RHTable.insert` for simpler
proof obligations (see `endpointQueueRemove_preserves_objects_invExt`).

The operation:
1. Looks up the endpoint and verifies the thread exists
2. Patches the predecessor's `queueNext` to skip over the removed thread
3. Patches the successor's `queuePrev` to skip over the removed thread
4. Updates the endpoint's head/tail pointers if the removed thread was at
   either boundary
5. Clears the removed thread's queue linkage fields (including `queuePPrev`)

**Invariant assumption (AUD-Z6-1):** Steps 2 and 3 use `| _ => objs` as a
defensive fallback when predecessor/successor lookup fails or returns a
non-TCB object. Under `ipcStateQueueMembershipConsistent` and
`queueNextBlockingConsistent` invariants, queue-linked thread IDs always
resolve to valid TCB objects, so the fallback is unreachable in well-formed
states. The fallback is retained (rather than returning an error) because:
- The timeout path must be non-failing for threads that are genuinely queued
- Returning an error would abort the entire timeout scan in `timeoutBlockedThreads`
- The invariant proofs guarantee this branch is dead code in practice

Returns the updated state, or an error if the endpoint or thread is not found. -/
def endpointQueueRemove
    (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId)
    (st : SystemState) : Except KernelError SystemState :=
  match st.objects[endpointId]? with
  | some (.endpoint ep) =>
    match lookupTcb st tid with
    | none => .error .objectNotFound
    | some tcb =>
      let q := if isReceiveQ then ep.receiveQ else ep.sendQ
      -- AF5-C (AF-06): Direct RHTable.insert (bypassing storeObject) is
      -- intentional for the queue-remove path where only queue links and
      -- ipcState are modified, not object lifecycle. Fallback unreachability
      -- proven by `queueRemove_predecessor_exists` and
      -- `queueRemove_successor_exists` (AE4-E). See dualQueueSystemInvariant
      -- for correctness proof.
      -- Step 1: Patch predecessor's queueNext to skip tid
      let objs := st.objects
      let objs := match tcb.queuePrev with
        | none => objs  -- tid is head; no predecessor to patch
        | some prevTid =>
          match objs[prevTid.toObjId]? with
          | some (.tcb prevTcb) =>
            objs.insert prevTid.toObjId (.tcb { prevTcb with queueNext := tcb.queueNext })
          | _ => objs
      -- Step 2: Patch successor's queuePrev to skip tid
      let objs := match tcb.queueNext with
        | none => objs  -- tid is tail; no successor to patch
        | some nextTid =>
          match objs[nextTid.toObjId]? with
          | some (.tcb nextTcb) =>
            objs.insert nextTid.toObjId (.tcb { nextTcb with queuePrev := tcb.queuePrev })
          | _ => objs
      -- Step 3: Update endpoint head/tail pointers
      let q' : IntrusiveQueue := {
        head := if q.head = some tid then tcb.queueNext else q.head,
        tail := if q.tail = some tid then tcb.queuePrev else q.tail }
      let ep' := if isReceiveQ then { ep with receiveQ := q' } else { ep with sendQ := q' }
      let objs := objs.insert endpointId (.endpoint ep')
      -- Step 4: Clear removed thread's queue links
      let objs := objs.insert tid.toObjId (.tcb { tcb with
        queuePrev := none, queuePPrev := none, queueNext := none })
      .ok { st with objects := objs }
  | some _ => .error .invalidCapability
  | none => .error .objectNotFound

/-- Z6-D: `endpointQueueRemove` preserves `objects.invExt`.

The operation performs up to 4 `RHTable.insert` calls (predecessor patch,
successor patch, endpoint update, TCB link clear). Each insert preserves
`invExt` by `RHTable.insert_preserves_invExt`. -/
theorem endpointQueueRemove_preserves_objects_invExt
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemove endpointId isReceiveQ tid st = .ok st') :
    st'.objects.invExt := by
  unfold endpointQueueRemove at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ =>
      simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hTcb : lookupTcb st tid with
      | none => simp [hTcb] at hStep
      | some tcb =>
        simp only [hTcb] at hStep
        simp only [Except.ok.injEq] at hStep
        rw [← hStep]; simp only []
        -- Result objects = st.objects with up to 4 conditional inserts.
        -- Each insert preserves invExt via RobinHood.insert_preserves_invExt.
        -- Chain through all branch combinations:
        have ins := @SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt
        repeat (first | exact hObjInv | apply ins | split)

-- ============================================================================
-- AE4-E (U-24/IPC-02): endpointQueueRemove fallback unreachability
-- ============================================================================

/-- AE4-E (U-24/IPC-02): Under doubly-linked queue link integrity, the
predecessor TCB lookup in `endpointQueueRemove` always succeeds.

The hypothesis `hReverseInt` is the reverse direction of
`tcbQueueLinkIntegrity` (defined in IPC/Invariant/Defs.lean):
  b.queuePrev = some a → a exists as TCB ∧ a.queueNext = some b

This proves that the fallback `| _ => objs` at the predecessor patch
is unreachable under the IPC invariant. -/
theorem queueRemove_predecessor_exists
    (st : SystemState) (tid : SeLe4n.ThreadId) (prevTid : SeLe4n.ThreadId)
    (tcb : TCB)
    (hReverseInt : ∀ (b : SeLe4n.ThreadId) (tcbB : TCB),
      st.objects[b.toObjId]? = some (.tcb tcbB) →
      ∀ (a : SeLe4n.ThreadId), tcbB.queuePrev = some a →
        ∃ tcbA, st.objects[a.toObjId]? = some (.tcb tcbA) ∧ tcbA.queueNext = some b)
    (hTcb : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hPrev : tcb.queuePrev = some prevTid) :
    ∃ prevTcb, st.objects[prevTid.toObjId]? = some (.tcb prevTcb) := by
  have ⟨prevTcb, hPrevObj, _⟩ := hReverseInt tid tcb hTcb prevTid hPrev
  exact ⟨prevTcb, hPrevObj⟩

/-- AE4-E (U-24/IPC-02): Under doubly-linked queue link integrity, the
successor TCB lookup in `endpointQueueRemove` always succeeds.

The hypothesis `hForwardInt` is the forward direction of
`tcbQueueLinkIntegrity` (defined in IPC/Invariant/Defs.lean):
  a.queueNext = some b → b exists as TCB ∧ b.queuePrev = some a

This proves that the fallback `| _ => objs` at the successor patch
is unreachable under the IPC invariant. -/
theorem queueRemove_successor_exists
    (st : SystemState) (tid : SeLe4n.ThreadId) (nextTid : SeLe4n.ThreadId)
    (tcb : TCB)
    (hForwardInt : ∀ (a : SeLe4n.ThreadId) (tcbA : TCB),
      st.objects[a.toObjId]? = some (.tcb tcbA) →
      ∀ (b : SeLe4n.ThreadId), tcbA.queueNext = some b →
        ∃ tcbB, st.objects[b.toObjId]? = some (.tcb tcbB) ∧ tcbB.queuePrev = some a)
    (hTcb : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hNext : tcb.queueNext = some nextTid) :
    ∃ nextTcb, st.objects[nextTid.toObjId]? = some (.tcb nextTcb) := by
  have ⟨nextTcb, hNextObj, _⟩ := hForwardInt tid tcb hTcb nextTid hNext
  exact ⟨nextTcb, hNextObj⟩

/- AE4-E/IPC-02: Fallback branch documentation.

  In `endpointQueueRemove`, the two `| _ => objs` fallback branches (at the
  predecessor and successor patches) are unreachable under `dualQueueSystemInvariant`:
  - Predecessor fallback: `queueRemove_predecessor_exists` proves that if
    `tcb.queuePrev = some prevTid`, then `objs[prevTid.toObjId]?` is
    `some (.tcb prevTcb)` — the predecessor TCB always exists.
  - Successor fallback: `queueRemove_successor_exists` proves the same for
    `tcb.queueNext = some nextTid`.

  The fallback preserves state unchanged (defensive, no corruption) and is
  retained for totality of the pure function. The invariant guarantee means
  the fallback code is dead code under correct system operation. -/

