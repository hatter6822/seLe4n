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

def endpointQueuePopHead
    (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool)
    (st : SystemState) : Except KernelError (SeLe4n.ThreadId × SystemState) :=
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
                      | .ok st3 => .ok (tid, st3)
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

-- ============================================================================
-- WS-F1: Transport lemmas for endpointQueuePopHead
-- ============================================================================

/-- WS-F1: endpointQueuePopHead does not modify the scheduler. -/
theorem endpointQueuePopHead_scheduler_eq
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, st')) :
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
                intro ⟨_, hEq⟩; subst hEq
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
                    intro ⟨_, hEq⟩; subst hEq
                    exact (storeTcbQueueLinks_scheduler_eq _ _ headTid none none none hFinal).trans
                      ((storeTcbQueueLinks_scheduler_eq _ _ nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext hLink).trans
                        (storeObject_scheduler_eq _ _ endpointId _ hStore))

/-- WS-F1: endpointQueuePopHead backward-preserves endpoints at oid ≠ endpointId. -/
theorem endpointQueuePopHead_endpoint_backward_ne
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hNe : oid ≠ endpointId)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, st'))
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
                intro ⟨_, hEq⟩; subst hEq
                have h1 := storeTcbQueueLinks_endpoint_backward _ _ headTid none none none oid ep hFinal hEp
                rwa [storeObject_objects_ne st pair.2 endpointId oid _ hNe hStore] at h1
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
                    intro ⟨_, hEq⟩; subst hEq
                    have h3 := storeTcbQueueLinks_endpoint_backward _ _ headTid none none none oid ep hFinal hEp
                    have h2 := storeTcbQueueLinks_endpoint_backward _ _ nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext oid ep hLink h3
                    rwa [storeObject_objects_ne st pair.2 endpointId oid _ hNe hStore] at h2

/-- WS-F1: endpointQueuePopHead backward-preserves notifications. -/
theorem endpointQueuePopHead_notification_backward
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, st'))
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
                intro ⟨_, hEq⟩; subst hEq
                have h1 := storeTcbQueueLinks_notification_backward _ _ headTid none none none oid ntfn hFinal hNtfn
                by_cases hEqId : oid = endpointId
                · subst hEqId; rw [storeObject_objects_eq st pair.2 oid _ hStore] at h1; cases h1
                · rwa [storeObject_objects_ne st pair.2 endpointId oid _ hEqId hStore] at h1
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
                    intro ⟨_, hEq⟩; subst hEq
                    have h3 := storeTcbQueueLinks_notification_backward _ _ headTid none none none oid ntfn hFinal hNtfn
                    have h2 := storeTcbQueueLinks_notification_backward _ _ nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext oid ntfn hLink h3
                    by_cases hEqId : oid = endpointId
                    · subst hEqId; rw [storeObject_objects_eq st pair.2 oid _ hStore] at h2; cases h2
                    · rwa [storeObject_objects_ne st pair.2 endpointId oid _ hEqId hStore] at h2

/-- WS-F1: endpointQueuePopHead forward-preserves TCB existence. If a TCB exists
at oid in the pre-state, some TCB exists at oid in the post-state. -/
theorem endpointQueuePopHead_tcb_forward
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (oid : SeLe4n.ObjId) (tcb : TCB)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, st'))
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
            have hTcb1 : pair.2.objects[oid]? = some (.tcb tcb) := by
              rw [storeObject_objects_ne st pair.2 endpointId oid _ hNe hStore]; exact hTcb
            cases hNext : headTcb.queueNext with
            | none =>
              simp only []
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                exact storeTcbQueueLinks_tcb_forward pair.2 st3 headTid none none none oid tcb hFinal hTcb1
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
                  obtain ⟨tcb2, hTcb2⟩ := storeTcbQueueLinks_tcb_forward pair.2 st2 nextTid _ _ _ oid tcb hLink hTcb1
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    exact storeTcbQueueLinks_tcb_forward st2 st3 headTid none none none oid tcb2 hFinal hTcb2

/-- WS-F1: endpointQueuePopHead backward-preserves TCB ipcStates. For any TCB
in the post-state, a TCB with the same ipcState exists in the pre-state. -/
theorem endpointQueuePopHead_tcb_ipcState_backward
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (anyTid : SeLe4n.ThreadId) (tcb' : TCB)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, st'))
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
                intro ⟨_, hEq⟩; subst hEq
                obtain ⟨tcb1, hTcb1, hIpc1⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ headTid none none none hFinal anyTid tcb' hTcb'
                by_cases hEqEp : anyTid.toObjId = endpointId
                · rw [hEqEp] at hTcb1; rw [storeObject_objects_eq st pair.2 endpointId _ hStore] at hTcb1; cases hTcb1
                · rw [storeObject_objects_ne st pair.2 endpointId anyTid.toObjId _ hEqEp hStore] at hTcb1
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
                    intro ⟨_, hEq⟩; subst hEq
                    obtain ⟨tcb2, hTcb2, hIpc2⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ headTid none none none hFinal anyTid tcb' hTcb'
                    obtain ⟨tcb1, hTcb1, hIpc1⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ nextTid _ _ _ hLink anyTid tcb2 hTcb2
                    by_cases hEqEp : anyTid.toObjId = endpointId
                    · rw [hEqEp] at hTcb1; rw [storeObject_objects_eq st pair.2 endpointId _ hStore] at hTcb1; cases hTcb1
                    · rw [storeObject_objects_ne st pair.2 endpointId anyTid.toObjId _ hEqEp hStore] at hTcb1
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
                have h1 := storeTcbQueueLinks_endpoint_backward _ _ enqueueTid _ _ _ oid ep hStep hEp
                rwa [storeObject_objects_ne st pair.2 endpointId oid _ hNe hStore] at h1
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
                    have h3 := storeTcbQueueLinks_endpoint_backward _ _ enqueueTid _ _ _ oid ep hStep hEp
                    have h2 := storeTcbQueueLinks_endpoint_backward _ _ tailTid _ _ _ oid ep hLink1 h3
                    rwa [storeObject_objects_ne st pair.2 endpointId oid _ hNe hStore] at h2

/-- WS-F1: endpointQueueEnqueue backward-preserves notifications. -/
theorem endpointQueueEnqueue_notification_backward
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (enqueueTid : SeLe4n.ThreadId) (st st' : SystemState)
    (oid : SeLe4n.ObjId) (ntfn : Notification)
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
                have h1 := storeTcbQueueLinks_notification_backward _ _ enqueueTid _ _ _ oid ntfn hStep hNtfn
                by_cases hEqId : oid = endpointId
                · subst hEqId; rw [storeObject_objects_eq st pair.2 oid _ hStore] at h1; cases h1
                · rwa [storeObject_objects_ne st pair.2 endpointId oid _ hEqId hStore] at h1
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
                    have h3 := storeTcbQueueLinks_notification_backward _ _ enqueueTid _ _ _ oid ntfn hStep hNtfn
                    have h2 := storeTcbQueueLinks_notification_backward _ _ tailTid _ _ _ oid ntfn hLink1 h3
                    by_cases hEqId : oid = endpointId
                    · subst hEqId; rw [storeObject_objects_eq st pair.2 oid _ hStore] at h2; cases h2
                    · rwa [storeObject_objects_ne st pair.2 endpointId oid _ hEqId hStore] at h2

/-- WS-F1: endpointQueueEnqueue forward-preserves TCB existence. -/
theorem endpointQueueEnqueue_tcb_forward
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (enqueueTid : SeLe4n.ThreadId) (st st' : SystemState)
    (oid : SeLe4n.ObjId) (tcb : TCB)
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
                have hTcb1 : pair.2.objects[oid]? = some (.tcb tcb) := by
                  rw [storeObject_objects_ne st pair.2 endpointId oid _ hNe hStore]; exact hTcb
                exact storeTcbQueueLinks_tcb_forward pair.2 st' enqueueTid _ _ _ oid tcb hStep hTcb1
            | some tailTid =>
              cases hLookupTail : lookupTcb st tailTid with
              | none => simp [hLookupTail]
              | some tailTcb =>
                simp only [hLookupTail]
                cases hStore : storeObject endpointId _ st with
                | error e => simp
                | ok pair =>
                  simp only []
                  have hTcb1 : pair.2.objects[oid]? = some (.tcb tcb) := by
                    rw [storeObject_objects_ne st pair.2 endpointId oid _ hNe hStore]; exact hTcb
                  cases hLink1 : storeTcbQueueLinks pair.2 tailTid tailTcb.queuePrev tailTcb.queuePPrev (some enqueueTid) with
                  | error e => simp
                  | ok st2 =>
                    simp only []; intro hStep
                    obtain ⟨tcb2, hTcb2⟩ := storeTcbQueueLinks_tcb_forward pair.2 st2 tailTid _ _ _ oid tcb hLink1 hTcb1
                    exact storeTcbQueueLinks_tcb_forward st2 st' enqueueTid _ _ _ oid tcb2 hStep hTcb2

/-- WS-F1: endpointQueueEnqueue backward-preserves TCB ipcStates. -/
theorem endpointQueueEnqueue_tcb_ipcState_backward
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (enqueueTid : SeLe4n.ThreadId) (st st' : SystemState)
    (anyTid : SeLe4n.ThreadId) (tcb' : TCB)
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
                obtain ⟨tcb1, hTcb1, hIpc1⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ enqueueTid _ _ _ hStep anyTid tcb' hTcb'
                by_cases hEqEp : anyTid.toObjId = endpointId
                · rw [hEqEp] at hTcb1; rw [storeObject_objects_eq st pair.2 endpointId _ hStore] at hTcb1; cases hTcb1
                · rw [storeObject_objects_ne st pair.2 endpointId anyTid.toObjId _ hEqEp hStore] at hTcb1
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
                    obtain ⟨tcb3, hTcb3, hIpc3⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ enqueueTid _ _ _ hStep anyTid tcb' hTcb'
                    obtain ⟨tcb2, hTcb2, hIpc2⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ tailTid _ _ _ hLink1 anyTid tcb3 hTcb3
                    by_cases hEqEp : anyTid.toObjId = endpointId
                    · rw [hEqEp] at hTcb2; rw [storeObject_objects_eq st pair.2 endpointId _ hStore] at hTcb2; cases hTcb2
                    · rw [storeObject_objects_ne st pair.2 endpointId anyTid.toObjId _ hEqEp hStore] at hTcb2
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
                have hTcb1 : pair1.2.objects[oid]? = some (.tcb tcb) := by
                  rw [storeObject_objects_ne st pair1.2 endpointId oid _ hNe hStore1]; exact hTcb
                cases hNext : tcbTid.queueNext with
                | none =>
                  simp only []
                  cases hStore2 : storeObject endpointId _ pair1.2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only []
                  have hTcb2 : pair2.2.objects[oid]? = some (.tcb tcb) := by
                    rw [storeObject_objects_ne pair1.2 pair2.2 endpointId oid _ hNe hStore2]; exact hTcb1
                  cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    exact storeTcbQueueLinks_tcb_forward pair2.2 st4 tid none none none oid tcb hFinal hTcb2
                | some nextTid =>
                  simp only []
                  cases hLookupN : lookupTcb pair1.2 nextTid with
                  | none => simp
                  | some nextTcb =>
                  simp only []; cases hLink : storeTcbQueueLinks pair1.2 nextTid _ _ nextTcb.queueNext with
                  | error e => simp
                  | ok st2 =>
                  simp only []
                  obtain ⟨tcb2, hTcb2⟩ := storeTcbQueueLinks_tcb_forward pair1.2 st2 nextTid _ _ _ oid tcb hLink hTcb1
                  cases hStore2 : storeObject endpointId _ st2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only []
                  have hTcb3 : pair2.2.objects[oid]? = some (.tcb tcb2) := by
                    rw [storeObject_objects_ne st2 pair2.2 endpointId oid _ hNe hStore2]; exact hTcb2
                  cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    exact storeTcbQueueLinks_tcb_forward pair2.2 st4 tid none none none oid tcb2 hFinal hTcb3
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
                    obtain ⟨tcb0, hTcb0⟩ := storeTcbQueueLinks_tcb_forward st stPrev prevTid _ _ _ oid tcb hLink0 hTcb
                    cases hNext : tcbTid.queueNext with
                    | none =>
                      dsimp only [hNext]
                      cases hStore2 : storeObject endpointId _ stPrev with
                      | error e => simp
                      | ok pair2 =>
                      dsimp only [hStore2]
                      have hTcb1 : pair2.2.objects[oid]? = some (.tcb tcb0) := by
                        rw [storeObject_objects_ne stPrev pair2.2 endpointId oid _ hNe hStore2]; exact hTcb0
                      cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                      | error e => simp
                      | ok st4 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        exact storeTcbQueueLinks_tcb_forward pair2.2 st4 tid none none none oid tcb0 hFinal hTcb1
                    | some nextTid =>
                      dsimp only [hNext]
                      cases hLookupN : lookupTcb stPrev nextTid with
                      | none => simp
                      | some nextTcb =>
                      dsimp only [hLookupN]; cases hLink1 : storeTcbQueueLinks stPrev nextTid _ _ nextTcb.queueNext with
                      | error e => simp
                      | ok st2 =>
                      dsimp only [hLink1]
                      obtain ⟨tcb1, hTcb1⟩ := storeTcbQueueLinks_tcb_forward stPrev st2 nextTid _ _ _ oid tcb0 hLink1 hTcb0
                      cases hStore2 : storeObject endpointId _ st2 with
                      | error e => simp
                      | ok pair2 =>
                      dsimp only [hStore2]
                      have hTcb2 : pair2.2.objects[oid]? = some (.tcb tcb1) := by
                        rw [storeObject_objects_ne st2 pair2.2 endpointId oid _ hNe hStore2]; exact hTcb1
                      cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                      | error e => simp
                      | ok st4 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        exact storeTcbQueueLinks_tcb_forward pair2.2 st4 tid none none none oid tcb1 hFinal hTcb2

/-- WS-F1: Backward endpoint transport for endpointQueueRemoveDual (non-target endpoint).
If an endpoint exists at `oid ≠ endpointId` in the post-state, it existed unchanged in the pre-state. -/
theorem endpointQueueRemoveDual_endpoint_backward_ne
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId) (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hNe : oid ≠ endpointId)
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
                simp only []; cases hNext : tcbTid.queueNext with
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
                    have h1 := storeTcbQueueLinks_endpoint_backward _ _ tid none none none oid ep hFinal hEp
                    rw [storeObject_objects_ne pair1.2 pair2.2 endpointId oid _ hNe hStore2] at h1
                    rwa [storeObject_objects_ne st pair1.2 endpointId oid _ hNe hStore1] at h1
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
                    have h1 := storeTcbQueueLinks_endpoint_backward _ _ tid none none none oid ep hFinal hEp
                    rw [storeObject_objects_ne st2 pair2.2 endpointId oid _ hNe hStore2] at h1
                    have h2 := storeTcbQueueLinks_endpoint_backward _ _ nextTid _ _ _ oid ep hLink h1
                    rwa [storeObject_objects_ne st pair1.2 endpointId oid _ hNe hStore1] at h2
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
                    cases hNext : tcbTid.queueNext with
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
                        have h1 := storeTcbQueueLinks_endpoint_backward _ _ tid none none none oid ep hFinal hEp
                        rw [storeObject_objects_ne stPrev pair2.2 endpointId oid _ hNe hStore2] at h1
                        exact storeTcbQueueLinks_endpoint_backward _ _ prevTid _ _ _ oid ep hLink0 h1
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
                        have h1 := storeTcbQueueLinks_endpoint_backward _ _ tid none none none oid ep hFinal hEp
                        rw [storeObject_objects_ne st2 pair2.2 endpointId oid _ hNe hStore2] at h1
                        have h2 := storeTcbQueueLinks_endpoint_backward _ _ nextTid _ _ _ oid ep hLink1 h1
                        exact storeTcbQueueLinks_endpoint_backward _ _ prevTid _ _ _ oid ep hLink0 h2

/-- WS-F1: Backward notification transport for endpointQueueRemoveDual.
If a notification exists at `oid` in the post-state, it existed unchanged in the pre-state. -/
theorem endpointQueueRemoveDual_notification_backward
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId) (oid : SeLe4n.ObjId) (ntfn : Notification)
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
                simp only []; cases hNext : tcbTid.queueNext with
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
                    have h1 := storeTcbQueueLinks_notification_backward _ _ tid none none none oid ntfn hFinal hNtfn
                    by_cases hEqId : oid = endpointId
                    · subst hEqId; rw [storeObject_objects_eq _ _ oid _ hStore2] at h1; cases h1
                    · rw [storeObject_objects_ne pair1.2 pair2.2 endpointId oid _ hEqId hStore2] at h1
                      rwa [storeObject_objects_ne st pair1.2 endpointId oid _ hEqId hStore1] at h1
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
                    have h1 := storeTcbQueueLinks_notification_backward _ _ tid none none none oid ntfn hFinal hNtfn
                    by_cases hEqId : oid = endpointId
                    · subst hEqId; rw [storeObject_objects_eq _ _ oid _ hStore2] at h1; cases h1
                    · rw [storeObject_objects_ne st2 pair2.2 endpointId oid _ hEqId hStore2] at h1
                      have h2 := storeTcbQueueLinks_notification_backward _ _ nextTid _ _ _ oid ntfn hLink h1
                      rwa [storeObject_objects_ne st pair1.2 endpointId oid _ hEqId hStore1] at h2
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
                    cases hNext : tcbTid.queueNext with
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
                        have h1 := storeTcbQueueLinks_notification_backward _ _ tid none none none oid ntfn hFinal hNtfn
                        by_cases hEqId : oid = endpointId
                        · subst hEqId; rw [storeObject_objects_eq _ _ oid _ hStore2] at h1; cases h1
                        · rw [storeObject_objects_ne stPrev pair2.2 endpointId oid _ hEqId hStore2] at h1
                          exact storeTcbQueueLinks_notification_backward _ _ prevTid _ _ _ oid ntfn hLink0 h1
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
                        have h1 := storeTcbQueueLinks_notification_backward _ _ tid none none none oid ntfn hFinal hNtfn
                        by_cases hEqId : oid = endpointId
                        · subst hEqId; rw [storeObject_objects_eq _ _ oid _ hStore2] at h1; cases h1
                        · rw [storeObject_objects_ne st2 pair2.2 endpointId oid _ hEqId hStore2] at h1
                          have h2 := storeTcbQueueLinks_notification_backward _ _ nextTid _ _ _ oid ntfn hLink1 h1
                          exact storeTcbQueueLinks_notification_backward _ _ prevTid _ _ _ oid ntfn hLink0 h2

/-- WS-F1/TPI-D08: Backward TCB ipcState transport for endpointQueueRemoveDual.
endpointQueueRemoveDual only calls storeObject (for endpoints) and
storeTcbQueueLinks (which preserves ipcState). Therefore any TCB
present in the post-state has the same ipcState as in the pre-state. -/
theorem endpointQueueRemoveDual_tcb_ipcState_backward
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (anyTid : SeLe4n.ThreadId) (tcb' : TCB)
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
                simp only []; cases hNext : tcbTid.queueNext with
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
                    obtain ⟨tcb3, hTcb3, hIpc3⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ tid _ _ _ hFinal anyTid tcb' hTcb'
                    by_cases hEqEp : anyTid.toObjId = endpointId
                    · rw [hEqEp, storeObject_objects_eq _ _ endpointId _ hStore2] at hTcb3; cases hTcb3
                    · rw [storeObject_objects_ne _ _ endpointId anyTid.toObjId _ hEqEp hStore2] at hTcb3
                      by_cases hEqEp2 : anyTid.toObjId = endpointId
                      · exact absurd hEqEp2 hEqEp
                      · rw [storeObject_objects_ne _ _ endpointId anyTid.toObjId _ hEqEp2 hStore1] at hTcb3
                        exact ⟨tcb3, hTcb3, hIpc3⟩
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
                    obtain ⟨tcb4, hTcb4, hIpc4⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ tid _ _ _ hFinal anyTid tcb' hTcb'
                    by_cases hEqEp : anyTid.toObjId = endpointId
                    · rw [hEqEp, storeObject_objects_eq _ _ endpointId _ hStore2] at hTcb4; cases hTcb4
                    · rw [storeObject_objects_ne _ _ endpointId anyTid.toObjId _ hEqEp hStore2] at hTcb4
                      obtain ⟨tcb2, hTcb2, hIpc2⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ nextTid _ _ _ hLink anyTid tcb4 hTcb4
                      by_cases hEqEp2 : anyTid.toObjId = endpointId
                      · exact absurd hEqEp2 hEqEp
                      · rw [storeObject_objects_ne _ _ endpointId anyTid.toObjId _ hEqEp2 hStore1] at hTcb2
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
                    cases hNext : tcbTid.queueNext with
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
                        obtain ⟨tcb3, hTcb3, hIpc3⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ tid _ _ _ hFinal anyTid tcb' hTcb'
                        by_cases hEqEp : anyTid.toObjId = endpointId
                        · rw [hEqEp, storeObject_objects_eq _ _ endpointId _ hStore2] at hTcb3; cases hTcb3
                        · rw [storeObject_objects_ne _ _ endpointId anyTid.toObjId _ hEqEp hStore2] at hTcb3
                          obtain ⟨tcb1, hTcb1, hIpc1⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ prevTid _ _ _ hLink0 anyTid tcb3 hTcb3
                          exact ⟨tcb1, hTcb1, hIpc1.trans hIpc3⟩
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
                        obtain ⟨tcb4, hTcb4, hIpc4⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ tid _ _ _ hFinal anyTid tcb' hTcb'
                        by_cases hEqEp : anyTid.toObjId = endpointId
                        · rw [hEqEp, storeObject_objects_eq _ _ endpointId _ hStore2] at hTcb4; cases hTcb4
                        · rw [storeObject_objects_ne _ _ endpointId anyTid.toObjId _ hEqEp hStore2] at hTcb4
                          obtain ⟨tcb2, hTcb2, hIpc2⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ nextTid _ _ _ hLink1 anyTid tcb4 hTcb4
                          obtain ⟨tcb1, hTcb1, hIpc1⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ prevTid _ _ _ hLink0 anyTid tcb2 hTcb2
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
    match st.objects[endpointId]? with
    | some (.endpoint ep) =>
        match ep.receiveQ.head with
        | some _ =>
            match endpointQueuePopHead endpointId true st with
            | .error e => .error e
            | .ok (receiver, st') =>
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
            match endpointQueuePopHead endpointId false st with
            | .error e => .error e
            | .ok (sender, st') =>
                -- WS-F1/WS-H1: Extract message and IPC state from sender's TCB in a single lookup.
                -- blockedOnCall → blockedOnReply (caller stays blocked awaiting reply)
                -- blockedOnSend → ready (plain send, unblock sender)
                let (senderMsg, senderWasCall) := match lookupTcb st' sender with
                  | some tcb => (tcb.pendingMessage, match tcb.ipcState with
                    | .blockedOnCall _ => true
                    | _ => false)
                  | none => (none, false)
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
    match st.objects[endpointId]? with
    | some (.endpoint ep) =>
        match ep.receiveQ.head with
        | some _ =>
            match endpointQueuePopHead endpointId true st with
            | .error e => .error e
            | .ok (receiver, st') =>
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
              match storeTcbIpcStateAndMessage st target .ready (some msg) with
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
              -- WS-F1: Deliver reply message and unblock target
              match storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
              | .error e => .error e
              | .ok st' =>
                  let st'' := ensureRunnable st' replyTarget
                  -- WS-H12a: Full dual-queue receive path after reply
                  match endpointReceiveDual endpointId receiver st'' with
                  | .error e => .error e
                  | .ok (_, st''') => .ok ((), st''')
            else .error .replyCapInvalid
        | _ => .error .replyCapInvalid


end SeLe4n.Kernel
