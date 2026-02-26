import SeLe4n.Model.State

namespace SeLe4n.Kernel

open SeLe4n.Model

def removeRunnable (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  { st with
      scheduler := {
        st.scheduler with
          runnable := st.scheduler.runnable.filter (· ≠ tid)
          current := if st.scheduler.current = some tid then none else st.scheduler.current
      }
  }

def ensureRunnable (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  if tid ∈ st.scheduler.runnable then
    st
  else
    match st.objects tid.toObjId with
    | some (.tcb _) =>
        { st with scheduler := { st.scheduler with runnable := st.scheduler.runnable ++ [tid] } }
    | _ => st

def lookupTcb (st : SystemState) (tid : SeLe4n.ThreadId) : Option TCB :=
  match st.objects tid.toObjId with
  | some (.tcb tcb) => some tcb
  | _ => none

def storeTcbIpcState (st : SystemState) (tid : SeLe4n.ThreadId) (ipcState : ThreadIpcState) : Except KernelError SystemState :=
  match lookupTcb st tid with
  | none => .error .objectNotFound
  | some tcb =>
      match storeObject tid.toObjId (.tcb { tcb with ipcState := ipcState }) st with
      | .error e => .error e
      | .ok ((), st') => .ok st'

/-- Add a sender to an endpoint wait queue with explicit state transition.

WS-E3/H-09: Thread IPC state transitions are now enforced:
- **Blocking paths** (idle→send, send→send): the sender's IPC state is set to
  `.blockedOnSend endpointId` and the sender is removed from the runnable queue.
- **Handshake path** (receive→idle): the waiting receiver is unblocked — IPC state
  set to `.ready` and added to the runnable queue. The sender does not block. -/
def endpointSend (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) : Kernel Unit :=
  fun st =>
    match st.objects endpointId with
    | some (.endpoint ep) =>
        match ep.state with
        | .idle =>
            let ep' : Endpoint := { state := .send, queue := [sender], waitingReceiver := none }
            match storeObject endpointId (.endpoint ep') st with
            | .error e => .error e
            | .ok ((), st') =>
                match storeTcbIpcState st' sender (.blockedOnSend endpointId) with
                | .error e => .error e
                | .ok st'' => .ok ((), removeRunnable st'' sender)
        | .send =>
            let ep' : Endpoint := { state := .send, queue := ep.queue ++ [sender], waitingReceiver := none }
            match storeObject endpointId (.endpoint ep') st with
            | .error e => .error e
            | .ok ((), st') =>
                match storeTcbIpcState st' sender (.blockedOnSend endpointId) with
                | .error e => .error e
                | .ok st'' => .ok ((), removeRunnable st'' sender)
        | .receive =>
            match ep.queue, ep.waitingReceiver with
            | [], some receiver =>
                let ep' : Endpoint := { state := .idle, queue := [], waitingReceiver := none }
                match storeObject endpointId (.endpoint ep') st with
                | .error e => .error e
                | .ok ((), st') =>
                    match storeTcbIpcState st' receiver .ready with
                    | .error e => .error e
                    | .ok st'' => .ok ((), ensureRunnable st'' receiver)
            | _, _ => .error .endpointStateMismatch
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

/-- Register one waiting receiver on an idle endpoint.

WS-E3/H-09: After registration, the receiver's IPC state is set to
`.blockedOnReceive endpointId` and the receiver is removed from the runnable queue.
This makes the `blockedOnReceiveNotRunnable` contract predicate non-vacuous. -/
def endpointAwaitReceive (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) : Kernel Unit :=
  fun st =>
    match st.objects endpointId with
    | some (.endpoint ep) =>
        match ep.state, ep.queue, ep.waitingReceiver with
        | .idle, [], none =>
            let ep' : Endpoint := { state := .receive, queue := [], waitingReceiver := some receiver }
            match storeObject endpointId (.endpoint ep') st with
            | .error e => .error e
            | .ok ((), st') =>
                match storeTcbIpcState st' receiver (.blockedOnReceive endpointId) with
                | .error e => .error e
                | .ok st'' => .ok ((), removeRunnable st'' receiver)
        | .idle, _, _ => .error .endpointStateMismatch
        | .send, _, _ => .error .endpointStateMismatch
        | .receive, _, _ => .error .endpointStateMismatch
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

/-- Consume one queued sender from an endpoint wait queue.

WS-E3/H-09: After dequeuing a sender, the sender's IPC state is set to `.ready`
and the sender is added to the runnable queue. This unblocks the sender that was
previously blocked by `endpointSend`. -/
def endpointReceive (endpointId : SeLe4n.ObjId) : Kernel SeLe4n.ThreadId :=
  fun st =>
    match st.objects endpointId with
    | some (.endpoint ep) =>
        match ep.state, ep.queue, ep.waitingReceiver with
        | .send, sender :: rest, none =>
            let nextState : EndpointState := if rest.isEmpty then .idle else .send
            let ep' : Endpoint := { state := nextState, queue := rest, waitingReceiver := none }
            match storeObject endpointId (.endpoint ep') st with
            | .error e => .error e
            | .ok ((), st') =>
                match storeTcbIpcState st' sender .ready with
                | .error e => .error e
                | .ok st'' => .ok (sender, ensureRunnable st'' sender)
        | .send, [], none => .error .endpointQueueEmpty
        | .send, _, some _ => .error .endpointStateMismatch
        | .idle, _, _ => .error .endpointStateMismatch
        | .receive, _, _ => .error .endpointStateMismatch
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

/-- Signal a notification: wake one waiter or mark one pending badge. -/
def notificationSignal (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) : Kernel Unit :=
  fun st =>
    match st.objects notificationId with
    | some (.notification ntfn) =>
        match ntfn.waitingThreads with
        | waiter :: rest =>
            let nextState : NotificationState := if rest.isEmpty then .idle else .waiting
            let ntfn' : Notification := {
              state := nextState
              waitingThreads := rest
              pendingBadge := none
            }
            match storeObject notificationId (.notification ntfn') st with
            | .error e => .error e
            | .ok ((), st') =>
                match storeTcbIpcState st' waiter .ready with
                | .error e => .error e
                | .ok st'' => .ok ((), ensureRunnable st'' waiter)
        | [] =>
            let mergedBadge : SeLe4n.Badge :=
              match ntfn.pendingBadge with
              | some existing => SeLe4n.Badge.ofNat (existing.toNat ||| badge.toNat)
              | none => badge
            let ntfn' : Notification := {
              state := .active
              waitingThreads := []
              pendingBadge := some mergedBadge
            }
            storeObject notificationId (.notification ntfn') st
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

/-- Wait on a notification: consume pending badge or block the caller.

WS-D4/F-12: Before appending a thread to the waiting list, checks whether
the thread is already present. Returns `alreadyWaiting` if so, preventing
duplicate entries and ensuring the waiting list remains duplicate-free. -/
def notificationWait
    (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) : Kernel (Option SeLe4n.Badge) :=
  fun st =>
    match st.objects notificationId with
    | some (.notification ntfn) =>
        match ntfn.pendingBadge with
        | some badge =>
            let ntfn' : Notification := { state := .idle, waitingThreads := [], pendingBadge := none }
            match storeObject notificationId (.notification ntfn') st with
            | .error e => .error e
            | .ok ((), st') =>
                match storeTcbIpcState st' waiter .ready with
                | .error e => .error e
                | .ok st'' => .ok (some badge, st'')
        | none =>
            -- F-12: Reject if waiter is already in the waiting list
            if waiter ∈ ntfn.waitingThreads then
              .error .alreadyWaiting
            else
              let ntfn' : Notification := {
                state := .waiting
                waitingThreads := ntfn.waitingThreads ++ [waiter]
                pendingBadge := none
              }
              match storeObject notificationId (.notification ntfn') st with
              | .error e => .error e
              | .ok ((), st') =>
                  match storeTcbIpcState st' waiter (.blockedOnNotification notificationId) with
                  | .error e => .error e
                  | .ok st'' => .ok (none, removeRunnable st'' waiter)
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

-- ============================================================================
-- F-12: Supporting lemmas for notification waiting-list proofs (WS-D4)
-- ============================================================================

/-- `storeTcbIpcState` preserves objects at IDs other than `tid.toObjId`. -/
theorem storeTcbIpcState_preserves_objects_ne
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (oid : SeLe4n.ObjId)
    (hNe : oid ≠ tid.toObjId)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.objects oid = st.objects oid := by
  unfold storeTcbIpcState at hStep
  cases hTcb : lookupTcb st tid with
  | none =>
    have hImpossible : False := by
      simpa [storeTcbIpcState, hTcb] using hStep
    exact False.elim hImpossible
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => cases hStore
    | ok pair =>
      simp only [hStore] at hStep
      have hEq : pair.snd = st' := Except.ok.inj hStep
      subst hEq
      exact storeObject_objects_ne st pair.2 tid.toObjId oid
        (.tcb { tcb with ipcState := ipc }) hNe hStore

/-- `storeTcbIpcState` preserves notification objects (it only writes TCBs). -/
theorem storeTcbIpcState_preserves_notification
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (notifId : SeLe4n.ObjId)
    (ntfn : Notification)
    (hNtfn : st.objects notifId = some (.notification ntfn))
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.objects notifId = some (.notification ntfn) := by
  by_cases hEq : notifId = tid.toObjId
  · subst hEq
    unfold storeTcbIpcState at hStep
    have hLookup : lookupTcb st tid = none := by
      unfold lookupTcb; simp [hNtfn]
    rw [hLookup] at hStep
    cases hStep
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc notifId hEq hStep]
    exact hNtfn

/-- `removeRunnable` only modifies the scheduler; all objects are preserved. -/
theorem removeRunnable_preserves_objects
    (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    (removeRunnable st tid).objects = st.objects := by
  rfl

/-- WS-E3/H-09: `ensureRunnable` only modifies the scheduler; all objects are preserved. -/
theorem ensureRunnable_preserves_objects
    (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    (ensureRunnable st tid).objects = st.objects := by
  unfold ensureRunnable
  split
  · rfl
  · split <;> rfl

/-- WS-E3/H-09: `storeTcbIpcState` does not modify the scheduler. -/
theorem storeTcbIpcState_scheduler_eq
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.scheduler = st.scheduler := by
  unfold storeTcbIpcState at hStep
  cases hTcb : lookupTcb st tid with
  | none =>
    have hImpossible : False := by
      simpa [storeTcbIpcState, hTcb] using hStep
    exact False.elim hImpossible
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => cases hStore
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep
      subst hEq
      exact storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore

/-- WS-E3/H-09: `storeTcbIpcState` preserves endpoint objects. -/
theorem storeTcbIpcState_preserves_endpoint
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (epId : SeLe4n.ObjId)
    (ep : Endpoint)
    (hEp : st.objects epId = some (.endpoint ep))
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.objects epId = some (.endpoint ep) := by
  by_cases hEq : epId = tid.toObjId
  · subst hEq
    unfold storeTcbIpcState at hStep
    have hLookup : lookupTcb st tid = none := by
      unfold lookupTcb; simp [hEp]
    rw [hLookup] at hStep
    cases hStep
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc epId hEq hStep]
    exact hEp

/-- WS-E3/H-09: `storeTcbIpcState` preserves CNode objects. -/
theorem storeTcbIpcState_preserves_cnode
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (cnodeId : SeLe4n.ObjId)
    (cn : CNode)
    (hCn : st.objects cnodeId = some (.cnode cn))
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.objects cnodeId = some (.cnode cn) := by
  by_cases hEq : cnodeId = tid.toObjId
  · subst hEq
    unfold storeTcbIpcState at hStep
    have hLookup : lookupTcb st tid = none := by
      unfold lookupTcb; simp [hCn]
    rw [hLookup] at hStep
    cases hStep
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc cnodeId hEq hStep]
    exact hCn

/-- WS-E3/H-09: `storeTcbIpcState` preserves VSpaceRoot objects. -/
theorem storeTcbIpcState_preserves_vspaceRoot
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (oid : SeLe4n.ObjId)
    (vs : VSpaceRoot)
    (hVs : st.objects oid = some (.vspaceRoot vs))
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.objects oid = some (.vspaceRoot vs) := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq
    unfold storeTcbIpcState at hStep
    have hLookup : lookupTcb st tid = none := by
      unfold lookupTcb; simp [hVs]
    rw [hLookup] at hStep
    cases hStep
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc oid hEq hStep]
    exact hVs

/-- WS-E3/H-09: Backward CNode preservation: if post-state has a CNode, pre-state had it.
`storeTcbIpcState` only writes TCBs, so it cannot create or modify CNode objects. -/
theorem storeTcbIpcState_cnode_backward
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (oid : SeLe4n.ObjId)
    (cn : CNode)
    (hStep : storeTcbIpcState st tid ipc = .ok st')
    (hCn : st'.objects oid = some (.cnode cn)) :
    st.objects oid = some (.cnode cn) := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq
    unfold storeTcbIpcState at hStep
    cases hLookup : lookupTcb st tid with
    | none =>
      have hImpossible : False := by
        simpa [storeTcbIpcState, hLookup] using hStep
      exact False.elim hImpossible
    | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
      | error e => cases hStore
      | ok pair =>
        simp only [hStore] at hStep
        have := Except.ok.inj hStep; subst this
        rw [storeObject_objects_eq st pair.2 tid.toObjId _ hStore] at hCn; cases hCn
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc oid hEq hStep] at hCn; exact hCn

/-- WS-E3/H-09: Backward endpoint preservation for `storeTcbIpcState`. -/
theorem storeTcbIpcState_endpoint_backward
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (oid : SeLe4n.ObjId)
    (ep : Endpoint)
    (hStep : storeTcbIpcState st tid ipc = .ok st')
    (hEp : st'.objects oid = some (.endpoint ep)) :
    st.objects oid = some (.endpoint ep) := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq
    unfold storeTcbIpcState at hStep
    cases hLookup : lookupTcb st tid with
    | none =>
      have hImpossible : False := by
        simpa [storeTcbIpcState, hLookup] using hStep
      exact False.elim hImpossible
    | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
      | error e => cases hStore
      | ok pair =>
        simp only [hStore] at hStep
        have := Except.ok.inj hStep; subst this
        rw [storeObject_objects_eq st pair.2 tid.toObjId _ hStore] at hEp; cases hEp
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc oid hEq hStep] at hEp; exact hEp

/-- WS-E3/H-09: Backward notification preservation for `storeTcbIpcState`. -/
theorem storeTcbIpcState_notification_backward
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (oid : SeLe4n.ObjId)
    (ntfn : Notification)
    (hStep : storeTcbIpcState st tid ipc = .ok st')
    (hNtfn : st'.objects oid = some (.notification ntfn)) :
    st.objects oid = some (.notification ntfn) := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq
    unfold storeTcbIpcState at hStep
    cases hLookup : lookupTcb st tid with
    | none =>
      have hImpossible : False := by
        simpa [storeTcbIpcState, hLookup] using hStep
      exact False.elim hImpossible
    | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
      | error e => cases hStore
      | ok pair =>
        simp only [hStore] at hStep
        have := Except.ok.inj hStep; subst this
        rw [storeObject_objects_eq st pair.2 tid.toObjId _ hStore] at hNtfn; cases hNtfn
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc oid hEq hStep] at hNtfn; exact hNtfn

/-- Double-wait is rejected: if the thread is already waiting,
`notificationWait` returns `alreadyWaiting`. -/
theorem notificationWait_error_alreadyWaiting
    (waiter : SeLe4n.ThreadId)
    (notifId : SeLe4n.ObjId)
    (st : SystemState)
    (ntfn : Notification)
    (hObj : st.objects notifId = some (.notification ntfn))
    (hNoBadge : ntfn.pendingBadge = none)
    (hMem : waiter ∈ ntfn.waitingThreads) :
    notificationWait notifId waiter st = .error .alreadyWaiting := by
  unfold notificationWait
  simp [hObj, hNoBadge, hMem]

/-- Decomposition: on the badge-consumed path, the post-state notification
has an empty waiting list. -/
theorem notificationWait_badge_path_notification
    (st st' : SystemState)
    (notifId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId)
    (badge : SeLe4n.Badge)
    (hStep : notificationWait notifId waiter st = .ok (some badge, st')) :
    ∃ ntfn', st'.objects notifId = some (.notification ntfn') ∧ ntfn'.waitingThreads = [] := by
  unfold notificationWait at hStep
  cases hObj : st.objects notifId with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hBadge : ntfn.pendingBadge with
      | none =>
        simp only [hBadge] at hStep
        split at hStep
        · simp at hStep
        · revert hStep
          cases hStore : storeObject notifId _ st with
          | error e => simp
          | ok pair =>
            simp only []
            intro hStep
            revert hStep
            cases hTcb : storeTcbIpcState pair.2 waiter _ with
            | error e => simp
            | ok st2 =>
              simp only [Except.ok.injEq, Prod.mk.injEq]
              intro ⟨h, _⟩
              exact absurd h (by simp)
      | some b =>
        simp only [hBadge] at hStep
        let newNtfn : Notification := { state := .idle, waitingThreads := [], pendingBadge := none }
        revert hStep
        cases hStore : storeObject notifId (.notification newNtfn) st with
        | error e => simp
        | ok pair =>
          simp only []
          intro hStep
          revert hStep
          cases hTcb : storeTcbIpcState pair.2 waiter .ready with
          | error e => simp
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hStEq⟩
            subst hStEq
            have hNtfnStored : pair.2.objects notifId = some (.notification newNtfn) :=
              storeObject_objects_eq st pair.2 notifId (.notification newNtfn) hStore
            have hNtfnPreserved : st2.objects notifId = some (.notification newNtfn) :=
              storeTcbIpcState_preserves_notification pair.2 st2 waiter .ready notifId newNtfn hNtfnStored hTcb
            exact ⟨newNtfn, hNtfnPreserved, rfl⟩

/-- Decomposition: on the wait path, the post-state notification has the
waiter appended, and the waiter was not already in the pre-state list. -/
theorem notificationWait_wait_path_notification
    (st st' : SystemState)
    (notifId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId)
    (hStep : notificationWait notifId waiter st = .ok (none, st')) :
    ∃ ntfn ntfn',
      st.objects notifId = some (.notification ntfn) ∧
      ntfn.pendingBadge = none ∧
      waiter ∉ ntfn.waitingThreads ∧
      st'.objects notifId = some (.notification ntfn') ∧
      ntfn'.waitingThreads = ntfn.waitingThreads ++ [waiter] := by
  unfold notificationWait at hStep
  cases hObj : st.objects notifId with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hBadge : ntfn.pendingBadge with
      | some b =>
        simp only [hBadge] at hStep
        revert hStep
        cases hStore : storeObject notifId (.notification { state := .idle, waitingThreads := [], pendingBadge := none }) st with
        | error e => simp
        | ok pair =>
          simp only []
          intro hStep
          revert hStep
          cases hTcb : storeTcbIpcState pair.2 waiter .ready with
          | error e => simp
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨h, _⟩
            exact absurd h (by simp)
      | none =>
        simp only [hBadge] at hStep
        by_cases hMem : waiter ∈ ntfn.waitingThreads
        · simp [hMem] at hStep
        · simp only [hMem, ite_false] at hStep
          let ntfn' : Notification := { state := .waiting, waitingThreads := ntfn.waitingThreads ++ [waiter], pendingBadge := none }
          revert hStep
          cases hStore : storeObject notifId (.notification ntfn') st with
          | error e => simp
          | ok pair =>
            simp only []
            intro hStep
            revert hStep
            cases hTcb : storeTcbIpcState pair.2 waiter (.blockedOnNotification notifId) with
            | error e => simp
            | ok st2 =>
              simp only [Except.ok.injEq, Prod.mk.injEq]
              intro ⟨_, hStEq⟩
              have hRemObj : (removeRunnable st2 waiter).objects = st2.objects := rfl
              have hNtfnStored : pair.2.objects notifId = some (.notification ntfn') :=
                storeObject_objects_eq st pair.2 notifId (.notification ntfn') hStore
              have hNtfnPreserved : st2.objects notifId = some (.notification ntfn') :=
                storeTcbIpcState_preserves_notification pair.2 st2 waiter
                  (.blockedOnNotification notifId) notifId ntfn' hNtfnStored hTcb
              refine ⟨ntfn, ntfn', rfl, hBadge, hMem, ?_, rfl⟩
              rw [← hStEq, hRemObj]
              exact hNtfnPreserved

-- ============================================================================
-- WS-E3/H-09: Scheduler lemmas for removeRunnable and ensureRunnable
-- ============================================================================

theorem removeRunnable_scheduler_current
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeRunnable st tid).scheduler.current =
      if st.scheduler.current = some tid then none else st.scheduler.current := by
  rfl

theorem removeRunnable_mem
    (st : SystemState) (tid x : SeLe4n.ThreadId) :
    x ∈ (removeRunnable st tid).scheduler.runnable ↔ x ∈ st.scheduler.runnable ∧ x ≠ tid := by
  simp [removeRunnable, List.mem_filter]

theorem removeRunnable_nodup
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hNodup : st.scheduler.runnable.Nodup) :
    (removeRunnable st tid).scheduler.runnable.Nodup := by
  exact hNodup.sublist List.filter_sublist

theorem ensureRunnable_scheduler_current
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (ensureRunnable st tid).scheduler.current = st.scheduler.current := by
  unfold ensureRunnable
  split
  · rfl
  · split <;> rfl

theorem ensureRunnable_mem_self
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hTcb : ∃ tcb, st.objects tid.toObjId = some (.tcb tcb)) :
    tid ∈ (ensureRunnable st tid).scheduler.runnable := by
  obtain ⟨tcb, hTcb⟩ := hTcb
  unfold ensureRunnable
  split
  · assumption
  · simp only [hTcb]; simp [List.mem_append]

theorem ensureRunnable_mem_old
    (st : SystemState) (tid x : SeLe4n.ThreadId)
    (hMem : x ∈ st.scheduler.runnable) :
    x ∈ (ensureRunnable st tid).scheduler.runnable := by
  unfold ensureRunnable
  split
  · exact hMem
  · split
    · exact List.mem_append_left _ hMem
    · exact hMem

theorem ensureRunnable_nodup
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hNodup : st.scheduler.runnable.Nodup) :
    (ensureRunnable st tid).scheduler.runnable.Nodup := by
  unfold ensureRunnable
  split
  · exact hNodup
  · rename_i hNotMem
    split
    · rw [List.nodup_append]
      refine ⟨hNodup, ?_, ?_⟩
      · exact .cons (fun _ h => absurd h List.not_mem_nil) .nil
      · intro x hxl y hya
        rw [List.mem_singleton] at hya; subst hya
        exact fun heq => hNotMem (heq ▸ hxl)
    · exact hNodup

/-- Alias referencing the canonical `ThreadId.toObjId_injective` in Prelude. -/
theorem threadId_toObjId_injective {a b : SeLe4n.ThreadId}
    (h : a.toObjId = b.toObjId) : a = b :=
  SeLe4n.ThreadId.toObjId_injective a b h

/-- WS-E3/H-09: If `storeTcbIpcState st tid ipc` succeeds and the post-state has a TCB
    at `tid.toObjId`, then that TCB has `ipcState = ipc`. Covers both the case where
    lookupTcb found an existing TCB (which was updated) and the no-op case (which leads
    to contradiction since lookupTcb failing means no TCB at tid). -/
theorem storeTcbIpcState_ipcState_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hStep : storeTcbIpcState st tid ipc = .ok st')
    (tcb : TCB) (hTcb : st'.objects tid.toObjId = some (.tcb tcb)) :
    tcb.ipcState = ipc := by
  unfold storeTcbIpcState at hStep
  cases hLookup : lookupTcb st tid with
  | none =>
    have hImpossible : False := by
      simpa [storeTcbIpcState, hLookup] using hStep
    exact False.elim hImpossible
  | some tcb' =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb' with ipcState := ipc }) st with
    | error e => cases hStore
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep; subst hEq
      have hAt := storeObject_objects_eq st pair.2 tid.toObjId _ hStore
      rw [hAt] at hTcb; cases hTcb; rfl

/-- WS-E3/H-09: Reverse membership for ensureRunnable. If a thread is in the runnable
    queue after ensureRunnable, it was either already there or it is the added thread. -/
theorem ensureRunnable_mem_reverse
    (st : SystemState) (tid x : SeLe4n.ThreadId)
    (hMem : x ∈ (ensureRunnable st tid).scheduler.runnable) :
    x ∈ st.scheduler.runnable ∨ x = tid := by
  unfold ensureRunnable at hMem
  split at hMem
  · exact .inl hMem
  · split at hMem
    · rw [List.mem_append, List.mem_singleton] at hMem; exact hMem
    · exact .inl hMem

/-- WS-E3/H-09: A thread is never in its own removeRunnable result. -/
theorem removeRunnable_not_mem_self
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    tid ∉ (removeRunnable st tid).scheduler.runnable := by
  rw [removeRunnable_mem]; simp

/-- WS-E3/H-09: If a TCB exists at `tid.toObjId` in the pre-state, then a TCB still
    exists there after `storeTcbIpcState` (though the ipcState may have changed). -/
theorem storeTcbIpcState_tcb_exists_at_target
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hStep : storeTcbIpcState st tid ipc = .ok st')
    (hTcb : ∃ tcb, st.objects tid.toObjId = some (.tcb tcb)) :
    ∃ tcb', st'.objects tid.toObjId = some (.tcb tcb') := by
  rcases hTcb with ⟨tcb, hObj⟩
  unfold storeTcbIpcState at hStep
  have hLookup : lookupTcb st tid = some tcb := by unfold lookupTcb; simp [hObj]
  simp only [hLookup] at hStep
  cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
  | error e => cases hStore
  | ok pair =>
    simp only [hStore] at hStep
    have := Except.ok.inj hStep; subst this
    exact ⟨{ tcb with ipcState := ipc }, storeObject_objects_eq st pair.2 tid.toObjId _ hStore⟩

-- ============================================================================
-- WS-E4/M-01: Dual-queue endpoint operations (send/receive queue separation)
-- ============================================================================

/-- WS-E4/M-01: Send to endpoint using the dual-queue model.

Sender checks receiveQueue first. If a receiver is waiting, rendezvous
(unblock receiver). Otherwise, enqueue sender on sendQueue and block. -/
def endpointSendDual (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    : Kernel Unit :=
  fun st =>
    match st.objects endpointId with
    | some (.endpoint ep) =>
        match ep.receiveQueue with
        | receiver :: restRecv =>
            -- Rendezvous: match sender with first waiting receiver
            let ep' : Endpoint := { ep with receiveQueue := restRecv }
            match storeObject endpointId (.endpoint ep') st with
            | .error e => .error e
            | .ok ((), st') =>
                match storeTcbIpcState st' receiver .ready with
                | .error e => .error e
                | .ok st'' => .ok ((), ensureRunnable st'' receiver)
        | [] =>
            -- No receiver waiting: enqueue sender and block
            let ep' : Endpoint := { ep with sendQueue := ep.sendQueue ++ [sender] }
            match storeObject endpointId (.endpoint ep') st with
            | .error e => .error e
            | .ok ((), st') =>
                match storeTcbIpcState st' sender (.blockedOnSend endpointId) with
                | .error e => .error e
                | .ok st'' => .ok ((), removeRunnable st'' sender)
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

/-- WS-E4/M-01: Receive from endpoint using the dual-queue model.

Checks sendQueue first. If a sender is waiting, dequeue and unblock it.
Otherwise, enqueue receiver on receiveQueue and block. -/
def endpointReceiveDual (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    : Kernel SeLe4n.ThreadId :=
  fun st =>
    match st.objects endpointId with
    | some (.endpoint ep) =>
        match ep.sendQueue with
        | sender :: restSend =>
            -- Rendezvous: dequeue first waiting sender
            let ep' : Endpoint := { ep with sendQueue := restSend }
            match storeObject endpointId (.endpoint ep') st with
            | .error e => .error e
            | .ok ((), st') =>
                match storeTcbIpcState st' sender .ready with
                | .error e => .error e
                | .ok st'' => .ok (sender, ensureRunnable st'' sender)
        | [] =>
            -- No sender waiting: enqueue receiver and block
            let ep' : Endpoint := { ep with receiveQueue := ep.receiveQueue ++ [receiver] }
            match storeObject endpointId (.endpoint ep') st with
            | .error e => .error e
            | .ok ((), st') =>
                match storeTcbIpcState st' receiver (.blockedOnReceive endpointId) with
                | .error e => .error e
                | .ok st'' => .ok (receiver, removeRunnable st'' receiver)
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

-- ============================================================================
-- WS-E4/M-12: Reply operations for bidirectional IPC
-- ============================================================================

/-- WS-E4/M-12: Call operation — send then block for reply.

If a receiver is queued: handshake with receiver, then block caller for reply.
If no receiver queued: enqueue caller as sender (will transition to blockedOnReply
when received). -/
def endpointCall (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    : Kernel Unit :=
  fun st =>
    match st.objects endpointId with
    | some (.endpoint ep) =>
        match ep.receiveQueue with
        | receiver :: restRecv =>
            -- Rendezvous with receiver, then block caller for reply
            let ep' : Endpoint := { ep with receiveQueue := restRecv }
            match storeObject endpointId (.endpoint ep') st with
            | .error e => .error e
            | .ok ((), st') =>
                match storeTcbIpcState st' receiver .ready with
                | .error e => .error e
                | .ok st'' =>
                    let st''' := ensureRunnable st'' receiver
                    match storeTcbIpcState st''' caller (.blockedOnReply endpointId) with
                    | .error e => .error e
                    | .ok st4 => .ok ((), removeRunnable st4 caller)
        | [] =>
            -- No receiver: enqueue as sender, block
            let ep' : Endpoint := { ep with sendQueue := ep.sendQueue ++ [caller] }
            match storeObject endpointId (.endpoint ep') st with
            | .error e => .error e
            | .ok ((), st') =>
                match storeTcbIpcState st' caller (.blockedOnSend endpointId) with
                | .error e => .error e
                | .ok st'' => .ok ((), removeRunnable st'' caller)
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

/-- WS-E4/M-12: Reply to a thread blocked on reply.

Unblocks the target thread by setting its IPC state to ready and adding it
to the runnable queue. Fails if the target is not in blockedOnReply state. -/
def endpointReply (target : SeLe4n.ThreadId) : Kernel Unit :=
  fun st =>
    match lookupTcb st target with
    | none => .error .objectNotFound
    | some tcb =>
        match tcb.ipcState with
        | .blockedOnReply _ =>
            match storeTcbIpcState st target .ready with
            | .error e => .error e
            | .ok st' => .ok ((), ensureRunnable st' target)
        | _ => .error .replyCapInvalid

/-- WS-E4/M-12: Reply to a caller, then await receive on the endpoint.

Combines reply + receive in a single atomic operation, matching seL4_ReplyRecv.
The reply unblocks the target, then the receiver waits on the endpoint. -/
def endpointReplyRecv
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (replyTarget : SeLe4n.ThreadId) : Kernel Unit :=
  fun st =>
    match lookupTcb st replyTarget with
    | none => .error .objectNotFound
    | some tcb =>
        match tcb.ipcState with
        | .blockedOnReply _ =>
            match storeTcbIpcState st replyTarget .ready with
            | .error e => .error e
            | .ok st' =>
                let st'' := ensureRunnable st' replyTarget
                match endpointAwaitReceive endpointId receiver st'' with
                | .error e => .error e
                | .ok result => .ok result
        | _ => .error .replyCapInvalid

end SeLe4n.Kernel
