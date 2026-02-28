import SeLe4n.Model.State

namespace SeLe4n.Kernel

open SeLe4n.Model

def removeRunnable (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  let runnable' := st.scheduler.runnable.filter (· ≠ tid)
  { st with
      scheduler := {
        st.scheduler.withRunnableQueue runnable' with
          current := if st.scheduler.current = some tid then none else st.scheduler.current
      }
  }

def ensureRunnable (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  if tid ∈ st.scheduler.runnable then
    st
  else
    match st.objects tid.toObjId with
    | some (.tcb _) =>
        let runnable' := st.scheduler.runnable ++ [tid]
        { st with scheduler := st.scheduler.withRunnableQueue runnable' }
    | _ => st

def lookupTcb (st : SystemState) (tid : SeLe4n.ThreadId) : Option TCB :=
  if tid.isReserved then
    none
  else
    match st.objects tid.toObjId with
    | some (.tcb tcb) => some tcb
    | _ => none

/-- If lookupTcb succeeds, the underlying objects map has a TCB at tid.toObjId. -/
theorem lookupTcb_some_objects
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (h : lookupTcb st tid = some tcb) :
    st.objects tid.toObjId = some (.tcb tcb) := by
  unfold lookupTcb at h
  cases hRes : tid.isReserved
  · -- false
    simp [hRes] at h; revert h
    cases hObj : st.objects tid.toObjId with
    | none => simp
    | some obj => cases obj <;> simp
  · -- true: contradiction
    simp [hRes] at h

def storeTcbIpcState (st : SystemState) (tid : SeLe4n.ThreadId) (ipcState : ThreadIpcState) : Except KernelError SystemState :=
  match lookupTcb st tid with
  | none => .error .objectNotFound
  | some tcb =>
      match storeObject tid.toObjId (.tcb { tcb with ipcState := ipcState }) st with
      | .error e => .error e
      | .ok ((), st') => .ok st'

/-- WS-F1: Store a pending IPC message in a thread's TCB.
Used during IPC send to stage the message for transfer. -/
def storeTcbPendingMessage (st : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage) : Except KernelError SystemState :=
  match lookupTcb st tid with
  | none => .error .objectNotFound
  | some tcb =>
      match storeObject tid.toObjId (.tcb { tcb with pendingMessage := msg }) st with
      | .error e => .error e
      | .ok ((), st') => .ok st'

/-- WS-F1: Combined store of IPC state and pending message in a single TCB update.
Avoids two separate storeObject calls and simplifies proof tracking. -/
def storeTcbIpcStateAndMessage (st : SystemState) (tid : SeLe4n.ThreadId)
    (ipcState : ThreadIpcState) (msg : Option IpcMessage) : Except KernelError SystemState :=
  match lookupTcb st tid with
  | none => .error .objectNotFound
  | some tcb =>
      match storeObject tid.toObjId (.tcb { tcb with ipcState := ipcState, pendingMessage := msg }) st with
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
    simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => simp [hStore] at hStep
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
    simp [hLookup] at hStep
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
    simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => simp [hStore] at hStep
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
    simp [hLookup] at hStep
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
    simp [hLookup] at hStep
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
    simp [hLookup] at hStep
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
      simp [hLookup] at hStep;
    | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
      | error e => simp [hStore] at hStep
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
      simp [hLookup] at hStep;
    | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
      | error e => simp [hStore] at hStep
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
      simp [hLookup] at hStep
    | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
      | error e => simp [hStore] at hStep
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
  simp [removeRunnable, SchedulerState.withRunnableQueue, List.mem_filter]

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
  · simp [hTcb, SchedulerState.withRunnableQueue, List.mem_append]

theorem ensureRunnable_mem_old
    (st : SystemState) (tid x : SeLe4n.ThreadId)
    (hMem : x ∈ st.scheduler.runnable) :
    x ∈ (ensureRunnable st tid).scheduler.runnable := by
  unfold ensureRunnable
  split
  · exact hMem
  · split
    · simpa [SchedulerState.withRunnableQueue, List.mem_append] using Or.inl hMem
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
    · simp [SchedulerState.withRunnableQueue]
      rw [List.nodup_append]
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
    simp [hLookup] at hStep
  | some tcb' =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb' with ipcState := ipc }) st with
    | error e => simp [hStore] at hStep
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
    · simpa [SchedulerState.withRunnableQueue, List.mem_append, List.mem_singleton] using hMem
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
    (_hTcb : ∃ tcb, st.objects tid.toObjId = some (.tcb tcb)) :
    ∃ tcb', st'.objects tid.toObjId = some (.tcb tcb') := by
  unfold storeTcbIpcState at hStep
  cases hLookup : lookupTcb st tid with
  | none =>
    simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have := Except.ok.inj hStep; subst this
      exact ⟨{ tcb with ipcState := ipc }, storeObject_objects_eq st pair.2 tid.toObjId _ hStore⟩

-- ============================================================================
-- WS-F1: Supporting lemmas for storeTcbIpcStateAndMessage / storeTcbPendingMessage
-- ============================================================================

/-- WS-F1: `storeTcbIpcStateAndMessage` preserves objects at IDs other than `tid.toObjId`. -/
theorem storeTcbIpcStateAndMessage_preserves_objects_ne
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (oid : SeLe4n.ObjId) (hNe : oid ≠ tid.toObjId)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    st'.objects oid = st.objects oid := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hTcb : lookupTcb st tid with
  | none => simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq : pair.snd = st' := Except.ok.inj hStep; subst hEq
      exact storeObject_objects_ne st pair.2 tid.toObjId oid _ hNe hStore

/-- WS-F1: `storeTcbIpcStateAndMessage` does not modify the scheduler. -/
theorem storeTcbIpcStateAndMessage_scheduler_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    st'.scheduler = st.scheduler := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hTcb : lookupTcb st tid with
  | none => simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep; subst hEq
      exact storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore

/-- WS-F1: `storeTcbIpcStateAndMessage` preserves endpoint objects. -/
theorem storeTcbIpcStateAndMessage_preserves_endpoint
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (epId : SeLe4n.ObjId) (ep : Endpoint)
    (hEp : st.objects epId = some (.endpoint ep))
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    st'.objects epId = some (.endpoint ep) := by
  by_cases hEq : epId = tid.toObjId
  · subst hEq
    unfold storeTcbIpcStateAndMessage at hStep
    have hLookup : lookupTcb st tid = none := by unfold lookupTcb; simp [hEp]
    simp [hLookup] at hStep
  · rw [storeTcbIpcStateAndMessage_preserves_objects_ne st st' tid ipc msg epId hEq hStep]; exact hEp

/-- WS-F1: `storeTcbIpcStateAndMessage` preserves notification objects. -/
theorem storeTcbIpcStateAndMessage_preserves_notification
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (notifId : SeLe4n.ObjId) (ntfn : Notification)
    (hNtfn : st.objects notifId = some (.notification ntfn))
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    st'.objects notifId = some (.notification ntfn) := by
  by_cases hEq : notifId = tid.toObjId
  · subst hEq
    unfold storeTcbIpcStateAndMessage at hStep
    have hLookup : lookupTcb st tid = none := by unfold lookupTcb; simp [hNtfn]
    simp [hLookup] at hStep
  · rw [storeTcbIpcStateAndMessage_preserves_objects_ne st st' tid ipc msg notifId hEq hStep]; exact hNtfn

/-- WS-F1: Backward endpoint preservation for `storeTcbIpcStateAndMessage`. -/
theorem storeTcbIpcStateAndMessage_endpoint_backward
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st')
    (hEp : st'.objects oid = some (.endpoint ep)) :
    st.objects oid = some (.endpoint ep) := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq
    unfold storeTcbIpcStateAndMessage at hStep
    cases hLookup : lookupTcb st tid with
    | none => simp [hLookup] at hStep
    | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        simp only [hStore] at hStep
        have := Except.ok.inj hStep; subst this
        rw [storeObject_objects_eq st pair.2 tid.toObjId _ hStore] at hEp; cases hEp
  · rw [storeTcbIpcStateAndMessage_preserves_objects_ne st st' tid ipc msg oid hEq hStep] at hEp; exact hEp

/-- WS-F1: Backward notification preservation for `storeTcbIpcStateAndMessage`. -/
theorem storeTcbIpcStateAndMessage_notification_backward
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st')
    (hNtfn : st'.objects oid = some (.notification ntfn)) :
    st.objects oid = some (.notification ntfn) := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq
    unfold storeTcbIpcStateAndMessage at hStep
    cases hLookup : lookupTcb st tid with
    | none => simp [hLookup] at hStep
    | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        simp only [hStore] at hStep
        have := Except.ok.inj hStep; subst this
        rw [storeObject_objects_eq st pair.2 tid.toObjId _ hStore] at hNtfn; cases hNtfn
  · rw [storeTcbIpcStateAndMessage_preserves_objects_ne st st' tid ipc msg oid hEq hStep] at hNtfn; exact hNtfn

/-- WS-F1: IPC state read-back for `storeTcbIpcStateAndMessage`. -/
theorem storeTcbIpcStateAndMessage_ipcState_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st')
    (tcb : TCB) (hTcb : st'.objects tid.toObjId = some (.tcb tcb)) :
    tcb.ipcState = ipc := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb' =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb' with ipcState := ipc, pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep; subst hEq
      have hAt := storeObject_objects_eq st pair.2 tid.toObjId _ hStore
      rw [hAt] at hTcb; cases hTcb; rfl

/-- WS-F1: TCB existence at target after `storeTcbIpcStateAndMessage`. -/
theorem storeTcbIpcStateAndMessage_tcb_exists_at_target
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st')
    (_hTcb : ∃ tcb, st.objects tid.toObjId = some (.tcb tcb)) :
    ∃ tcb', st'.objects tid.toObjId = some (.tcb tcb') := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have := Except.ok.inj hStep; subst this
      exact ⟨_, storeObject_objects_eq st pair.2 tid.toObjId _ hStore⟩

/-- WS-F1: `storeTcbPendingMessage` preserves objects at IDs other than `tid.toObjId`. -/
theorem storeTcbPendingMessage_preserves_objects_ne
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (msg : Option IpcMessage) (oid : SeLe4n.ObjId) (hNe : oid ≠ tid.toObjId)
    (hStep : storeTcbPendingMessage st tid msg = .ok st') :
    st'.objects oid = st.objects oid := by
  unfold storeTcbPendingMessage at hStep
  cases hTcb : lookupTcb st tid with
  | none => simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq : pair.snd = st' := Except.ok.inj hStep; subst hEq
      exact storeObject_objects_ne st pair.2 tid.toObjId oid _ hNe hStore

/-- WS-F1: `storeTcbPendingMessage` does not modify the scheduler. -/
theorem storeTcbPendingMessage_scheduler_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (msg : Option IpcMessage)
    (hStep : storeTcbPendingMessage st tid msg = .ok st') :
    st'.scheduler = st.scheduler := by
  unfold storeTcbPendingMessage at hStep
  cases hTcb : lookupTcb st tid with
  | none => simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep; subst hEq
      exact storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore

/-- WS-F1: `storeTcbPendingMessage` preserves endpoint objects. -/
theorem storeTcbPendingMessage_preserves_endpoint
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (msg : Option IpcMessage) (epId : SeLe4n.ObjId) (ep : Endpoint)
    (hEp : st.objects epId = some (.endpoint ep))
    (hStep : storeTcbPendingMessage st tid msg = .ok st') :
    st'.objects epId = some (.endpoint ep) := by
  by_cases hEq : epId = tid.toObjId
  · subst hEq; unfold storeTcbPendingMessage at hStep
    have hLookup : lookupTcb st tid = none := by unfold lookupTcb; simp [hEp]
    simp [hLookup] at hStep
  · rw [storeTcbPendingMessage_preserves_objects_ne st st' tid msg epId hEq hStep]; exact hEp

/-- WS-F1: Backward endpoint preservation for `storeTcbPendingMessage`. -/
theorem storeTcbPendingMessage_endpoint_backward
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hStep : storeTcbPendingMessage st tid msg = .ok st')
    (hEp : st'.objects oid = some (.endpoint ep)) :
    st.objects oid = some (.endpoint ep) := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq; unfold storeTcbPendingMessage at hStep
    cases hLookup : lookupTcb st tid with
    | none => simp [hLookup] at hStep
    | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with pendingMessage := msg }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        simp only [hStore] at hStep
        have := Except.ok.inj hStep; subst this
        rw [storeObject_objects_eq st pair.2 tid.toObjId _ hStore] at hEp; cases hEp
  · rw [storeTcbPendingMessage_preserves_objects_ne st st' tid msg oid hEq hStep] at hEp; exact hEp

/-- WS-F1: Backward notification preservation for `storeTcbPendingMessage`. -/
theorem storeTcbPendingMessage_notification_backward
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hStep : storeTcbPendingMessage st tid msg = .ok st')
    (hNtfn : st'.objects oid = some (.notification ntfn)) :
    st.objects oid = some (.notification ntfn) := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq; unfold storeTcbPendingMessage at hStep
    cases hLookup : lookupTcb st tid with
    | none => simp [hLookup] at hStep
    | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with pendingMessage := msg }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        simp only [hStore] at hStep
        have := Except.ok.inj hStep; subst this
        rw [storeObject_objects_eq st pair.2 tid.toObjId _ hStore] at hNtfn; cases hNtfn
  · rw [storeTcbPendingMessage_preserves_objects_ne st st' tid msg oid hEq hStep] at hNtfn; exact hNtfn

/-- WS-F1: storeTcbPendingMessage forward-preserves TCB existence. -/
theorem storeTcbPendingMessage_tcb_forward
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (oid : SeLe4n.ObjId) (tcb : TCB)
    (hStep : storeTcbPendingMessage st tid msg = .ok st')
    (hTcb : st.objects oid = some (.tcb tcb)) :
    ∃ tcb', st'.objects oid = some (.tcb tcb') := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq; unfold storeTcbPendingMessage at hStep
    cases hLookup : lookupTcb st tid with
    | none => simp [hLookup] at hStep
    | some origTcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { origTcb with pendingMessage := msg }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        simp only [hStore] at hStep; have := Except.ok.inj hStep; subst this
        exact ⟨_, storeObject_objects_eq st pair.2 tid.toObjId _ hStore⟩
  · exact ⟨tcb, by rw [storeTcbPendingMessage_preserves_objects_ne st st' tid msg oid hEq hStep]; exact hTcb⟩

/-- WS-F1: storeTcbPendingMessage backward-preserves TCB ipcStates. -/
theorem storeTcbPendingMessage_tcb_ipcState_backward
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (anyTid : SeLe4n.ThreadId) (tcb' : TCB)
    (hStep : storeTcbPendingMessage st tid msg = .ok st')
    (hTcb' : st'.objects anyTid.toObjId = some (.tcb tcb')) :
    ∃ tcb, st.objects anyTid.toObjId = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState := by
  by_cases hEq : anyTid.toObjId = tid.toObjId
  · unfold storeTcbPendingMessage at hStep
    cases hLookup : lookupTcb st tid with
    | none => simp [hLookup] at hStep
    | some origTcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { origTcb with pendingMessage := msg }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        simp only [hStore] at hStep; have := Except.ok.inj hStep; subst this
        rw [hEq, storeObject_objects_eq st pair.2 tid.toObjId _ hStore] at hTcb'
        simp at hTcb'; subst hTcb'
        exact ⟨origTcb, hEq ▸ lookupTcb_some_objects st tid origTcb hLookup, rfl⟩
  · rw [storeTcbPendingMessage_preserves_objects_ne st st' tid msg anyTid.toObjId hEq hStep] at hTcb'
    exact ⟨tcb', hTcb', rfl⟩

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
    st'.objects oid = st.objects oid := by
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
    (hEp : st'.objects oid = some (.endpoint ep)) :
    st.objects oid = some (.endpoint ep) := by
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
    (hNtfn : st'.objects oid = some (.notification ntfn)) :
    st.objects oid = some (.notification ntfn) := by
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
    (hTcb' : st'.objects anyTid.toObjId = some (.tcb tcb')) :
    ∃ tcb, st.objects anyTid.toObjId = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState := by
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
    (hTcb : st.objects oid = some (.tcb tcb)) :
    ∃ tcb', st'.objects oid = some (.tcb tcb') := by
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
  match st.objects endpointId with
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
  match st.objects endpointId with
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
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep; revert hStep
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp [hHead]
      | some headTid =>
        simp only [hHead]
        cases hLookup : lookupTcb st headTid with
        | none => simp [hLookup]
        | some headTcb =>
          simp only [hLookup]
          cases hStore : storeObject endpointId _ st with
          | error e => simp [hStore]
          | ok pair => simp only [hStore]; cases hNext : headTcb.queueNext with
            | none =>
              simp only [hNext]
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp [hFinal]
              | ok st3 =>
                simp only [hFinal, Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                exact (storeTcbQueueLinks_scheduler_eq _ _ headTid none none none hFinal).trans
                  (storeObject_scheduler_eq _ _ endpointId _ hStore)
            | some nextTid =>
              simp only [hNext]
              cases hLookupNext : lookupTcb pair.2 nextTid with
              | none => simp [hLookupNext]
              | some nextTcb =>
                simp only [hLookupNext]
                cases hLink : storeTcbQueueLinks pair.2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp [hLink]
                | ok st2 =>
                  simp only []
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp [hFinal]
                  | ok st3 =>
                    simp only [hFinal, Except.ok.injEq, Prod.mk.injEq]
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
    (hEp : st'.objects oid = some (.endpoint ep)) :
    st.objects oid = some (.endpoint ep) := by
  unfold endpointQueuePopHead at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ => simp [hObj] at hStep
    | endpoint epOrig =>
      simp only [hObj] at hStep; revert hStep
      cases hHead : (if isReceiveQ then epOrig.receiveQ else epOrig.sendQ).head with
      | none => simp [hHead]
      | some headTid =>
        simp only [hHead]
        cases hLookup : lookupTcb st headTid with
        | none => simp [hLookup]
        | some headTcb =>
          simp only [hLookup]
          cases hStore : storeObject endpointId _ st with
          | error e => simp [hStore]
          | ok pair => simp only [hStore]; cases hNext : headTcb.queueNext with
            | none =>
              simp only [hNext]
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp [hFinal]
              | ok st3 =>
                simp only [hFinal, Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                have h1 := storeTcbQueueLinks_endpoint_backward _ _ headTid none none none oid ep hFinal hEp
                rwa [storeObject_objects_ne st pair.2 endpointId oid _ hNe hStore] at h1
            | some nextTid =>
              simp only [hNext]
              cases hLookupNext : lookupTcb pair.2 nextTid with
              | none => simp [hLookupNext]
              | some nextTcb =>
                simp only [hLookupNext]
                cases hLink : storeTcbQueueLinks pair.2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp [hLink]
                | ok st2 =>
                  simp only []
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp [hFinal]
                  | ok st3 =>
                    simp only [hFinal, Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    have h3 := storeTcbQueueLinks_endpoint_backward _ _ headTid none none none oid ep hFinal hEp
                    have h2 := storeTcbQueueLinks_endpoint_backward _ _ nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext oid ep hLink h3
                    rwa [storeObject_objects_ne st pair.2 endpointId oid _ hNe hStore] at h2

/-- WS-F1: endpointQueuePopHead backward-preserves notifications. -/
theorem endpointQueuePopHead_notification_backward
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, st'))
    (hNtfn : st'.objects oid = some (.notification ntfn)) :
    st.objects oid = some (.notification ntfn) := by
  unfold endpointQueuePopHead at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep; revert hStep
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp [hHead]
      | some headTid =>
        simp only [hHead]
        cases hLookup : lookupTcb st headTid with
        | none => simp [hLookup]
        | some headTcb =>
          simp only [hLookup]
          cases hStore : storeObject endpointId _ st with
          | error e => simp [hStore]
          | ok pair => simp only [hStore]; cases hNext : headTcb.queueNext with
            | none =>
              simp only [hNext]
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp [hFinal]
              | ok st3 =>
                simp only [hFinal, Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                have h1 := storeTcbQueueLinks_notification_backward _ _ headTid none none none oid ntfn hFinal hNtfn
                by_cases hEqId : oid = endpointId
                · subst hEqId; rw [storeObject_objects_eq st pair.2 oid _ hStore] at h1; cases h1
                · rwa [storeObject_objects_ne st pair.2 endpointId oid _ hEqId hStore] at h1
            | some nextTid =>
              simp only [hNext]
              cases hLookupNext : lookupTcb pair.2 nextTid with
              | none => simp [hLookupNext]
              | some nextTcb =>
                simp only [hLookupNext]
                cases hLink : storeTcbQueueLinks pair.2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp [hLink]
                | ok st2 =>
                  simp only []
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp [hFinal]
                  | ok st3 =>
                    simp only [hFinal, Except.ok.injEq, Prod.mk.injEq]
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
    (hTcb : st.objects oid = some (.tcb tcb)) :
    ∃ tcb', st'.objects oid = some (.tcb tcb') := by
  unfold endpointQueuePopHead at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep; revert hStep
      have hNe : oid ≠ endpointId := by intro h; subst h; rw [hTcb] at hObj; cases hObj
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp [hHead]
      | some headTid =>
        simp only [hHead]
        cases hLookup : lookupTcb st headTid with
        | none => simp [hLookup]
        | some headTcb =>
          simp only [hLookup]
          cases hStore : storeObject endpointId _ st with
          | error e => simp [hStore]
          | ok pair =>
            simp only [hStore]
            have hTcb1 : pair.2.objects oid = some (.tcb tcb) := by
              rw [storeObject_objects_ne st pair.2 endpointId oid _ hNe hStore]; exact hTcb
            cases hNext : headTcb.queueNext with
            | none =>
              simp only [hNext]
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp [hFinal]
              | ok st3 =>
                simp only [hFinal, Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                exact storeTcbQueueLinks_tcb_forward pair.2 st3 headTid none none none oid tcb hFinal hTcb1
            | some nextTid =>
              simp only [hNext]
              cases hLookupNext : lookupTcb pair.2 nextTid with
              | none => simp [hLookupNext]
              | some nextTcb =>
                simp only [hLookupNext]
                cases hLink : storeTcbQueueLinks pair.2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp [hLink]
                | ok st2 =>
                  simp only []
                  obtain ⟨tcb2, hTcb2⟩ := storeTcbQueueLinks_tcb_forward pair.2 st2 nextTid _ _ _ oid tcb hLink hTcb1
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp [hFinal]
                  | ok st3 =>
                    simp only [hFinal, Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    exact storeTcbQueueLinks_tcb_forward st2 st3 headTid none none none oid tcb2 hFinal hTcb2

/-- WS-F1: endpointQueuePopHead backward-preserves TCB ipcStates. For any TCB
in the post-state, a TCB with the same ipcState exists in the pre-state. -/
theorem endpointQueuePopHead_tcb_ipcState_backward
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (anyTid : SeLe4n.ThreadId) (tcb' : TCB)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, st'))
    (hTcb' : st'.objects anyTid.toObjId = some (.tcb tcb')) :
    ∃ tcb, st.objects anyTid.toObjId = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState := by
  unfold endpointQueuePopHead at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep; revert hStep
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp [hHead]
      | some headTid =>
        simp only [hHead]
        cases hLookup : lookupTcb st headTid with
        | none => simp [hLookup]
        | some headTcb =>
          simp only [hLookup]
          cases hStore : storeObject endpointId _ st with
          | error e => simp [hStore]
          | ok pair =>
            simp only [hStore]
            cases hNext : headTcb.queueNext with
            | none =>
              simp only [hNext]
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp [hFinal]
              | ok st3 =>
                simp only [hFinal, Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                obtain ⟨tcb1, hTcb1, hIpc1⟩ := storeTcbQueueLinks_tcb_ipcState_backward _ _ headTid none none none hFinal anyTid tcb' hTcb'
                by_cases hEqEp : anyTid.toObjId = endpointId
                · rw [hEqEp] at hTcb1; rw [storeObject_objects_eq st pair.2 endpointId _ hStore] at hTcb1; cases hTcb1
                · rw [storeObject_objects_ne st pair.2 endpointId anyTid.toObjId _ hEqEp hStore] at hTcb1
                  exact ⟨tcb1, hTcb1, hIpc1⟩
            | some nextTid =>
              simp only [hNext]
              cases hLookupNext : lookupTcb pair.2 nextTid with
              | none => simp [hLookupNext]
              | some nextTcb =>
                simp only [hLookupNext]
                cases hLink : storeTcbQueueLinks pair.2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp [hLink]
                | ok st2 =>
                  simp only []
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp [hFinal]
                  | ok st3 =>
                    simp only [hFinal, Except.ok.injEq, Prod.mk.injEq]
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
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ => simp [hObj] at hStep
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
              | error e => simp [hStore]
              | ok pair =>
                simp only [hStore]
                intro hStep
                exact (storeTcbQueueLinks_scheduler_eq _ _ tid _ _ _ hStep).trans
                  (storeObject_scheduler_eq _ _ endpointId _ hStore)
            | some tailTid =>
              cases hLookupTail : lookupTcb st tailTid with
              | none => simp [hLookupTail]
              | some tailTcb =>
                simp only [hLookupTail]
                cases hStore : storeObject endpointId _ st with
                | error e => simp [hStore]
                | ok pair =>
                  simp only [hStore]
                  cases hLink1 : storeTcbQueueLinks pair.2 tailTid tailTcb.queuePrev tailTcb.queuePPrev (some tid) with
                  | error e => simp [hLink1]
                  | ok st2 =>
                    simp only [hLink1]
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
    (hEp : st'.objects oid = some (.endpoint ep)) :
    st.objects oid = some (.endpoint ep) := by
  unfold endpointQueueEnqueue at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ => simp [hObj] at hStep
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
              | error e => simp [hStore]
              | ok pair =>
                simp only [hStore]
                intro hStep
                have h1 := storeTcbQueueLinks_endpoint_backward _ _ enqueueTid _ _ _ oid ep hStep hEp
                rwa [storeObject_objects_ne st pair.2 endpointId oid _ hNe hStore] at h1
            | some tailTid =>
              cases hLookupTail : lookupTcb st tailTid with
              | none => simp [hLookupTail]
              | some tailTcb =>
                simp only [hLookupTail]
                cases hStore : storeObject endpointId _ st with
                | error e => simp [hStore]
                | ok pair =>
                  simp only [hStore]
                  cases hLink1 : storeTcbQueueLinks pair.2 tailTid tailTcb.queuePrev tailTcb.queuePPrev (some enqueueTid) with
                  | error e => simp [hLink1]
                  | ok st2 =>
                    simp only [hLink1]
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
    (hNtfn : st'.objects oid = some (.notification ntfn)) :
    st.objects oid = some (.notification ntfn) := by
  unfold endpointQueueEnqueue at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ => simp [hObj] at hStep
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
              | error e => simp [hStore]
              | ok pair =>
                simp only [hStore]
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
                | error e => simp [hStore]
                | ok pair =>
                  simp only [hStore]
                  cases hLink1 : storeTcbQueueLinks pair.2 tailTid tailTcb.queuePrev tailTcb.queuePPrev (some enqueueTid) with
                  | error e => simp [hLink1]
                  | ok st2 =>
                    simp only [hLink1]
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
    (hTcb : st.objects oid = some (.tcb tcb)) :
    ∃ tcb', st'.objects oid = some (.tcb tcb') := by
  unfold endpointQueueEnqueue at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ => simp [hObj] at hStep
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
              | error e => simp [hStore]
              | ok pair =>
                simp only [hStore]; intro hStep
                have hTcb1 : pair.2.objects oid = some (.tcb tcb) := by
                  rw [storeObject_objects_ne st pair.2 endpointId oid _ hNe hStore]; exact hTcb
                exact storeTcbQueueLinks_tcb_forward pair.2 st' enqueueTid _ _ _ oid tcb hStep hTcb1
            | some tailTid =>
              cases hLookupTail : lookupTcb st tailTid with
              | none => simp [hLookupTail]
              | some tailTcb =>
                simp only [hLookupTail]
                cases hStore : storeObject endpointId _ st with
                | error e => simp [hStore]
                | ok pair =>
                  simp only [hStore]
                  have hTcb1 : pair.2.objects oid = some (.tcb tcb) := by
                    rw [storeObject_objects_ne st pair.2 endpointId oid _ hNe hStore]; exact hTcb
                  cases hLink1 : storeTcbQueueLinks pair.2 tailTid tailTcb.queuePrev tailTcb.queuePPrev (some enqueueTid) with
                  | error e => simp [hLink1]
                  | ok st2 =>
                    simp only [hLink1]; intro hStep
                    obtain ⟨tcb2, hTcb2⟩ := storeTcbQueueLinks_tcb_forward pair.2 st2 tailTid _ _ _ oid tcb hLink1 hTcb1
                    exact storeTcbQueueLinks_tcb_forward st2 st' enqueueTid _ _ _ oid tcb2 hStep hTcb2

/-- WS-F1: endpointQueueEnqueue backward-preserves TCB ipcStates. -/
theorem endpointQueueEnqueue_tcb_ipcState_backward
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (enqueueTid : SeLe4n.ThreadId) (st st' : SystemState)
    (anyTid : SeLe4n.ThreadId) (tcb' : TCB)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ enqueueTid st = .ok st')
    (hTcb' : st'.objects anyTid.toObjId = some (.tcb tcb')) :
    ∃ tcb, st.objects anyTid.toObjId = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState := by
  unfold endpointQueueEnqueue at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ => simp [hObj] at hStep
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
              | error e => simp [hStore]
              | ok pair =>
                simp only [hStore]; intro hStep
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
                | error e => simp [hStore]
                | ok pair =>
                  simp only [hStore]
                  cases hLink1 : storeTcbQueueLinks pair.2 tailTid tailTcb.queuePrev tailTcb.queuePPrev (some enqueueTid) with
                  | error e => simp [hLink1]
                  | ok st2 =>
                    simp only [hLink1]; intro hStep
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
    match st.objects endpointId with
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
  cases hObj : st.objects endpointId with
  | none => simp [hObj]
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ => simp [hObj]
    | endpoint ep =>
      simp only [hObj]
      cases hLookup : lookupTcb st tid with
      | none => simp [hLookup]
      | some tcb =>
        simp only [hLookup]
        cases hPPrev : tcb.queuePPrev with
        | none => simp [hPPrev]
        | some pprev =>
          simp only [hPPrev]
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
                simp only [hStore1]; cases hNext : tcb.queueNext with
                | none =>
                  simp only [hNext]
                  cases hStore2 : storeObject endpointId _ pair1.2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only [hStore2]; cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [hFinal, Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    exact (storeTcbQueueLinks_scheduler_eq _ _ tid _ _ _ hFinal).trans
                      ((storeObject_scheduler_eq _ _ endpointId _ hStore2).trans
                        (storeObject_scheduler_eq _ _ endpointId _ hStore1))
                | some nextTid =>
                  simp only [hNext]
                  cases hLookupN : lookupTcb pair1.2 nextTid with
                  | none => simp
                  | some nextTcb =>
                  simp only [hLookupN]; cases hLink : storeTcbQueueLinks pair1.2 nextTid _ _ nextTcb.queueNext with
                  | error e => simp
                  | ok st2 =>
                  simp only [hLink]; cases hStore2 : storeObject endpointId _ st2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only [hStore2]; cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [hFinal, Except.ok.injEq, Prod.mk.injEq]
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
    (hTcb : st.objects oid = some (.tcb tcb)) :
    ∃ tcb', st'.objects oid = some (.tcb tcb') := by
  unfold endpointQueueRemoveDual at hStep; revert hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj]
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ => simp [hObj]
    | endpoint ep =>
      simp only [hObj]
      have hNe : oid ≠ endpointId := by intro h; subst h; rw [hTcb] at hObj; cases hObj
      cases hLookup : lookupTcb st tid with
      | none => simp [hLookup]
      | some tcbTid =>
        simp only [hLookup]
        cases hPPrev : tcbTid.queuePPrev with
        | none => simp [hPPrev]
        | some pprev =>
          simp only [hPPrev]
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
                simp only [hStore1]
                have hTcb1 : pair1.2.objects oid = some (.tcb tcb) := by
                  rw [storeObject_objects_ne st pair1.2 endpointId oid _ hNe hStore1]; exact hTcb
                cases hNext : tcbTid.queueNext with
                | none =>
                  simp only [hNext]
                  cases hStore2 : storeObject endpointId _ pair1.2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only [hStore2]
                  have hTcb2 : pair2.2.objects oid = some (.tcb tcb) := by
                    rw [storeObject_objects_ne pair1.2 pair2.2 endpointId oid _ hNe hStore2]; exact hTcb1
                  cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [hFinal, Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    exact storeTcbQueueLinks_tcb_forward pair2.2 st4 tid none none none oid tcb hFinal hTcb2
                | some nextTid =>
                  simp only [hNext]
                  cases hLookupN : lookupTcb pair1.2 nextTid with
                  | none => simp
                  | some nextTcb =>
                  simp only [hLookupN]; cases hLink : storeTcbQueueLinks pair1.2 nextTid _ _ nextTcb.queueNext with
                  | error e => simp
                  | ok st2 =>
                  simp only [hLink]
                  obtain ⟨tcb2, hTcb2⟩ := storeTcbQueueLinks_tcb_forward pair1.2 st2 nextTid _ _ _ oid tcb hLink hTcb1
                  cases hStore2 : storeObject endpointId _ st2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only [hStore2]
                  have hTcb3 : pair2.2.objects oid = some (.tcb tcb2) := by
                    rw [storeObject_objects_ne st2 pair2.2 endpointId oid _ hNe hStore2]; exact hTcb2
                  cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [hFinal, Except.ok.injEq, Prod.mk.injEq]
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
                      have hTcb1 : pair2.2.objects oid = some (.tcb tcb0) := by
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
                      have hTcb2 : pair2.2.objects oid = some (.tcb tcb1) := by
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
    (hEp : st'.objects oid = some (.endpoint ep)) :
    st.objects oid = some (.endpoint ep) := by
  unfold endpointQueueRemoveDual at hStep; revert hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj]
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ => simp [hObj]
    | endpoint epOrig =>
      simp only [hObj]
      cases hLookup : lookupTcb st tid with
      | none => simp [hLookup]
      | some tcbTid =>
        simp only [hLookup]
        cases hPPrev : tcbTid.queuePPrev with
        | none => simp [hPPrev]
        | some pprev =>
          simp only [hPPrev]
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
                simp only [hStore1]; cases hNext : tcbTid.queueNext with
                | none =>
                  simp only [hNext]
                  cases hStore2 : storeObject endpointId _ pair1.2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only [hStore2]; cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [hFinal, Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    have h1 := storeTcbQueueLinks_endpoint_backward _ _ tid none none none oid ep hFinal hEp
                    rw [storeObject_objects_ne pair1.2 pair2.2 endpointId oid _ hNe hStore2] at h1
                    rwa [storeObject_objects_ne st pair1.2 endpointId oid _ hNe hStore1] at h1
                | some nextTid =>
                  simp only [hNext]
                  cases hLookupN : lookupTcb pair1.2 nextTid with
                  | none => simp
                  | some nextTcb =>
                  simp only [hLookupN]; cases hLink : storeTcbQueueLinks pair1.2 nextTid _ _ nextTcb.queueNext with
                  | error e => simp
                  | ok st2 =>
                  simp only [hLink]; cases hStore2 : storeObject endpointId _ st2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only [hStore2]; cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [hFinal, Except.ok.injEq, Prod.mk.injEq]
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
    (hNtfn : st'.objects oid = some (.notification ntfn)) :
    st.objects oid = some (.notification ntfn) := by
  unfold endpointQueueRemoveDual at hStep; revert hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj]
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ => simp [hObj]
    | endpoint epOrig =>
      simp only [hObj]
      cases hLookup : lookupTcb st tid with
      | none => simp [hLookup]
      | some tcbTid =>
        simp only [hLookup]
        cases hPPrev : tcbTid.queuePPrev with
        | none => simp [hPPrev]
        | some pprev =>
          simp only [hPPrev]
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
                simp only [hStore1]; cases hNext : tcbTid.queueNext with
                | none =>
                  simp only [hNext]
                  cases hStore2 : storeObject endpointId _ pair1.2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only [hStore2]; cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [hFinal, Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    have h1 := storeTcbQueueLinks_notification_backward _ _ tid none none none oid ntfn hFinal hNtfn
                    by_cases hEqId : oid = endpointId
                    · subst hEqId; rw [storeObject_objects_eq _ _ oid _ hStore2] at h1; cases h1
                    · rw [storeObject_objects_ne pair1.2 pair2.2 endpointId oid _ hEqId hStore2] at h1
                      rwa [storeObject_objects_ne st pair1.2 endpointId oid _ hEqId hStore1] at h1
                | some nextTid =>
                  simp only [hNext]
                  cases hLookupN : lookupTcb pair1.2 nextTid with
                  | none => simp
                  | some nextTcb =>
                  simp only [hLookupN]; cases hLink : storeTcbQueueLinks pair1.2 nextTid _ _ nextTcb.queueNext with
                  | error e => simp
                  | ok st2 =>
                  simp only [hLink]; cases hStore2 : storeObject endpointId _ st2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only [hStore2]; cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [hFinal, Except.ok.injEq, Prod.mk.injEq]
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
    match st.objects endpointId with
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

Returns the sender's ThreadId. The transferred message is available in the
receiver's TCB.pendingMessage after the operation (matching seL4's model
where the message lands in the receiver's IPC buffer). -/
def endpointReceiveDual (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    : Kernel SeLe4n.ThreadId :=
  fun st =>
    match st.objects endpointId with
    | some (.endpoint ep) =>
        match ep.sendQ.head with
        | some _ =>
            match endpointQueuePopHead endpointId false st with
            | .error e => .error e
            | .ok (sender, st') =>
                -- WS-F1: Extract message from sender's TCB
                let senderMsg := match lookupTcb st' sender with
                  | some tcb => tcb.pendingMessage
                  | none => none
                -- Unblock sender and clear its pending message
                match storeTcbIpcStateAndMessage st' sender .ready none with
                | .error e => .error e
                | .ok st'' =>
                    let st''' := ensureRunnable st'' sender
                    -- WS-F1: Deliver message to receiver's TCB (best-effort —
                    -- receiver TCB existence is not a precondition for dequeue)
                    match storeTcbPendingMessage st''' receiver senderMsg with
                    | .ok st4 => .ok (sender, st4)
                    | .error _ => .ok (sender, st''')
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
If no receiver queued: enqueue caller as sender with message stored in TCB. -/
def endpointCall (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) : Kernel Unit :=
  fun st =>
    match st.objects endpointId with
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
                    -- Caller blocks waiting for reply
                    match storeTcbIpcState st''' caller (.blockedOnReply endpointId) with
                    | .error e => .error e
                    | .ok st4 => .ok ((), removeRunnable st4 caller)
        | none =>
            match endpointQueueEnqueue endpointId false caller st with
            | .error e => .error e
            | .ok st' =>
                -- WS-F1: Store message in caller's TCB while blocked
                match storeTcbIpcStateAndMessage st' caller (.blockedOnSend endpointId) (some msg) with
                | .error e => .error e
                | .ok st'' => .ok ((), removeRunnable st'' caller)
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

/-- WS-F1/WS-E4/M-12: Reply to a thread blocked on reply, with message transfer.

Unblocks the target thread by setting its IPC state to ready, delivers the reply
`msg` into the target's TCB, and adds it to the runnable queue.
Fails if the target is not in blockedOnReply state. -/
def endpointReply (target : SeLe4n.ThreadId) (msg : IpcMessage) : Kernel Unit :=
  fun st =>
    match lookupTcb st target with
    | none => .error .objectNotFound
    | some tcb =>
        match tcb.ipcState with
        | .blockedOnReply _ =>
            -- WS-F1: Deliver reply message and unblock
            match storeTcbIpcStateAndMessage st target .ready (some msg) with
            | .error e => .error e
            | .ok st' => .ok ((), ensureRunnable st' target)
        | _ => .error .replyCapInvalid

/-- WS-F1/WS-E4/M-12: Reply to a caller, then await receive on the endpoint.

Combines reply + receive in a single atomic operation, matching seL4_ReplyRecv.
The reply delivers `msg` to the target and unblocks it, then the receiver waits
on the endpoint for incoming messages. -/
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
        | .blockedOnReply _ =>
            -- WS-F1: Deliver reply message and unblock target
            match storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
            | .error e => .error e
            | .ok st' =>
                let st'' := ensureRunnable st' replyTarget
                match endpointAwaitReceive endpointId receiver st'' with
                | .error e => .error e
                | .ok result => .ok result
        | _ => .error .replyCapInvalid

end SeLe4n.Kernel
