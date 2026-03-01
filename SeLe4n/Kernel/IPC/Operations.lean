import SeLe4n.Model.State

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- WS-G4/F-P02: O(1) amortized remove via RunQueue. -/
def removeRunnable (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  { st with
      scheduler := {
        st.scheduler with
          runQueue := st.scheduler.runQueue.remove tid
          current := if st.scheduler.current = some tid then none else st.scheduler.current
      }
  }

/-- WS-G4/F-P02: O(1) amortized insert via RunQueue.
    Priority defaults to 0 when TCB priority is not yet modelled. -/
def ensureRunnable (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  if tid ∈ st.scheduler.runQueue then
    st
  else
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
        { st with
            scheduler := {
              st.scheduler with
                runQueue := st.scheduler.runQueue.insert tid tcb.priority
            }
        }
    | _ => st

def lookupTcb (st : SystemState) (tid : SeLe4n.ThreadId) : Option TCB :=
  if tid.isReserved then
    none
  else
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) => some tcb
    | _ => none

/-- If lookupTcb succeeds, the underlying objects map has a TCB at tid.toObjId. -/
theorem lookupTcb_some_objects
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (h : lookupTcb st tid = some tcb) :
    st.objects[tid.toObjId]? = some (.tcb tcb) := by
  unfold lookupTcb at h
  cases hRes : tid.isReserved
  · -- false
    simp [hRes] at h; revert h
    cases hObj : st.objects[tid.toObjId]? with
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

/-- **Deprecated (WS-G7):** Use `endpointSendDual` from `IPC.DualQueue` instead.
This legacy O(n) endpoint send is retained only for backward compatibility of
existing invariant proofs; new code should use the O(1) dual-queue path.

Add a sender to an endpoint wait queue with explicit state transition.

WS-E3/H-09: Thread IPC state transitions are now enforced:
- **Blocking paths** (idle→send, send→send): the sender's IPC state is set to
  `.blockedOnSend endpointId` and the sender is removed from the runnable queue.
- **Handshake path** (receive→idle): the waiting receiver is unblocked — IPC state
  set to `.ready` and added to the runnable queue. The sender does not block. -/
def endpointSend (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) : Kernel Unit :=
  fun st =>
    match st.objects[endpointId]? with
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

/-- **Deprecated (WS-G7):** Use `endpointReceiveDual` from `IPC.DualQueue` instead.
This legacy O(n) endpoint await-receive is retained only for backward compatibility
of existing invariant proofs; new code should use the O(1) dual-queue path.

Register one waiting receiver on an idle endpoint.

WS-E3/H-09: After registration, the receiver's IPC state is set to
`.blockedOnReceive endpointId` and the receiver is removed from the runnable queue.
This makes the `blockedOnReceiveNotRunnable` contract predicate non-vacuous. -/
def endpointAwaitReceive (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) : Kernel Unit :=
  fun st =>
    match st.objects[endpointId]? with
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

/-- **Deprecated (WS-G7):** Use `endpointReceiveDual` from `IPC.DualQueue` instead.
This legacy O(n) endpoint receive is retained only for backward compatibility of
existing invariant proofs; new code should use the O(1) dual-queue path.

Consume one queued sender from an endpoint wait queue.

WS-E3/H-09: After dequeuing a sender, the sender's IPC state is set to `.ready`
and the sender is added to the runnable queue. This unblocks the sender that was
previously blocked by `endpointSend`. -/
def endpointReceive (endpointId : SeLe4n.ObjId) : Kernel SeLe4n.ThreadId :=
  fun st =>
    match st.objects[endpointId]? with
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
    match st.objects[notificationId]? with
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

WS-G7/F-P11: Duplicate-wait check uses O(1) TCB ipcState lookup instead of
O(n) list membership scan. If the waiter's ipcState is already
`.blockedOnNotification notificationId`, the thread is already waiting and
`alreadyWaiting` is returned.

WS-G7/F-P11: Waiter is prepended (`waiter :: waitingThreads`) instead of
appended (`waitingThreads ++ [waiter]`), reducing enqueue from O(n) to O(1).
FIFO ordering is not required by the seL4 notification spec — any waiter may
be woken on signal. -/
def notificationWait
    (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) : Kernel (Option SeLe4n.Badge) :=
  fun st =>
    match st.objects[notificationId]? with
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
            -- WS-G7/F-P11: O(1) duplicate check via TCB ipcState instead of O(n) list membership
            match lookupTcb st waiter with
            | none => .error .objectNotFound
            | some tcb =>
                if tcb.ipcState = .blockedOnNotification notificationId then
                  .error .alreadyWaiting
                else
                  let ntfn' : Notification := {
                    state := .waiting
                    waitingThreads := waiter :: ntfn.waitingThreads
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
    st'.objects[oid]? = st.objects[oid]? := by
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
    (hNtfn : st.objects[notifId]? = some (.notification ntfn))
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.objects[notifId]? = some (.notification ntfn) := by
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
    (hEp : st.objects[epId]? = some (.endpoint ep))
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.objects[epId]? = some (.endpoint ep) := by
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
    (hCn : st.objects[cnodeId]? = some (.cnode cn))
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.objects[cnodeId]? = some (.cnode cn) := by
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
    (hVs : st.objects[oid]? = some (.vspaceRoot vs))
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.objects[oid]? = some (.vspaceRoot vs) := by
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
    (hCn : st'.objects[oid]? = some (.cnode cn)) :
    st.objects[oid]? = some (.cnode cn) := by
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
    (hEp : st'.objects[oid]? = some (.endpoint ep)) :
    st.objects[oid]? = some (.endpoint ep) := by
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
    (hNtfn : st'.objects[oid]? = some (.notification ntfn)) :
    st.objects[oid]? = some (.notification ntfn) := by
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

/-- WS-G7/F-P11: Double-wait is rejected: if the waiter's TCB ipcState is
already `.blockedOnNotification notifId`, `notificationWait` returns
`alreadyWaiting`. Uses O(1) TCB lookup instead of O(n) list membership. -/
theorem notificationWait_error_alreadyWaiting
    (waiter : SeLe4n.ThreadId)
    (notifId : SeLe4n.ObjId)
    (st : SystemState)
    (ntfn : Notification)
    (tcb : TCB)
    (hObj : st.objects[notifId]? = some (.notification ntfn))
    (hNoBadge : ntfn.pendingBadge = none)
    (hTcb : lookupTcb st waiter = some tcb)
    (hBlocked : tcb.ipcState = .blockedOnNotification notifId) :
    notificationWait notifId waiter st = .error .alreadyWaiting := by
  unfold notificationWait
  simp [hObj, hNoBadge, hTcb, hBlocked]

/-- Decomposition: on the badge-consumed path, the post-state notification
has an empty waiting list. -/
theorem notificationWait_badge_path_notification
    (st st' : SystemState)
    (notifId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId)
    (badge : SeLe4n.Badge)
    (hStep : notificationWait notifId waiter st = .ok (some badge, st')) :
    ∃ ntfn', st'.objects[notifId]? = some (.notification ntfn') ∧ ntfn'.waitingThreads = [] := by
  unfold notificationWait at hStep
  cases hObj : st.objects[notifId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hBadge : ntfn.pendingBadge with
      | none =>
        simp only [hBadge] at hStep
        -- WS-G7: lookupTcb match
        cases hLookup : lookupTcb st waiter with
        | none => simp [hLookup] at hStep
        | some tcb =>
          simp only [hLookup] at hStep
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
            have hNtfnStored : pair.2.objects[notifId]? = some (.notification newNtfn) :=
              storeObject_objects_eq st pair.2 notifId (.notification newNtfn) hStore
            have hNtfnPreserved : st2.objects[notifId]? = some (.notification newNtfn) :=
              storeTcbIpcState_preserves_notification pair.2 st2 waiter .ready notifId newNtfn hNtfnStored hTcb
            exact ⟨newNtfn, hNtfnPreserved, rfl⟩

/-- WS-G7/F-P11: Decomposition: on the wait path, the post-state notification has the
waiter prepended. The waiter's TCB existed and was not already blocked on this
notification. -/
theorem notificationWait_wait_path_notification
    (st st' : SystemState)
    (notifId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId)
    (hStep : notificationWait notifId waiter st = .ok (none, st')) :
    ∃ ntfn ntfn',
      st.objects[notifId]? = some (.notification ntfn) ∧
      ntfn.pendingBadge = none ∧
      st'.objects[notifId]? = some (.notification ntfn') ∧
      ntfn'.waitingThreads = waiter :: ntfn.waitingThreads := by
  unfold notificationWait at hStep
  cases hObj : st.objects[notifId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
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
        -- WS-G7: match on lookupTcb
        cases hLookup : lookupTcb st waiter with
        | none => simp [hLookup] at hStep
        | some tcb =>
          simp only [hLookup] at hStep
          -- ipcState check
          by_cases hBlocked : tcb.ipcState = .blockedOnNotification notifId
          · simp [hBlocked] at hStep
          · simp only [hBlocked, ite_false] at hStep
            let ntfn' : Notification := { state := .waiting, waitingThreads := waiter :: ntfn.waitingThreads, pendingBadge := none }
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
                have hNtfnStored : pair.2.objects[notifId]? = some (.notification ntfn') :=
                  storeObject_objects_eq st pair.2 notifId (.notification ntfn') hStore
                have hNtfnPreserved : st2.objects[notifId]? = some (.notification ntfn') :=
                  storeTcbIpcState_preserves_notification pair.2 st2 waiter
                    (.blockedOnNotification notifId) notifId ntfn' hNtfnStored hTcb
                refine ⟨ntfn, ntfn', rfl, hBadge, ?_, rfl⟩
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
    x ∈ (removeRunnable st tid).scheduler.runQueue ↔
    x ∈ st.scheduler.runQueue ∧ x ≠ tid := by
  simp only [removeRunnable]
  exact RunQueue.mem_remove st.scheduler.runQueue tid x

/-- WS-G4: Flat-list version of `removeRunnable_mem` for proof compatibility.
    Works with `.runnable` (= `runQueue.toList`) instead of `.runQueue` (HashSet). -/
theorem removeRunnable_runnable_mem
    (st : SystemState) (tid x : SeLe4n.ThreadId) :
    x ∈ (removeRunnable st tid).scheduler.runnable ↔
    x ∈ st.scheduler.runnable ∧ x ≠ tid := by
  simp only [SchedulerState.runnable, removeRunnable, RunQueue.toList]
  unfold RunQueue.remove
  constructor
  · intro hx
    have ⟨hFlat, hNe⟩ := List.mem_filter.mp hx
    exact ⟨hFlat, by simpa using hNe⟩
  · intro ⟨hFlat, hNe⟩
    exact List.mem_filter.mpr ⟨hFlat, by simpa using hNe⟩

theorem removeRunnable_nodup
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hNodup : st.scheduler.runnable.Nodup) :
    (removeRunnable st tid).scheduler.runnable.Nodup := by
  simp only [SchedulerState.runnable, removeRunnable, RunQueue.toList]
  unfold RunQueue.remove
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
    (hTcb : ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb)) :
    tid ∈ (ensureRunnable st tid).scheduler.runQueue := by
  obtain ⟨tcb, hTcb⟩ := hTcb
  unfold ensureRunnable
  split
  · assumption
  · simp only [hTcb]
    rw [RunQueue.mem_insert]
    exact Or.inr rfl

theorem ensureRunnable_mem_old
    (st : SystemState) (tid x : SeLe4n.ThreadId)
    (hMem : x ∈ st.scheduler.runQueue) :
    x ∈ (ensureRunnable st tid).scheduler.runQueue := by
  unfold ensureRunnable
  split
  · exact hMem
  · split
    · rw [RunQueue.mem_insert]; exact Or.inl hMem
    · exact hMem

/-- WS-G4: Flat-list version of `ensureRunnable_mem_old` for proof compatibility.
    Works with `.runnable` (= `runQueue.toList`) instead of `.runQueue` (HashSet). -/
theorem ensureRunnable_runnable_mem_old
    (st : SystemState) (tid x : SeLe4n.ThreadId)
    (hMem : x ∈ st.scheduler.runnable) :
    x ∈ (ensureRunnable st tid).scheduler.runnable := by
  unfold ensureRunnable
  split
  · exact hMem
  · rename_i hNotMem
    split
    · rename_i tcb hTcb
      show x ∈ (st.scheduler.runQueue.insert tid tcb.priority).toList
      rw [RunQueue.toList_insert_not_mem _ _ _ hNotMem]
      exact List.mem_append_left _ hMem
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
    · rename_i tcb hTcb
      show (st.scheduler.runQueue.insert tid tcb.priority).toList.Nodup
      rw [RunQueue.toList_insert_not_mem _ _ _ hNotMem]
      have hNotFlat : tid ∉ st.scheduler.runnable :=
        RunQueue.not_mem_toList_of_not_mem _ _ hNotMem
      refine List.nodup_append.2 ⟨hNodup, List.pairwise_singleton _ _, ?_⟩
      intro x hx y hy
      have : y = tid := by simpa using hy
      subst this; intro hEq; subst hEq
      exact hNotFlat hx
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
    (tcb : TCB) (hTcb : st'.objects[tid.toObjId]? = some (.tcb tcb)) :
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
  · rename_i hNotMem
    split at hMem
    · -- TCB case: runnable = (rq.insert tid prio).toList
      simp only [SchedulerState.runnable, RunQueue.toList] at hMem ⊢
      unfold RunQueue.insert at hMem
      split at hMem
      · exact .inl hMem
      · simp only [List.mem_append, List.mem_singleton] at hMem
        exact hMem.elim .inl .inr
    · exact .inl hMem

/-- WS-E3/H-09: A thread is never in its own removeRunnable result. -/
theorem removeRunnable_not_mem_self
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    tid ∉ (removeRunnable st tid).scheduler.runnable := by
  simp only [SchedulerState.runnable, removeRunnable]
  exact RunQueue.not_mem_remove_toList st.scheduler.runQueue tid

/-- WS-E3/H-09: If a TCB exists at `tid.toObjId` in the pre-state, then a TCB still
    exists there after `storeTcbIpcState` (though the ipcState may have changed). -/
theorem storeTcbIpcState_tcb_exists_at_target
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hStep : storeTcbIpcState st tid ipc = .ok st')
    (_hTcb : ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb)) :
    ∃ tcb', st'.objects[tid.toObjId]? = some (.tcb tcb') := by
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
    st'.objects[oid]? = st.objects[oid]? := by
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
    (hEp : st.objects[epId]? = some (.endpoint ep))
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    st'.objects[epId]? = some (.endpoint ep) := by
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
    (hNtfn : st.objects[notifId]? = some (.notification ntfn))
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    st'.objects[notifId]? = some (.notification ntfn) := by
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
    (hEp : st'.objects[oid]? = some (.endpoint ep)) :
    st.objects[oid]? = some (.endpoint ep) := by
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
    (hNtfn : st'.objects[oid]? = some (.notification ntfn)) :
    st.objects[oid]? = some (.notification ntfn) := by
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
    (tcb : TCB) (hTcb : st'.objects[tid.toObjId]? = some (.tcb tcb)) :
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
    (_hTcb : ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb)) :
    ∃ tcb', st'.objects[tid.toObjId]? = some (.tcb tcb') := by
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
    st'.objects[oid]? = st.objects[oid]? := by
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
    (hEp : st.objects[epId]? = some (.endpoint ep))
    (hStep : storeTcbPendingMessage st tid msg = .ok st') :
    st'.objects[epId]? = some (.endpoint ep) := by
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
    (hEp : st'.objects[oid]? = some (.endpoint ep)) :
    st.objects[oid]? = some (.endpoint ep) := by
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
    (hNtfn : st'.objects[oid]? = some (.notification ntfn)) :
    st.objects[oid]? = some (.notification ntfn) := by
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
    (hTcb : st.objects[oid]? = some (.tcb tcb)) :
    ∃ tcb', st'.objects[oid]? = some (.tcb tcb') := by
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
    (hTcb' : st'.objects[anyTid.toObjId]? = some (.tcb tcb')) :
    ∃ tcb, st.objects[anyTid.toObjId]? = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState := by
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


end SeLe4n.Kernel
