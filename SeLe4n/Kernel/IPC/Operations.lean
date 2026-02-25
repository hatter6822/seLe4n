import SeLe4n.Model.State

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- Remove a thread from the runnable set and clear `current` if the removed
thread was the currently scheduled thread.

H-09 (WS-E3): clearing `current` ensures `queueCurrentConsistent` is
preserved when the current thread blocks on an IPC endpoint. -/
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
    { st with scheduler := { st.scheduler with runnable := st.scheduler.runnable ++ [tid] } }

def lookupTcb (st : SystemState) (tid : SeLe4n.ThreadId) : Option TCB :=
  match st.objects tid.toObjId with
  | some (.tcb tcb) => some tcb
  | _ => none

def storeTcbIpcState (st : SystemState) (tid : SeLe4n.ThreadId) (ipcState : ThreadIpcState) : Except KernelError SystemState :=
  match lookupTcb st tid with
  | none => .ok st
  | some tcb =>
      match storeObject tid.toObjId (.tcb { tcb with ipcState := ipcState }) st with
      | .error e => .error e
      | .ok ((), st') => .ok st'

/-- Add a sender to an endpoint wait queue with explicit state transition.

H-09 (WS-E3): Thread IPC state transitions are now enforced:
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
            | .ok ((), st1) =>
                match storeTcbIpcState st1 sender (.blockedOnSend endpointId) with
                | .error e => .error e
                | .ok st2 => .ok ((), removeRunnable st2 sender)
        | .send =>
            let ep' : Endpoint := { state := .send, queue := ep.queue ++ [sender], waitingReceiver := none }
            match storeObject endpointId (.endpoint ep') st with
            | .error e => .error e
            | .ok ((), st1) =>
                match storeTcbIpcState st1 sender (.blockedOnSend endpointId) with
                | .error e => .error e
                | .ok st2 => .ok ((), removeRunnable st2 sender)
        | .receive =>
            match ep.queue, ep.waitingReceiver with
            | [], some receiver =>
                let ep' : Endpoint := { state := .idle, queue := [], waitingReceiver := none }
                match storeObject endpointId (.endpoint ep') st with
                | .error e => .error e
                | .ok ((), st1) =>
                    match storeTcbIpcState st1 receiver .ready with
                    | .error e => .error e
                    | .ok st2 => .ok ((), ensureRunnable st2 receiver)
            | _, _ => .error .endpointStateMismatch
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

/-- Register one waiting receiver on an idle endpoint.

H-09 (WS-E3): The receiver's IPC state is set to `.blockedOnReceive endpointId`
and the receiver is removed from the runnable queue. This makes the
`blockedOnReceiveNotRunnable` contract predicate non-vacuous. -/
def endpointAwaitReceive (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) : Kernel Unit :=
  fun st =>
    match st.objects endpointId with
    | some (.endpoint ep) =>
        match ep.state, ep.queue, ep.waitingReceiver with
        | .idle, [], none =>
            let ep' : Endpoint := { state := .receive, queue := [], waitingReceiver := some receiver }
            match storeObject endpointId (.endpoint ep') st with
            | .error e => .error e
            | .ok ((), st1) =>
                match storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
                | .error e => .error e
                | .ok st2 => .ok ((), removeRunnable st2 receiver)
        | .idle, _, _ => .error .endpointStateMismatch
        | .send, _, _ => .error .endpointStateMismatch
        | .receive, _, _ => .error .endpointStateMismatch
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

/-- Consume one queued sender from an endpoint wait queue.

H-09 (WS-E3): The dequeued sender's IPC state is set to `.ready` and the
sender is added to the runnable queue via `ensureRunnable`. This unblocks
the sender that was previously blocked by `endpointSend`. -/
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
            | .ok ((), st1) =>
                match storeTcbIpcState st1 sender .ready with
                | .error e => .error e
                | .ok st2 => .ok (sender, ensureRunnable st2 sender)
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
    subst hStep; rfl
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
    subst hStep
    exact hNtfn
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc notifId hEq hStep]
    exact hNtfn

/-- `removeRunnable` only modifies the scheduler; all objects are preserved. -/
theorem removeRunnable_preserves_objects
    (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    (removeRunnable st tid).objects = st.objects := by
  rfl

-- ============================================================================
-- H-09 (WS-E3): Frame lemmas for multi-step endpoint chain proofs
-- ============================================================================

/-- `ensureRunnable` only modifies the scheduler; all objects are preserved. -/
theorem ensureRunnable_preserves_objects
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (ensureRunnable st tid).objects = st.objects := by
  simp [ensureRunnable]; split <;> rfl

/-- `removeRunnable` preserves services. -/
theorem removeRunnable_preserves_services
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeRunnable st tid).services = st.services := by rfl

/-- `ensureRunnable` preserves services. -/
theorem ensureRunnable_preserves_services
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (ensureRunnable st tid).services = st.services := by
  simp [ensureRunnable]; split <;> rfl

/-- `removeRunnable` scheduler current: cleared if tid is current, else preserved. -/
theorem removeRunnable_current
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeRunnable st tid).scheduler.current =
      if st.scheduler.current = some tid then none else st.scheduler.current := by rfl

/-- `ensureRunnable` preserves the scheduler `current` field. -/
theorem ensureRunnable_preserves_current
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (ensureRunnable st tid).scheduler.current = st.scheduler.current := by
  simp [ensureRunnable]; split <;> rfl

/-- `storeTcbIpcState` preserves the scheduler. -/
theorem storeTcbIpcState_preserves_scheduler
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.scheduler = st.scheduler := by
  unfold storeTcbIpcState at hStep
  cases hTcb : lookupTcb st tid with
  | none => simp [hTcb] at hStep; subst hStep; rfl
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq : pair.snd = st' := Except.ok.inj hStep
      subst hEq
      exact storeObject_scheduler_eq st pair.2 tid.toObjId (.tcb { tcb with ipcState := ipc }) hStore

/-- `storeTcbIpcState` preserves services. -/
theorem storeTcbIpcState_preserves_services
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.services = st.services := by
  unfold storeTcbIpcState at hStep
  cases hTcb : lookupTcb st tid with
  | none => simp [hTcb] at hStep; subst hStep; rfl
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq : pair.snd = st' := Except.ok.inj hStep
      subst hEq
      exact storeObject_preserves_services st pair.2 tid.toObjId _ hStore

/-- `storeTcbIpcState` preserves endpoint objects (it only writes TCBs). -/
theorem storeTcbIpcState_preserves_endpoint
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (eid : SeLe4n.ObjId) (ep : Endpoint)
    (hEp : st.objects eid = some (.endpoint ep))
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.objects eid = some (.endpoint ep) := by
  by_cases hEq : eid = tid.toObjId
  · subst hEq
    unfold storeTcbIpcState at hStep
    have hLookup : lookupTcb st tid = none := by unfold lookupTcb; simp [hEp]
    simp [hLookup] at hStep; subst hStep; exact hEp
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc eid hEq hStep]; exact hEp

/-- `storeTcbIpcState` preserves CNode objects (it only writes TCBs). -/
theorem storeTcbIpcState_preserves_cnode
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (oid : SeLe4n.ObjId) (cn : CNode)
    (hCn : st.objects oid = some (.cnode cn))
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.objects oid = some (.cnode cn) := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq
    unfold storeTcbIpcState at hStep
    have hLookup : lookupTcb st tid = none := by unfold lookupTcb; simp [hCn]
    simp [hLookup] at hStep; subst hStep; exact hCn
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc oid hEq hStep]; exact hCn

/-- `storeTcbIpcState` preserves VSpaceRoot objects (it only writes TCBs). -/
theorem storeTcbIpcState_preserves_vspaceRoot
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (oid : SeLe4n.ObjId) (root : VSpaceRoot)
    (hRoot : st.objects oid = some (.vspaceRoot root))
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.objects oid = some (.vspaceRoot root) := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq
    unfold storeTcbIpcState at hStep
    have hLookup : lookupTcb st tid = none := by unfold lookupTcb; simp [hRoot]
    simp [hLookup] at hStep; subst hStep; exact hRoot
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc oid hEq hStep]; exact hRoot

/-- Backward: if an endpoint exists post-storeTcbIpcState, it existed pre. -/
theorem storeTcbIpcState_endpoint_backward
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hEpPost : st'.objects oid = some (.endpoint ep))
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st.objects oid = some (.endpoint ep) := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq
    unfold storeTcbIpcState at hStep
    cases hLookup : lookupTcb st tid with
    | none => simp [hLookup] at hStep; subst hStep; exact hEpPost
    | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        simp only [hStore] at hStep
        have hEq2 : pair.snd = st' := Except.ok.inj hStep
        subst hEq2
        have := storeObject_objects_eq st pair.2 tid.toObjId (.tcb { tcb with ipcState := ipc }) hStore
        rw [this] at hEpPost; cases hEpPost
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc oid hEq hStep] at hEpPost
    exact hEpPost

/-- Backward: if a notification exists post-storeTcbIpcState, it existed pre. -/
theorem storeTcbIpcState_notification_backward
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hNtfnPost : st'.objects oid = some (.notification ntfn))
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st.objects oid = some (.notification ntfn) := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq
    unfold storeTcbIpcState at hStep
    cases hLookup : lookupTcb st tid with
    | none => simp [hLookup] at hStep; subst hStep; exact hNtfnPost
    | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        simp only [hStore] at hStep
        have hEq2 : pair.snd = st' := Except.ok.inj hStep
        subst hEq2
        have := storeObject_objects_eq st pair.2 tid.toObjId (.tcb { tcb with ipcState := ipc }) hStore
        rw [this] at hNtfnPost; cases hNtfnPost
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc oid hEq hStep] at hNtfnPost
    exact hNtfnPost

/-- If `x` is in the runnable list of `removeRunnable st tid`, then `x` was in the original. -/
theorem removeRunnable_mem_implies_mem
    (st : SystemState) (tid x : SeLe4n.ThreadId)
    (h : x ∈ (removeRunnable st tid).scheduler.runnable) :
    x ∈ st.scheduler.runnable :=
  List.filter_sublist.subset h

/-- If `x` is in the runnable list of `removeRunnable st tid`, then `x ≠ tid`. -/
theorem removeRunnable_mem_implies_ne
    (st : SystemState) (tid x : SeLe4n.ThreadId)
    (h : x ∈ (removeRunnable st tid).scheduler.runnable) :
    x ≠ tid := by
  simp only [removeRunnable, List.mem_filter] at h
  exact fun heq => by simp [heq] at h

/-- Nodup is preserved by `removeRunnable`. -/
theorem removeRunnable_nodup
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hNd : st.scheduler.runnable.Nodup) :
    (removeRunnable st tid).scheduler.runnable.Nodup :=
  List.Nodup.sublist List.filter_sublist hNd

/-- If `x` is in the runnable list of `ensureRunnable st tid`,
then `x` was already runnable or `x = tid`. -/
theorem ensureRunnable_mem_implies
    (st : SystemState) (tid x : SeLe4n.ThreadId)
    (h : x ∈ (ensureRunnable st tid).scheduler.runnable) :
    x ∈ st.scheduler.runnable ∨ x = tid := by
  by_cases hMem : tid ∈ st.scheduler.runnable
  · have : ensureRunnable st tid = st := by simp [ensureRunnable, hMem]
    rw [this] at h; exact .inl h
  · have : (ensureRunnable st tid).scheduler.runnable = st.scheduler.runnable ++ [tid] := by
      simp [ensureRunnable, hMem]
    rw [this] at h
    rcases List.mem_append.mp h with h1 | h2
    · exact .inl h1
    · exact .inr (List.mem_singleton.mp h2)

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

end SeLe4n.Kernel
