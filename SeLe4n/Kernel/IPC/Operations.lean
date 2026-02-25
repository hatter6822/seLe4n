import SeLe4n.Model.State

namespace SeLe4n.Kernel

open SeLe4n.Model

def removeRunnable (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  {
    st with
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

    H-09/WS-E3: When the sender blocks (idle→send or send→send transitions),
    the sender's IPC state is set to `.blockedOnSend endpointId` and the sender
    is removed from the runnable queue. When a waiting receiver is present
    (receive→idle handshake), the sender does not block. -/
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
            | [], some _ =>
                let ep' : Endpoint := { state := .idle, queue := [], waitingReceiver := none }
                storeObject endpointId (.endpoint ep') st
            | _, _ => .error .endpointStateMismatch
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

/-- Register one waiting receiver on an idle endpoint.

    H-09/WS-E3: The receiver's IPC state is set to `.blockedOnReceive endpointId`
    and the receiver is removed from the runnable queue. -/
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

    H-09/WS-E3: The dequeued sender's IPC state is set to `.ready` and the
    sender is added back to the runnable queue via `ensureRunnable`. -/
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

/-- `storeTcbIpcState` preserves endpoint objects (it only writes TCBs). -/
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
    subst hStep
    exact hEp
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc epId hEq hStep]
    exact hEp

/-- `storeTcbIpcState` backward for endpoints: if the output has an endpoint at some ID,
    the input had the same endpoint (since `storeTcbIpcState` only writes TCBs). -/
theorem storeTcbIpcState_endpoint_backward
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (epId : SeLe4n.ObjId)
    (ep : Endpoint)
    (hPost : st'.objects epId = some (.endpoint ep))
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st.objects epId = some (.endpoint ep) := by
  unfold storeTcbIpcState at hStep
  cases hTcb : lookupTcb st tid with
  | none =>
    simp [hTcb] at hStep
    subst hStep; exact hPost
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq : pair.snd = st' := Except.ok.inj hStep; subst hEq
      by_cases hIdEq : epId = tid.toObjId
      · rw [hIdEq, storeObject_objects_eq st pair.2 tid.toObjId _ hStore] at hPost
        cases hPost
      · rw [storeObject_objects_ne st pair.2 tid.toObjId epId _ hIdEq hStore] at hPost
        exact hPost

/-- `storeTcbIpcState` backward for notifications: if the output has a notification at some ID,
    the input had the same notification (since `storeTcbIpcState` only writes TCBs). -/
theorem storeTcbIpcState_notification_backward
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (nid : SeLe4n.ObjId)
    (ntfn : Notification)
    (hPost : st'.objects nid = some (.notification ntfn))
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st.objects nid = some (.notification ntfn) := by
  unfold storeTcbIpcState at hStep
  cases hTcb : lookupTcb st tid with
  | none =>
    simp [hTcb] at hStep
    subst hStep; exact hPost
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq : pair.snd = st' := Except.ok.inj hStep; subst hEq
      by_cases hIdEq : nid = tid.toObjId
      · rw [hIdEq, storeObject_objects_eq st pair.2 tid.toObjId _ hStore] at hPost
        cases hPost
      · rw [storeObject_objects_ne st pair.2 tid.toObjId nid _ hIdEq hStore] at hPost
        exact hPost

/-- `storeTcbIpcState` preserves the scheduler state. -/
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
    subst hStep; rfl
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq : pair.snd = st' := Except.ok.inj hStep
      subst hEq
      exact storeObject_scheduler_eq st pair.2 tid.toObjId
        (.tcb { tcb with ipcState := ipc }) hStore

/-- `removeRunnable` only modifies the scheduler; all objects are preserved. -/
theorem removeRunnable_preserves_objects
    (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    (removeRunnable st tid).objects = st.objects := by
  rfl

/-- `ensureRunnable` only modifies the scheduler; all objects are preserved. -/
theorem ensureRunnable_preserves_objects
    (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    (ensureRunnable st tid).objects = st.objects := by
  unfold ensureRunnable
  split <;> rfl

/-- `removeRunnable` membership: a thread is in the resulting runnable list iff it was
    in the original list and is not the removed thread. -/
theorem removeRunnable_mem_iff
    (st : SystemState) (tid tid' : SeLe4n.ThreadId) :
    tid' ∈ (removeRunnable st tid).scheduler.runnable ↔
      tid' ∈ st.scheduler.runnable ∧ tid' ≠ tid := by
  simp [removeRunnable, List.mem_filter]

/-- `removeRunnable` sets `current` to `none` when removing the current thread. -/
theorem removeRunnable_current
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeRunnable st tid).scheduler.current =
      if st.scheduler.current = some tid then none else st.scheduler.current := by
  rfl

/-- `ensureRunnable` membership: a thread is in the resulting runnable list iff it was
    already there or it is the added thread. -/
theorem ensureRunnable_mem_iff
    (st : SystemState) (tid tid' : SeLe4n.ThreadId) :
    tid' ∈ (ensureRunnable st tid).scheduler.runnable ↔
      tid' ∈ st.scheduler.runnable ∨ tid' = tid := by
  unfold ensureRunnable
  split
  case isTrue h => exact ⟨fun hm => Or.inl hm, fun ho => ho.elim id (fun h' => h' ▸ h)⟩
  case isFalse h =>
    simp [List.mem_append]

/-- `ensureRunnable` preserves `current`. -/
theorem ensureRunnable_current
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (ensureRunnable st tid).scheduler.current = st.scheduler.current := by
  unfold ensureRunnable
  split <;> rfl

/-- `storeTcbIpcState` sets the IPC state on the target TCB (if it exists). -/
theorem storeTcbIpcState_objects_at
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    (∃ tcb, st.objects tid.toObjId = some (.tcb tcb) ∧
            st'.objects tid.toObjId = some (.tcb { tcb with ipcState := ipc })) ∨
    (lookupTcb st tid = none ∧ st' = st) := by
  unfold storeTcbIpcState at hStep
  cases hTcb : lookupTcb st tid with
  | none =>
    simp [hTcb] at hStep; subst hStep
    exact Or.inr ⟨rfl, rfl⟩
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq : pair.snd = st' := Except.ok.inj hStep; subst hEq
      have hLookup : st.objects tid.toObjId = some (.tcb tcb) := by
        unfold lookupTcb at hTcb
        cases hObj : st.objects tid.toObjId with
        | none => simp [hObj] at hTcb
        | some obj => cases obj <;> simp_all
      exact Or.inl ⟨tcb, hLookup,
        storeObject_objects_eq st pair.2 tid.toObjId _ hStore⟩

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
-- H-09/WS-E3: Service preservation lemmas for compound IPC non-interference
-- ============================================================================

/-- `removeRunnable` only modifies the scheduler; services are preserved. -/
theorem removeRunnable_preserves_services
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeRunnable st tid).services = st.services := by
  rfl

/-- `ensureRunnable` only modifies the scheduler; services are preserved. -/
theorem ensureRunnable_preserves_services
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (ensureRunnable st tid).services = st.services := by
  unfold ensureRunnable; split <;> rfl

/-- `storeTcbIpcState` only modifies objects; services are preserved. -/
theorem storeTcbIpcState_preserves_services
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.services = st.services := by
  unfold storeTcbIpcState at hStep
  split at hStep
  · simp at hStep; subst hStep; rfl
  · split at hStep
    · exact absurd hStep (by simp)
    · rename_i st'' hStore
      simp at hStep; subst hStep
      exact storeObject_preserves_services _ _ _ _ hStore

end SeLe4n.Kernel
