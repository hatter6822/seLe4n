import SeLe4n.Model.State

namespace SeLe4n.Kernel

open SeLe4n.Model

def removeRunnable (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  {
    st with
      scheduler := { st.scheduler with runnable := st.scheduler.runnable.filter (· ≠ tid) }
  }

def ensureRunnable (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  if tid ∈ st.scheduler.runnable then
    st
  else
    { st with scheduler := { st.scheduler with runnable := st.scheduler.runnable ++ [tid] } }

/-- H-09 (WS-E3): Combined block operation that removes a thread from the runnable
queue and clears the current-thread field if the blocked thread was current.
This is semantically correct: a blocked thread cannot be the currently-executing
thread. The combined operation maintains `queueCurrentConsistent`. -/
def blockThread (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  let st' := removeRunnable st tid
  match st'.scheduler.current with
  | some cur => if cur = tid then { st' with scheduler := { st'.scheduler with current := none } } else st'
  | none => st'

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

-- ============================================================================
-- Core endpoint operations: endpoint-object-only transitions.
-- These are the internal building blocks. The public operations compose these
-- with IPC state effects (storeTcbIpcState + blockThread/ensureRunnable).
-- All invariant proofs target these core operations.
-- ============================================================================

/-- Core endpoint send: updates only the endpoint object. -/
def endpointSendCore (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) : Kernel Unit :=
  fun st =>
    match st.objects endpointId with
    | some (.endpoint ep) =>
        match ep.state with
        | .idle =>
            let ep' : Endpoint := { state := .send, queue := [sender], waitingReceiver := none }
            storeObject endpointId (.endpoint ep') st
        | .send =>
            let ep' : Endpoint := { state := .send, queue := ep.queue ++ [sender], waitingReceiver := none }
            storeObject endpointId (.endpoint ep') st
        | .receive =>
            match ep.queue, ep.waitingReceiver with
            | [], some _ =>
                let ep' : Endpoint := { state := .idle, queue := [], waitingReceiver := none }
                storeObject endpointId (.endpoint ep') st
            | _, _ => .error .endpointStateMismatch
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

/-- Core endpoint await-receive: updates only the endpoint object. -/
def endpointAwaitReceiveCore (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) : Kernel Unit :=
  fun st =>
    match st.objects endpointId with
    | some (.endpoint ep) =>
        match ep.state, ep.queue, ep.waitingReceiver with
        | .idle, [], none =>
            let ep' : Endpoint := { state := .receive, queue := [], waitingReceiver := some receiver }
            storeObject endpointId (.endpoint ep') st
        | .idle, _, _ => .error .endpointStateMismatch
        | .send, _, _ => .error .endpointStateMismatch
        | .receive, _, _ => .error .endpointStateMismatch
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

/-- Core endpoint receive: updates only the endpoint object. -/
def endpointReceiveCore (endpointId : SeLe4n.ObjId) : Kernel SeLe4n.ThreadId :=
  fun st =>
    match st.objects endpointId with
    | some (.endpoint ep) =>
        match ep.state, ep.queue, ep.waitingReceiver with
        | .send, sender :: rest, none =>
            let nextState : EndpointState := if rest.isEmpty then .idle else .send
            let ep' : Endpoint := { state := nextState, queue := rest, waitingReceiver := none }
            match storeObject endpointId (.endpoint ep') st with
            | .error e => .error e
            | .ok ((), st') => .ok (sender, st')
        | .send, [], none => .error .endpointQueueEmpty
        | .send, _, some _ => .error .endpointStateMismatch
        | .idle, _, _ => .error .endpointStateMismatch
        | .receive, _, _ => .error .endpointStateMismatch
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

-- ============================================================================
-- Public endpoint operations: core + IPC state effects.
-- H-09 (WS-E3): These compose the core endpoint transition with thread
-- IPC state management and scheduler changes.
-- ============================================================================

/-- Determine which thread to block/unblock after endpointSend.
Returns `(.block sender)` for idle/send paths and `(.unblock receiver)` for rendezvous. -/
inductive SendEffect where
  | blockSender (sender : SeLe4n.ThreadId) (endpointId : SeLe4n.ObjId)
  | unblockReceiver (receiver : SeLe4n.ThreadId)

/-- Extract the effect for endpointSend from the pre-state. -/
def endpointSendEffect (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (st : SystemState) : Option SendEffect :=
  match st.objects endpointId with
  | some (.endpoint ep) =>
      match ep.state with
      | .idle => some (.blockSender sender endpointId)
      | .send => some (.blockSender sender endpointId)
      | .receive =>
          match ep.queue, ep.waitingReceiver with
          | [], some receiver => some (.unblockReceiver receiver)
          | _, _ => none
  | _ => none

/-- Apply IPC effects after a core endpoint step. -/
def applyBlockEffect (st : SystemState) (tid : SeLe4n.ThreadId)
    (ipcState : ThreadIpcState) : Except KernelError SystemState :=
  match storeTcbIpcState st tid ipcState with
  | .error e => .error e
  | .ok st' => .ok (blockThread st' tid)

def applyUnblockEffect (st : SystemState) (tid : SeLe4n.ThreadId) :
    Except KernelError SystemState :=
  match storeTcbIpcState st tid .ready with
  | .error e => .error e
  | .ok st' => .ok (ensureRunnable st' tid)

/-- Add a sender to an endpoint wait queue with explicit state transition.

H-09 (WS-E3): When the sender blocks (idle/send paths), its IPC state is set
to `.blockedOnSend endpointId` and it is removed from the runnable queue.
When a waiting receiver is present (receive path), the receiver is unblocked
(IPC state set to `.ready`, added to runnable queue). -/
def endpointSend (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) : Kernel Unit :=
  fun st =>
    match endpointSendEffect endpointId sender st with
    | none =>
        -- Fallthrough to core for error reporting
        endpointSendCore endpointId sender st
    | some effect =>
        match endpointSendCore endpointId sender st with
        | .error e => .error e
        | .ok ((), stCore) =>
            match effect with
            | .blockSender s eid =>
                match applyBlockEffect stCore s (.blockedOnSend eid) with
                | .error e => .error e
                | .ok st' => .ok ((), st')
            | .unblockReceiver r =>
                match applyUnblockEffect stCore r with
                | .error e => .error e
                | .ok st' => .ok ((), st')

/-- Register one waiting receiver on an idle endpoint.

H-09 (WS-E3): The receiver's IPC state is set to `.blockedOnReceive endpointId`
and the receiver is removed from the runnable queue, making the
`blockedOnReceiveNotRunnable` contract predicate non-vacuous. -/
def endpointAwaitReceive (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) : Kernel Unit :=
  fun st =>
    match endpointAwaitReceiveCore endpointId receiver st with
    | .error e => .error e
    | .ok ((), stCore) =>
        match applyBlockEffect stCore receiver (.blockedOnReceive endpointId) with
        | .error e => .error e
        | .ok st' => .ok ((), st')

/-- Consume one queued sender from an endpoint wait queue.

H-09 (WS-E3): The dequeued sender is unblocked: its IPC state is set to
`.ready` and it is added to the runnable queue via `ensureRunnable`, making
the `blockedOnSendNotRunnable` contract predicate non-vacuous. -/
def endpointReceive (endpointId : SeLe4n.ObjId) : Kernel SeLe4n.ThreadId :=
  fun st =>
    match endpointReceiveCore endpointId st with
    | .error e => .error e
    | .ok (sender, stCore) =>
        match applyUnblockEffect stCore sender with
        | .error e => .error e
        | .ok st' => .ok (sender, st')

-- ============================================================================
-- Key properties of effects: they preserve objects
-- ============================================================================

theorem blockThread_preserves_objects
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (blockThread st tid).objects = st.objects := by
  unfold blockThread
  have : (removeRunnable st tid).objects = st.objects := rfl
  cases h : (removeRunnable st tid).scheduler.current with
  | none => simp [h, this]
  | some cur =>
      by_cases hEq : cur = tid
      · simp [h, hEq]; exact this
      · simp [h, hEq]; exact this

theorem ensureRunnable_preserves_objects
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (ensureRunnable st tid).objects = st.objects := by
  unfold ensureRunnable
  by_cases hMem : tid ∈ st.scheduler.runnable <;> simp [hMem]

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

theorem storeTcbIpcState_scheduler_eq
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
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

/-- Core property: applyBlockEffect preserves objects at all IDs except possibly the thread's ObjId. -/
theorem applyBlockEffect_preserves_objects_ne
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (oid : SeLe4n.ObjId) (hNe : oid ≠ tid.toObjId)
    (hStep : applyBlockEffect st tid ipc = .ok st') :
    st'.objects oid = st.objects oid := by
  unfold applyBlockEffect at hStep
  cases hTcb : storeTcbIpcState st tid ipc with
  | error e => simp [hTcb] at hStep
  | ok stMid =>
    simp only [hTcb] at hStep
    have hEq : blockThread stMid tid = st' := Except.ok.inj hStep
    subst hEq
    rw [blockThread_preserves_objects]
    exact storeTcbIpcState_preserves_objects_ne st stMid tid ipc oid hNe hTcb

/-- Core property: applyUnblockEffect preserves objects at all IDs except possibly the thread's ObjId. -/
theorem applyUnblockEffect_preserves_objects_ne
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (oid : SeLe4n.ObjId) (hNe : oid ≠ tid.toObjId)
    (hStep : applyUnblockEffect st tid = .ok st') :
    st'.objects oid = st.objects oid := by
  unfold applyUnblockEffect at hStep
  cases hTcb : storeTcbIpcState st tid .ready with
  | error e => simp [hTcb] at hStep
  | ok stMid =>
    simp only [hTcb] at hStep
    have hEq : ensureRunnable stMid tid = st' := Except.ok.inj hStep
    subst hEq
    rw [ensureRunnable_preserves_objects]
    exact storeTcbIpcState_preserves_objects_ne st stMid tid .ready oid hNe hTcb

-- ============================================================================
-- Signal and wait notification operations (unchanged)
-- ============================================================================

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
