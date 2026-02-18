import SeLe4n.Model.State

namespace SeLe4n.Kernel

open SeLe4n.Model

private def removeRunnable (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  {
    st with
      scheduler := { st.scheduler with runnable := st.scheduler.runnable.filter (· ≠ tid) }
  }

private def ensureRunnable (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  if tid ∈ st.scheduler.runnable then
    st
  else
    { st with scheduler := { st.scheduler with runnable := st.scheduler.runnable ++ [tid] } }

private def lookupTcb (st : SystemState) (tid : SeLe4n.ThreadId) : Option TCB :=
  match st.objects tid.toObjId with
  | some (.tcb tcb) => some tcb
  | _ => none

private def storeTcbIpcState (st : SystemState) (tid : SeLe4n.ThreadId) (ipcState : ThreadIpcState) : Except KernelError SystemState :=
  match lookupTcb st tid with
  | none => .ok st
  | some tcb =>
      match storeObject tid.toObjId (.tcb { tcb with ipcState := ipcState }) st with
      | .error e => .error e
      | .ok ((), st') => .ok st'

/-- Add a sender to an endpoint wait queue with explicit state transition. -/
def endpointSend (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) : Kernel Unit :=
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

/-- Register one waiting receiver on an idle endpoint. -/
def endpointAwaitReceive (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) : Kernel Unit :=
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

/-- Consume one queued sender from an endpoint wait queue. -/
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
            | .ok ((), st') => .ok (sender, st')
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

/-- Wait on a notification: consume pending badge or block the caller. -/
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

end SeLe4n.Kernel
