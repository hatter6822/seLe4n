/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.DualQueue.Transport

/-! # Z7: SchedContext Donation / Passive Servers

SchedContext donation enables passive servers — threads that consume zero CPU
when idle by borrowing the client's SchedContext during IPC Call/Reply.

## Donation Protocol

1. Client calls server via `endpointCall`. If the server is passive (unbound),
   the client's SchedContext is temporarily donated to the server.
2. Server receives `.donated(clientScId, clientTid)` binding. The SchedContext's
   `boundThread` is updated to point to the server.
3. Server runs on the client's CPU budget.
4. Server replies via `endpointReply` or `endpointReplyRecv`. The SchedContext
   is returned to the original client.
5. Server becomes passive again (unbound, not in RunQueue).

## Architecture

The donation logic is implemented as post-processing wrappers around the
existing IPC primitives (`endpointCall`, `endpointReply`, `endpointReplyRecv`).
This design preserves all existing IPC invariant proofs unchanged — the core
IPC functions are not modified. Donation is applied after the core operation
completes, modifying only `schedContextBinding` fields and RunQueue membership.

## Cross-cutting: Timeout + Donation

When a client's SchedContext is donated to a server and the budget expires:
- The server is preempted (budget exhaustion via `timerTickBudget`)
- The client is timed out (budget-bounded IPC via `timeoutBlockedThreads`)
- The SchedContext returns to the client via timeout cleanup, not reply
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- Z7-B: Post-call donation (endpointCall → donation to passive server)
-- ============================================================================

/-- Z7-B: Apply SchedContext donation after a successful `endpointCall`.

After the caller blocks on reply and the receiver is woken, check if:
1. The receiver is passive (schedContextBinding = .unbound)
2. The caller has a bound SchedContext

If both conditions hold, donate the caller's SchedContext to the receiver.
Otherwise, return the state unchanged.

This function modifies only `objects` (SchedContext and TCB schedContextBinding
fields). It does NOT modify the scheduler RunQueue or current thread. -/
def applyCallDonation
    (st : SystemState)
    (caller : SeLe4n.ThreadId) (receiver : SeLe4n.ThreadId) : SystemState :=
  -- Check if receiver is passive
  match lookupTcb st receiver with
  | none => st
  | some receiverTcb =>
    match receiverTcb.schedContextBinding with
    | .unbound =>
      -- Receiver is passive — check if caller has a SchedContext to donate
      match lookupTcb st caller with
      | none => st
      | some callerTcb =>
        match callerTcb.schedContextBinding with
        | .bound clientScId =>
          match donateSchedContext st caller receiver clientScId with
          | .error _ => st
          | .ok st' => st'
        | _ => st
    | _ => st  -- Receiver already has SC, no donation needed

/-- Z7-B: storeObject preserves scheduler. -/
private theorem storeObject_scheduler_eq_local (st : SystemState) (oid : SeLe4n.ObjId)
    (obj : KernelObject) (pair : Unit × SystemState)
    (h : storeObject oid obj st = .ok pair) :
    pair.2.scheduler = st.scheduler := by
  unfold storeObject at h; cases h; rfl

/-- Z7-B: donateSchedContext only modifies objects — scheduler is preserved. -/
theorem donateSchedContext_scheduler_eq
    (st st' : SystemState)
    (clientTid serverTid : SeLe4n.ThreadId)
    (clientScId : SeLe4n.SchedContextId)
    (h : donateSchedContext st clientTid serverTid clientScId = .ok st') :
    st'.scheduler = st.scheduler := by
  unfold donateSchedContext at h
  revert h
  cases hObj : st.objects[clientScId.toObjId]? with
  | none => intro h; cases h
  | some obj =>
    cases obj with
    | schedContext sc =>
      simp only []
      cases hS1 : storeObject clientScId.toObjId _ st with
      | error _ => intro h; cases h
      | ok p1 =>
        simp only []
        cases hLookup : lookupTcb p1.2 serverTid with
        | none => intro h; cases h
        | some _ =>
          simp only []
          cases hS2 : storeObject serverTid.toObjId _ p1.2 with
          | error _ => intro h; cases h
          | ok p2 =>
            simp only [Except.ok.injEq]
            intro hEq; subst hEq
            have h1 := storeObject_scheduler_eq_local st _ _ _ hS1
            have h2 := storeObject_scheduler_eq_local p1.2 _ _ _ hS2
            exact h2.trans h1
    | _ => simp only []; intro h; cases h

/-- Z7-B: applyCallDonation preserves the scheduler exactly. -/
theorem applyCallDonation_scheduler_eq
    (st : SystemState) (caller receiver : SeLe4n.ThreadId) :
    (applyCallDonation st caller receiver).scheduler = st.scheduler := by
  unfold applyCallDonation
  cases hRecv : lookupTcb st receiver with
  | none => rfl
  | some receiverTcb =>
    simp only []
    cases hBinding : receiverTcb.schedContextBinding with
    | unbound =>
      simp only []
      cases hCaller : lookupTcb st caller with
      | none => rfl
      | some callerTcb =>
        simp only []
        cases hCallerBinding : callerTcb.schedContextBinding with
        | unbound => rfl
        | bound clientScId =>
          simp only []
          cases hDonate : donateSchedContext st caller receiver clientScId with
          | error _ => rfl
          | ok st' => exact donateSchedContext_scheduler_eq st st' caller receiver clientScId hDonate
        | donated scId owner => rfl
    | bound scId => rfl
    | donated scId owner => rfl

-- ============================================================================
-- Z7-C: Post-reply donation return (endpointReply → return SC to client)
-- ============================================================================

/-- Z7-C: Apply SchedContext return after a successful `endpointReply`.

If the replier has a donated SchedContext binding (.donated scId originalOwner),
return the SchedContext to the original owner and remove the (now passive)
replier from the RunQueue. Otherwise, return the state unchanged. -/
def applyReplyDonation (st : SystemState) (replier : SeLe4n.ThreadId) : SystemState :=
  match lookupTcb st replier with
  | none => st
  | some replierTcb =>
    match replierTcb.schedContextBinding with
    | .donated scId originalOwner =>
      match returnDonatedSchedContext st replier scId originalOwner with
      | .error _ => st
      | .ok st' => removeRunnable st' replier
    | _ => st

-- ============================================================================
-- Z7-E: Pre-receive donation cleanup
-- ============================================================================

/-- Z7-E: Clean up stale donation before a server blocks on receive.

If the receiver has a `.donated` binding from a previous call that was never
replied to (abnormal path), return the SchedContext to the original owner
before blocking. Otherwise, return the state unchanged. -/
def cleanupPreReceiveDonation (st : SystemState) (receiver : SeLe4n.ThreadId) : SystemState :=
  match lookupTcb st receiver with
  | none => st
  | some recvTcb =>
    match recvTcb.schedContextBinding with
    | .donated scId originalOwner =>
      match returnDonatedSchedContext st receiver scId originalOwner with
      | .error _ => st
      | .ok st' => st'
    | _ => st

-- ============================================================================
-- Z7: Donation-aware IPC operation wrappers
-- ============================================================================

/-- Z7: Donation-aware endpointCall. Composes the standard `endpointCall` with
post-call SchedContext donation to passive servers.

Before calling `endpointCall`, checks if the endpoint has a waiting receiver
(handshake path). If so, records the receiver's ThreadId. After `endpointCall`
completes, applies donation from the caller to the receiver if the receiver
was passive (unbound). -/
def endpointCallWithDonation
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) : Kernel Unit :=
  fun st =>
    -- Pre-check: determine receiver before endpointCall pops it
    let maybeReceiver := match st.objects[endpointId]? with
      | some (.endpoint ep) => ep.receiveQ.head
      | _ => none
    match endpointCall endpointId caller msg st with
    | .error e => .error e
    | .ok ((), st') =>
      match maybeReceiver with
      | some receiverTid =>
        -- Handshake path: a receiver was woken — apply donation
        .ok ((), applyCallDonation st' caller receiverTid)
      | none =>
        -- Blocking path: no receiver was available, caller blocked
        .ok ((), st')

/-- Z7: Donation-aware endpointReply. Composes the standard `endpointReply`
with post-reply SchedContext return from the server. -/
def endpointReplyWithDonation
    (replier : SeLe4n.ThreadId) (target : SeLe4n.ThreadId)
    (msg : IpcMessage) : Kernel Unit :=
  fun st =>
    match endpointReply replier target msg st with
    | .error e => .error e
    | .ok ((), st') =>
      -- Apply donation return: if replier has donated SC, return it
      .ok ((), applyReplyDonation st' replier)

/-- Z7: Donation-aware endpointReplyRecv. Composes:
1. Standard endpointReplyRecv (reply + receive) — server still holds donated SC during reply
2. Return old donation from replier AFTER the reply completes
3. (New donation from incoming caller is handled by the Call path)

**Ordering rationale (AUD-3)**: The donation return happens AFTER `endpointReplyRecv`
completes, not before. The server needs the donated SchedContext while replying
(it's the currently running thread with that SC's budget). After the reply delivers
the message and the server enters the receive path, the SC is returned. -/
def endpointReplyRecvWithDonation
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (replyTarget : SeLe4n.ThreadId)
    (msg : IpcMessage) : Kernel Unit :=
  fun st =>
    match endpointReplyRecv endpointId receiver replyTarget msg st with
    | .error e => .error e
    | .ok ((), st') =>
      -- Z7-D1: Return old donation AFTER reply+receive completes
      .ok ((), applyReplyDonation st' receiver)

end SeLe4n.Kernel
