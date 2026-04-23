/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.DualQueue.Transport
import SeLe4n.Kernel.Scheduler.PriorityInheritance.Propagate
import SeLe4n.Kernel.IPC.Operations.Donation.Primitives

/-! # Z7: Donation Transport-Dependent Wrappers

SchedContext donation enables passive servers - threads that consume zero CPU
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

## Architecture (post-AN3-A / H-01)

The donation logic is split across two sibling modules:

* `SeLe4n.Kernel.IPC.Operations.Donation.Primitives` - transport-independent
  helpers (`applyCallDonation`, `applyReplyDonation`, all `*_scheduler_eq` /
  `*_machine_eq` / `*_atomicRegion` preservation theorems, server binding
  witnesses). Re-exported by `SeLe4n.Kernel.IPC.Operations` (the IPC operations
  hub).
* This file - donation-aware wrappers around the core transport-layer IPC
  entry points (`endpointCallWithDonation`, `endpointReplyWithDonation`,
  `endpointReplyRecvWithDonation`). These unavoidably depend on
  `SeLe4n.Kernel.IPC.DualQueue.Transport`, so re-exporting this file from
  the operations hub would reintroduce the `Operations -> Donation ->
  Transport -> Core -> Operations` import cycle closed by AI4-A.

Legacy consumers that `import SeLe4n.Kernel.IPC.Operations.Donation` continue
to see the full donation API, because this file re-exports the primitives via
its `import SeLe4n.Kernel.IPC.Operations.Donation.Primitives` line.

This design preserves all existing IPC invariant proofs unchanged - the core
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
-- Z7: Donation-aware IPC operation wrappers (transport-dependent subset)
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
    -- Pre-check: determine receiver before endpointCall pops it.
    -- AJ1-C (M-02): `endpointQueuePopHead_returns_head` proves the pre-inspected
    -- receiver matches the thread actually dequeued by endpointCall, ensuring
    -- donation targets the correct thread.
    let maybeReceiver := match st.objects[endpointId]? with
      | some (.endpoint ep) => ep.receiveQ.head
      | _ => none
    match endpointCall endpointId caller msg st with
    | .error e => .error e
    | .ok ((), st') =>
      match maybeReceiver with
      | some receiverTid =>
        -- Handshake path: a receiver was woken — apply donation
        -- AH2-C: Propagate donation errors
        match applyCallDonation st' caller receiverTid with
        | .error e => .error e
        | .ok st'' =>
          -- D4-L: Apply PIP — propagate priority inheritance from the server
          -- upward through the blocking chain. The server may itself be blocked
          -- on another server, requiring transitive propagation.
          .ok ((), PriorityInheritance.propagatePriorityInheritance st'' receiverTid)
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
      -- AH2-C: Propagate donation return errors
      match applyReplyDonation st' replier with
      | .error e => .error e
      | .ok st'' =>
        -- D4-M: Revert PIP — the client (target) is unblocked, so the replier's
        -- pipBoost must be recomputed from remaining waiters. Propagate reversion
        -- upward through the chain.
        .ok ((), PriorityInheritance.revertPriorityInheritance st'' replier)

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
      -- AH2-C: Propagate donation return errors
      match applyReplyDonation st' receiver with
      | .error e => .error e
      | .ok st'' =>
        -- D4-M: Revert PIP for the reply portion
        .ok ((), PriorityInheritance.revertPriorityInheritance st'' receiver)

-- ============================================================================
-- AJ1-D (M-01): Decomposition lemmas for donation-aware wrappers
-- ============================================================================

/-- AJ1-D (M-01): `endpointReplyWithDonation` decomposes into the three-step
sequence: `endpointReply` → `applyReplyDonation` → `revertPriorityInheritance`.
This is a definitional unfolding — the wrapper is syntactic sugar for the
three-step pipeline. The `dispatchWithCapChecked` `.reply` arm manually inlines
this same three-step sequence (via `endpointReplyChecked` + inline donation +
inline PIP revert), making the two paths structurally identical when the
information flow check passes. -/
theorem endpointReplyWithDonation_unfold
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (st : SystemState) :
    endpointReplyWithDonation replier target msg st =
    (match endpointReply replier target msg st with
     | .error e => .error e
     | .ok ((), st') =>
       match applyReplyDonation st' replier with
       | .error e => .error e
       | .ok st'' =>
         .ok ((), PriorityInheritance.revertPriorityInheritance st'' replier)) := by
  rfl

/-- AJ1-D (M-01): `endpointReplyRecvWithDonation` decomposes into:
`endpointReplyRecv` → `applyReplyDonation` → `revertPriorityInheritance`. -/
theorem endpointReplyRecvWithDonation_unfold
    (endpointId : SeLe4n.ObjId) (receiver replyTarget : SeLe4n.ThreadId)
    (msg : IpcMessage) (st : SystemState) :
    endpointReplyRecvWithDonation endpointId receiver replyTarget msg st =
    (match endpointReplyRecv endpointId receiver replyTarget msg st with
     | .error e => .error e
     | .ok ((), st') =>
       match applyReplyDonation st' receiver with
       | .error e => .error e
       | .ok st'' =>
         .ok ((), PriorityInheritance.revertPriorityInheritance st'' receiver)) := by
  rfl

end SeLe4n.Kernel
