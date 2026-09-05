-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.DualQueue.Transport
import SeLe4n.Kernel.IPC.Operations.CapTransfer

/-! # IPC Dual-Queue WithCaps Wrappers (M-D01 / WS-M3)

Wrapper operations that compose existing dual-queue IPC operations with
`ipcUnwrapCaps` as a post-step for capability transfer during rendezvous.

These wrappers preserve all existing operation signatures and proofs.
The cap unwrap only occurs when an immediate rendezvous happens (a receiver
was waiting on the endpoint). When the sender is enqueued (no receiver),
caps stay in the message and will be unwrapped when a receiver later arrives.

**Design decision**: The wrappers read the receiver's `cspaceRoot` from the
receiver's TCB internally, rather than accepting it as a parameter. This
ensures correctness when the receiver's identity is determined dynamically
during the rendezvous.

**AE4-I (U-37/I-WC01): Per-slot capability transfer targeting**: The
`receiverSlotBase` parameter is fully plumbed from the API dispatch layer
through to `ipcUnwrapCaps` → `ipcTransferSingleCap`, which scans for empty
slots starting at `receiverSlotBase`. The `SyscallDecodeResult.capRecvSlot`
field carries the receiver's requested slot base (default: `Slot.ofNat 0`).

For multiple cap transfers (up to `maxExtraCaps = 3`), `ipcUnwrapCapsLoop`
advances the slot cursor via `findFirstEmptySlot` after each successful
insertion, placing caps at consecutive empty slots starting from
`receiverSlotBase`. Each transferred cap gets its own unique CDT entry,
enabling precise per-cap revocation.

**Current status**: The receiver slot base defaults to `Slot.ofNat 0`
because the receiver-side extraction from the IPC buffer is not yet
implemented (requires H3 IPC buffer layout). The full plumbing is in
place: when receiver-side decode populates `capRecvSlot`, per-slot
targeting will activate without any additional code changes.

**CDT tracking**: Each transferred capability is tracked individually
in the CDT via `ensureCdtNodeForSlot` with the actual target slot
(not a shared slot). Revocation is precise per-capability.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- M-D01: Helper to read a thread's CSpace root ObjId from its TCB.
    AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration. -/
def lookupCspaceRoot (st : SystemState) (tid : SeLe4n.ThreadId)
    : Option SeLe4n.ObjId :=
  st.getTcb? tid |>.map (·.cspaceRoot)

/-- **WS-RR RR7.8: the CSpace root a caps-carrying rendezvous writes**, resolved
from the **pre**-state.

The send and call WithCaps arms both install the transferred capabilities into
the receiver's CSpace root, and `ipcTransferSingleCap` writes the CNode there.
A declared lock footprint has to name that object, and it has to name it from
the state whose locks the bracket took — so this reads `st`, and since RR7.8
both arms read the receiver's root from `st` as well.  (They read it from the
*post*-state before; the two agree, because nothing between them writes
`TCB.cspaceRoot` — thread creation is its only writer — but "the states agree"
is a fact about the tree that a later transition could falsify silently, while
"both read the same state" is a fact about the code.)

`none` covers the three shapes that install nothing: a message carrying no
capabilities, an endpoint with no waiting receiver, and a receiver whose TCB
does not resolve.  The last is the fail-closed arm the transitions take as
`.error .invalidCapability`; it declares no destination because it writes
none. -/
def rendezvousCapsDestination? (st : SystemState) (endpointId : SeLe4n.ObjId)
    (msg : IpcMessage) : Option SeLe4n.ObjId :=
  if msg.caps.isEmpty then none
  else ((st.getEndpoint? endpointId).bind (·.receiveQ.head)).bind (lookupCspaceRoot st)

/-- M-D01: Extended send with capability transfer. Composes `endpointSendDual`
with `ipcUnwrapCaps` as a post-step when immediate rendezvous occurs.

Semantics:
- First checks if a receiver is waiting on the endpoint's receiveQ.
- Sends the message via `endpointSendDual`.
- If immediate rendezvous occurred (receiver was waiting): reads the
  receiver's cspaceRoot from their TCB and unwraps `msg.caps` into the
  receiver's CSpace.
- If no receiver was waiting (sender enqueued): caps stay in the message
  stored in the sender's TCB. They will be unwrapped when a receiver
  later dequeues the sender.
- The `endpointRights` parameter carries the endpoint capability's rights
  from the sender's gate — used to check the `Grant` right gate.

Returns the cap transfer summary (empty if no immediate rendezvous or if
the endpoint lacks Grant right). -/
def endpointSendDualWithCaps
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (senderCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) : Kernel CapTransferSummary :=
  fun st =>
    -- PR #873 round 13: **the endpoint's grant right is stamped into the
    -- message**, because the message is where both orderings read it.  The
    -- immediate rendezvous below consulted `endpointRights` while a queued send
    -- left `msg.capsGranted` untouched for the later unwrap to read, so a caller
    -- that passed granting rights with the field's `false` default transferred
    -- capabilities on rendezvous and none after parking -- capability delivery
    -- decided by which side reached the endpoint first, the order-dependence
    -- round 6 removed from the receive side.  One authority, recorded once, read
    -- once.
    -- Check if a receiver is waiting BEFORE the send.
    -- AJ1-C (M-02): `endpointQueuePopHead_returns_head` proves the pre-inspected
    -- receiver matches the thread actually dequeued, ensuring capability transfer
    -- targets the correct thread.
    -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration.
    let hasReceiver := match st.getEndpoint? endpointId with
      | some ep => ep.receiveQ.head.isSome
      | none    => false
    match endpointSendDual endpointId sender { msg with capsGranted := endpointRights.mem .grant } st with
    | .error e => .error e
    | .ok ((), st') =>
        if !hasReceiver || msg.caps.isEmpty then
          -- No immediate rendezvous or no caps to transfer
          .ok ({ results := #[] }, st')
        else
          -- Immediate rendezvous occurred — find receiver's cspaceRoot
          -- The receiver was the head of the receiveQ before the send.
          -- After send, the receiver's TCB has been updated with the message.
          -- We need to find who was dequeued. Look at endpoint state pre-send.
          -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration.
          match st.getEndpoint? endpointId with
          | some ep =>
            match ep.receiveQ.head with
            | some receiverId =>
              match lookupCspaceRoot st receiverId with
              | some recvRoot =>
                ipcUnwrapCaps { msg with capsGranted := endpointRights.mem .grant } senderCspaceRoot recvRoot
                  receiverSlotBase (endpointRights.mem .grant) st'
              | none =>
                -- AK1-I (I-M07 / MEDIUM, NI L-1): Symmetric with the
                -- `endpointReceiveDualWithCaps` and `endpointCallWithCaps`
                -- arms below. Previous behavior returned
                -- `.ok ({ results := #[] }, st')` — a silent success on
                -- missing receiver CSpace root. This asymmetry was an NI
                -- distinguisher: send and receive (and later call)
                -- observed different kernel-result shapes for the same
                -- structural fault, giving a per-domain covert channel
                -- via `KernelError`. All three IPC capability-transfer
                -- paths now fail closed with `.invalidCapability`,
                -- preserving NI symmetry. The message payload itself was
                -- already delivered by `endpointSendDual` at line above;
                -- the `.error` indicates the capability-transfer side
                -- channel failed and allows the caller to surface a clean
                -- protocol-level error.
                .error .invalidCapability
            | none => .ok ({ results := #[] }, st')
          | none => .ok ({ results := #[] }, st')

/-- M-D01: Extended receive with capability transfer. When a sender is
dequeued (immediate rendezvous on the receive side), unwrap `msg.caps`
from the sender's pending message into the receiver's CSpace.

When no sender is waiting (receiver enqueues), no cap transfer occurs —
the receiver will get caps when a sender later arrives via
`endpointSendDualWithCaps`. -/
def endpointReceiveDualWithCaps
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId)
    (receiverCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) : Kernel (SeLe4n.ThreadId × CapTransferSummary) :=
  fun st =>
    -- WS-SM SM6.D (#7.1 fold): forward the server-supplied reply object into the
    -- folded receive transition (atomic reply-linking on a Call rendezvous).
    -- PR #873 round 8: **did this receive dequeue anything?**  Read before the
    -- transition, exactly as `endpointSendDualWithCaps` reads `hasReceiver`
    -- before the send.  Without it the blocking branch — which returns the
    -- receiver's own id and leaves `pendingMessage` untouched — unwrapped a
    -- *previously delivered* message a second time, installing an extra copy of
    -- authority for a receive that consumed nothing.
    let rendezvous := (receiveRendezvousSender? st endpointId).isSome
    match endpointReceiveDual endpointId receiver replyId st with
    | .error e => .error e
    | .ok (senderId, st') =>
        if !rendezvous then .ok ((senderId, { results := #[] }), st') else
        -- Check if the receiver got a message (sender was dequeued)
        -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration.
        match st'.getTcb? receiver with
        | some receiverTcb =>
            match receiverTcb.pendingMessage with
            | some msg =>
                if msg.caps.isEmpty then
                  .ok ((senderId, { results := #[] }), st')
                else
                  -- Sender was dequeued — get sender's cspaceRoot for CDT tracking.
                  -- AK1-I (I-M07 / MEDIUM, NI L-1) + U-H13: Symmetric with
                  -- the `endpointSendDualWithCaps` arm above and the
                  -- `endpointCallWithCaps` arm below. Previous behavior
                  -- fell back silently to `senderId.toObjId` on missing
                  -- sender CSpace root — a silent success that could mask
                  -- bugs and gave a per-domain covert channel via
                  -- `KernelError`. Now all three IPC capability-transfer
                  -- paths fail closed with `.invalidCapability` on this
                  -- structural fault, preserving NI symmetry. The
                  -- message payload itself was already delivered by
                  -- `endpointReceiveDual` at line above; the `.error`
                  -- indicates the capability-transfer side channel
                  -- failed and allows the caller to surface a clean
                  -- protocol-level error.
                  match lookupCspaceRoot st' senderId with
                  | none => .error .invalidCapability
                  | some senderRoot =>
                    -- PR #873 round 6: the grant right is the **sender's**, read
                    -- off the message it sent.  It used to be the receiver's
                    -- endpoint rights, which is a different principal's
                    -- authority: seL4 gates capability transfer on the sender's
                    -- endpoint capability, and consulting the receiver's here
                    -- made the queued ordering disagree with the rendezvous one
                    -- whenever a granting sender met a non-granting receiver.
                    match ipcUnwrapCaps msg senderRoot receiverCspaceRoot
                        receiverSlotBase msg.capsGranted st' with
                    | .error e => .error e
                    | .ok (summary, st'') => .ok ((senderId, summary), st'')
            | none =>
                -- Receiver was enqueued (no sender available)
                .ok ((senderId, { results := #[] }), st')
        | none => .ok ((senderId, { results := #[] }), st')

/-- **M-D01 (PR #873 round 8): a receive that dequeued nothing installs
nothing** — the single-core sibling of
`endpointReceiveDualWithCapsOnCore_blocked_installs_nothing`, and the same
security property.

`endpointReceiveDual`'s blocking branch returns the receiver's own id and leaves
`pendingMessage` untouched, so deciding by that field alone re-unwrapped a
message the receiver had been holding since a previous receive — an extra copy of
authority installed with no sender.  The gate is the endpoint's pre-state send
queue, which is what the bare transition itself branches on. -/
theorem endpointReceiveDualWithCaps_blocked_installs_nothing
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) (receiverCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (st st' : SystemState) (senderId : SeLe4n.ThreadId)
    (hBlocked : receiveRendezvousSender? st endpointId = none)
    (hRecv : endpointReceiveDual endpointId receiver replyId st = .ok (senderId, st')) :
    endpointReceiveDualWithCaps endpointId receiver replyId receiverCspaceRoot
        receiverSlotBase st
      = .ok ((senderId, { results := #[] }), st') := by
  simp [endpointReceiveDualWithCaps, hRecv, hBlocked]

/-- M-D01: Extended call with capability transfer. Composes `endpointCall`
with `ipcUnwrapCaps` for the immediate-rendezvous path. Same structure as
`endpointSendDualWithCaps` but using `endpointCall` as the base operation. -/
def endpointCallWithCaps
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (callerCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) : Kernel CapTransferSummary :=
  fun st =>
    -- PR #873 round 13: **the endpoint's grant right is stamped into the
    -- message**, because the message is where both orderings read it.  The
    -- immediate rendezvous below consulted `endpointRights` while a queued send
    -- left `msg.capsGranted` untouched for the later unwrap to read, so a caller
    -- that passed granting rights with the field's `false` default transferred
    -- capabilities on rendezvous and none after parking -- capability delivery
    -- decided by which side reached the endpoint first, the order-dependence
    -- round 6 removed from the receive side.  One authority, recorded once, read
    -- once.
    -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration.
    let hasReceiver := match st.getEndpoint? endpointId with
      | some ep => ep.receiveQ.head.isSome
      | none    => false
    match endpointCall endpointId caller { msg with capsGranted := endpointRights.mem .grant } st with
    | .error e => .error e
    | .ok ((), st') =>
        if !hasReceiver || msg.caps.isEmpty then
          .ok ({ results := #[] }, st')
        else
          -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration.
          match st.getEndpoint? endpointId with
          | some ep =>
            match ep.receiveQ.head with
            | some receiverId =>
              match lookupCspaceRoot st receiverId with
              | some recvRoot =>
                ipcUnwrapCaps { msg with capsGranted := endpointRights.mem .grant } callerCspaceRoot recvRoot
                  receiverSlotBase (endpointRights.mem .grant) st'
              | none =>
                -- WS-RC R1 (DEEP-IPC-03 / MEDIUM, NI L-1): Symmetric with
                -- the `endpointSendDualWithCaps` and
                -- `endpointReceiveDualWithCaps` arms above. Previous
                -- behavior returned `.ok ({ results := #[] }, st')` — a
                -- silent success on missing receiver CSpace root. This
                -- asymmetry was an NI distinguisher: the call path
                -- observed a different kernel-result shape from the
                -- send/receive paths for the same structural fault,
                -- giving a per-domain covert channel via `KernelError`.
                -- All three IPC capability-transfer paths now fail
                -- closed with `.invalidCapability` on this branch,
                -- preserving NI symmetry. The message payload itself
                -- was already delivered by `endpointCall` at line
                -- above; the `.error` indicates the capability-transfer
                -- side channel failed and allows the caller to surface
                -- a clean protocol-level error.
                .error .invalidCapability
            | none => .ok ({ results := #[] }, st')
          | none => .ok ({ results := #[] }, st')

/-- **WS-RR RR7.8**: when the pre-state names a destination, the send arm's whole
effect is the base transition followed by `ipcUnwrapCaps` **at that root**.

The anti-drift device.  `rendezvousCapsDestination?` exists so a declared lock
footprint can name the object the transfer writes; this is what makes the two
one fact rather than two that agree today.  A refactor that changes which root
the arm installs into — or which state it reads it from — fails here. -/
theorem endpointSendDualWithCaps_reduces_to_unwrap
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (senderCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (recvRoot : SeLe4n.ObjId)
    (hSend : endpointSendDual endpointId sender
        { msg with capsGranted := endpointRights.mem .grant } st = .ok ((), st'))
    (hDest : rendezvousCapsDestination? st endpointId msg = some recvRoot) :
    endpointSendDualWithCaps endpointId sender msg endpointRights senderCspaceRoot
        receiverSlotBase st
      = ipcUnwrapCaps { msg with capsGranted := endpointRights.mem .grant }
          senderCspaceRoot recvRoot receiverSlotBase (endpointRights.mem .grant) st' := by
  unfold endpointSendDualWithCaps
  unfold rendezvousCapsDestination? at hDest
  by_cases hEmpty : msg.caps.isEmpty = true
  · simp [hEmpty] at hDest
  · simp only [hEmpty] at hDest
    cases hEp : st.getEndpoint? endpointId with
    | none => simp [hEp] at hDest
    | some ep =>
      cases hHead : ep.receiveQ.head with
      | none => simp [hEp, hHead] at hDest
      | some receiverId =>
        simp only [hEp, hHead, Option.bind_some] at hDest
        simp only [hSend, hHead, Option.isSome_some, hEmpty,
          Bool.not_true, Bool.false_or]
        simp only [Bool.false_eq_true, if_false] at hDest ⊢
        rw [hDest]

/-- **WS-RR RR7.8**: the call arm's reduction, identically shaped — the same
condition, the same resolver, the same root. -/
theorem endpointCallWithCaps_reduces_to_unwrap
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (callerCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (recvRoot : SeLe4n.ObjId)
    (hCall : endpointCall endpointId caller
        { msg with capsGranted := endpointRights.mem .grant } st = .ok ((), st'))
    (hDest : rendezvousCapsDestination? st endpointId msg = some recvRoot) :
    endpointCallWithCaps endpointId caller msg endpointRights callerCspaceRoot
        receiverSlotBase st
      = ipcUnwrapCaps { msg with capsGranted := endpointRights.mem .grant }
          callerCspaceRoot recvRoot receiverSlotBase (endpointRights.mem .grant) st' := by
  unfold endpointCallWithCaps
  unfold rendezvousCapsDestination? at hDest
  by_cases hEmpty : msg.caps.isEmpty = true
  · simp [hEmpty] at hDest
  · simp only [hEmpty] at hDest
    cases hEp : st.getEndpoint? endpointId with
    | none => simp [hEp] at hDest
    | some ep =>
      cases hHead : ep.receiveQ.head with
      | none => simp [hEp, hHead] at hDest
      | some receiverId =>
        simp only [hEp, hHead, Option.bind_some] at hDest
        simp only [hCall, hHead, Option.isSome_some, hEmpty,
          Bool.not_true, Bool.false_or]
        simp only [Bool.false_eq_true, if_false] at hDest ⊢
        rw [hDest]

end SeLe4n.Kernel
