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
    -- Check if a receiver is waiting BEFORE the send.
    -- AJ1-C (M-02): `endpointQueuePopHead_returns_head` proves the pre-inspected
    -- receiver matches the thread actually dequeued, ensuring capability transfer
    -- targets the correct thread.
    -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration.
    let hasReceiver := match st.getEndpoint? endpointId with
      | some ep => ep.receiveQ.head.isSome
      | none    => false
    match endpointSendDual endpointId sender msg st with
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
              match lookupCspaceRoot st' receiverId with
              | some recvRoot =>
                let grantRight := endpointRights.mem .grant
                ipcUnwrapCaps msg senderCspaceRoot recvRoot receiverSlotBase grantRight st'
              | none =>
                -- AK1-I (I-M07 / MEDIUM, NI L-1): Symmetric with the receive
                -- path below. Previous behavior returned `.ok ({ results := #[] }, st')`
                -- — a silent success on missing receiver CSpace root. This
                -- asymmetry was an NI distinguisher: send and receive
                -- observed different kernel-result shapes for the same
                -- structural fault, giving a per-domain covert channel.
                -- Now both paths fail closed with `.invalidCapability`,
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
    (endpointRights : AccessRightSet)
    (receiverCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) : Kernel (SeLe4n.ThreadId × CapTransferSummary) :=
  fun st =>
    match endpointReceiveDual endpointId receiver st with
    | .error e => .error e
    | .ok (senderId, st') =>
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
                  -- U-H13: Missing CSpace root returns explicit error instead of
                  -- silently falling back to senderId.toObjId, which could mask bugs.
                  match lookupCspaceRoot st' senderId with
                  | none => .error .invalidCapability
                  | some senderRoot =>
                    let grantRight := endpointRights.mem .grant
                    match ipcUnwrapCaps msg senderRoot receiverCspaceRoot
                        receiverSlotBase grantRight st' with
                    | .error e => .error e
                    | .ok (summary, st'') => .ok ((senderId, summary), st'')
            | none =>
                -- Receiver was enqueued (no sender available)
                .ok ((senderId, { results := #[] }), st')
        | none => .ok ((senderId, { results := #[] }), st')

/-- M-D01: Extended call with capability transfer. Composes `endpointCall`
with `ipcUnwrapCaps` for the immediate-rendezvous path. Same structure as
`endpointSendDualWithCaps` but using `endpointCall` as the base operation. -/
def endpointCallWithCaps
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (callerCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) : Kernel CapTransferSummary :=
  fun st =>
    -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration.
    let hasReceiver := match st.getEndpoint? endpointId with
      | some ep => ep.receiveQ.head.isSome
      | none    => false
    match endpointCall endpointId caller msg st with
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
              match lookupCspaceRoot st' receiverId with
              | some recvRoot =>
                let grantRight := endpointRights.mem .grant
                ipcUnwrapCaps msg callerCspaceRoot recvRoot receiverSlotBase grantRight st'
              | none => .ok ({ results := #[] }, st')
            | none => .ok ({ results := #[] }, st')
          | none => .ok ({ results := #[] }, st')

end SeLe4n.Kernel
