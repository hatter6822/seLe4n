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

**U5-K/U-M30: CSpace root slot 0 simplification**: The `receiverSlotBase`
parameter is hardcoded to `Slot.ofNat 0` at the API dispatch layer (API.lean).
This is a model simplification — real seL4 uses the actual slot address from
the message info register to determine where received capabilities are placed
in the receiver's CNode. In seLe4n, all cap transfers target slot 0 of the
receiver's CSpace root. This simplification is safe for correctness but
imprecise: real seL4 allows receivers to specify where caps are placed.
See: seL4 Reference Manual §4.2 "Message Info".

**U5-M/U-L06: Cap transfer CDT tracking**: Transferred capabilities are
tracked in the CDT (Capability Derivation Tree) using fixed slot 0 of the
receiver's CSpace root. This means all transferred capabilities share the
same CDT parent slot, which is imprecise but safe: CDT-based revocation of
the parent slot over-revokes (revokes ALL caps received via this endpoint)
rather than under-revokes. This is a conservative simplification that
preserves the security guarantee: no capability can escape revocation.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- M-D01: Helper to read a thread's CSpace root ObjId from its TCB. -/
def lookupCspaceRoot (st : SystemState) (tid : SeLe4n.ThreadId)
    : Option SeLe4n.ObjId :=
  match st.objects[tid.toObjId]? with
  | some (.tcb tcb) => some tcb.cspaceRoot
  | _ => none

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
    -- Check if a receiver is waiting BEFORE the send
    let hasReceiver := match st.objects[endpointId]? with
      | some (.endpoint ep) => ep.receiveQ.head.isSome
      | _ => false
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
          match st.objects[endpointId]? with
          | some (.endpoint ep) =>
            match ep.receiveQ.head with
            | some receiverId =>
              match lookupCspaceRoot st' receiverId with
              | some recvRoot =>
                let grantRight := endpointRights.mem .grant
                ipcUnwrapCaps msg senderCspaceRoot recvRoot receiverSlotBase grantRight st'
              | none => .ok ({ results := #[] }, st')
            | none => .ok ({ results := #[] }, st')
          | _ => .ok ({ results := #[] }, st')

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
        match st'.objects[receiver.toObjId]? with
        | some (.tcb receiverTcb) =>
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
        | _ => .ok ((senderId, { results := #[] }), st')

/-- M-D01: Extended call with capability transfer. Composes `endpointCall`
with `ipcUnwrapCaps` for the immediate-rendezvous path. Same structure as
`endpointSendDualWithCaps` but using `endpointCall` as the base operation. -/
def endpointCallWithCaps
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (callerCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) : Kernel CapTransferSummary :=
  fun st =>
    let hasReceiver := match st.objects[endpointId]? with
      | some (.endpoint ep) => ep.receiveQ.head.isSome
      | _ => false
    match endpointCall endpointId caller msg st with
    | .error e => .error e
    | .ok ((), st') =>
        if !hasReceiver || msg.caps.isEmpty then
          .ok ({ results := #[] }, st')
        else
          match st.objects[endpointId]? with
          | some (.endpoint ep) =>
            match ep.receiveQ.head with
            | some receiverId =>
              match lookupCspaceRoot st' receiverId with
              | some recvRoot =>
                let grantRight := endpointRights.mem .grant
                ipcUnwrapCaps msg callerCspaceRoot recvRoot receiverSlotBase grantRight st'
              | none => .ok ({ results := #[] }, st')
            | none => .ok ({ results := #[] }, st')
          | _ => .ok ({ results := #[] }, st')

end SeLe4n.Kernel
