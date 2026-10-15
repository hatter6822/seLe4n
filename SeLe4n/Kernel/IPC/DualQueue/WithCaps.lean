-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
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
was waiting on the endpoint). When the sender is enqueued (no receiver), it
keeps its capability addresses in its own frame, and the receive that later
dequeues it resolves and installs them (`receiveTransferCaps`).

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
both arms read the receiver's root from `st` as well. (They read it from the
*post*-state before; the two agree, because nothing between them writes
`TCB.cspaceRoot` — thread creation is its only writer — but "the states agree"
is a fact about the tree that a later transition could falsify silently, while
"both read the same state" is a fact about the code.)

`none` covers the three shapes that install nothing: a send asking to transfer
no capabilities (`sendCapRequest`), an endpoint with no waiting receiver, and a
receiver whose TCB does not resolve. The last is the fail-closed arm the transitions take as
`.error .invalidCapability`; it declares no destination because it writes
none. -/
def rendezvousCapsDestination? (st : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (payload : SendPayload) : Option SeLe4n.ObjId :=
  if (sendCapRequest st endpointId sender payload).isNone then none
  else ((st.getEndpoint? endpointId).bind (·.receiveQ.head)).bind (lookupCspaceRoot st)

/-- WS-ZA ZA4.7: a frame sent without the grant right asks to transfer nothing,
so it names no capability destination. -/
theorem rendezvousCapsDestination?_ungranted (st : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (badge : Option SeLe4n.Badge) :
    rendezvousCapsDestination? st endpointId sender (.frame badge false) = none := by
  unfold rendezvousCapsDestination? sendCapRequest
  split
  · rfl
  · split <;> rfl

/-- WS-ZA ZA4.7: **resolve and install a receive's capability request** -- the
capabilities a dequeued sender asked to transfer (`receiveCapRequest`), looked
up in its CSpace now, as seL4 does at the rendezvous (a capability revoked while
the sender waited is never transferred), then unwrapped into the receiver's
CSpace.  The grant right was checked when the request was formed, so the unwrap
runs granted.  No request, or nothing that resolves, installs nothing. -/
def receiveTransferCaps (req : Option (SeLe4n.ObjId × Array SeLe4n.CPtr × Nat))
    (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot) :
    Kernel CapTransferSummary :=
  fun st =>
    match req with
    | none => .ok ({ results := #[] }, st)
    | some (root, addrs, depth) =>
        let (caps, st') := resolveExtraCaps root addrs depth true st
        if caps.isEmpty then .ok ({ results := #[] }, st')
        else
          ipcUnwrapCaps { IpcMessage.empty with caps := caps, capsGranted := true }
            receiverCspaceRoot receiverSlotBase true st'

/-- M-D01: Extended send with capability transfer.

Semantics:
- Sends via `endpointSendDual`.
- If a receiver was waiting (immediate rendezvous): resolves the capabilities
  the sender's frame asks to transfer (`sendCapRequest`, under its capability's
  grant right) in its CSpace now, and installs them in the receiver's CSpace
  (`receiveTransferCaps`, the receive side's own transfer).
- If no receiver was waiting (sender enqueued): nothing is resolved or
  installed; the receive that later dequeues the sender resolves its
  capability addresses then.

So capabilities are looked up only on the arm that delivers them, at the
rendezvous, on either arrival order (WS-ZA ZA4.7; seL4 `doIPCTransfer`).
Returns the cap transfer summary (empty when nothing is transferred). -/
def endpointSendDualWithCaps
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (payload : SendPayload) (receiverSlotBase : SeLe4n.Slot) : Kernel CapTransferSummary :=
  fun st =>
    let req := sendCapRequest st endpointId sender payload
    let dest? := ((st.getEndpoint? endpointId).bind (·.receiveQ.head)).bind (lookupCspaceRoot st)
    match endpointSendDual endpointId sender payload st with
    | .error e => .error e
    | .ok ((), st') =>
        match req with
        | none => .ok ({ results := #[] }, st')
        | some _ =>
            match dest? with
            | some recvRoot => receiveTransferCaps req recvRoot receiverSlotBase st'
            | none => .error .invalidCapability

/-- M-D01: Extended receive with capability transfer. When a sender is
dequeued (immediate rendezvous on the receive side), the capabilities it asked
to transfer are resolved in its CSpace and installed in the receiver's
(`receiveTransferCaps`).

When no sender is waiting (receiver enqueues), no cap transfer occurs —
the receiver will get caps when a sender later arrives via
`endpointSendDualWithCaps`. -/
def endpointReceiveDualWithCaps
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId)
    (receiverCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) : Kernel (SeLe4n.ThreadId × CapTransferSummary) :=
  fun st =>
    -- PR #873 round 8: **did this receive dequeue anything?** Read before the
    -- transition, exactly as `endpointSendDualWithCaps` reads `hasReceiver`
    -- before the send: the blocking branch returns the receiver's own id, so
    -- only a rendezvous may install anything.
    let rendezvous := (receiveRendezvousSender? st endpointId).isSome
    -- WS-ZA ZA4.7: and what the dequeued sender asks to transfer, read from the
    -- same pre-state (its registers and grant right).
    let req := receiveCapRequest st endpointId
    match endpointReceiveDual endpointId receiver replyId st with
    | .error e => .error e
    | .ok (senderId, st') =>
        if !rendezvous then .ok ((senderId, { results := #[] }), st') else
        match receiveTransferCaps req receiverCspaceRoot receiverSlotBase st' with
        | .error e => .error e
        | .ok (summary, st'') => .ok ((senderId, summary), st'')

/-- **M-D01 (PR #873 round 8): a receive that dequeued nothing installs
nothing** — the single-core sibling of
`endpointReceiveDualWithCapsOnCore_blocked_installs_nothing`, and the same
security property.

`endpointReceiveDual`'s blocking branch returns the receiver's own id and leaves
`pendingMessage` untouched, so deciding by that field alone re-unwrapped a
message the receiver had been holding since a previous receive — an extra copy of
authority installed with no sender. The gate is the endpoint's pre-state send
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

/-- M-D01: Extended call with capability transfer. Same structure as
`endpointSendDualWithCaps` but using `endpointCall` as the base operation. -/
def endpointCallWithCaps
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (payload : SendPayload) (receiverSlotBase : SeLe4n.Slot) : Kernel CapTransferSummary :=
  fun st =>
    let req := sendCapRequest st endpointId caller payload
    let dest? := ((st.getEndpoint? endpointId).bind (·.receiveQ.head)).bind (lookupCspaceRoot st)
    match endpointCall endpointId caller payload st with
    | .error e => .error e
    | .ok ((), st') =>
        match req with
        | none => .ok ({ results := #[] }, st')
        | some _ =>
            match dest? with
            | some recvRoot => receiveTransferCaps req recvRoot receiverSlotBase st'
            | none => .error .invalidCapability

/-- **WS-RR RR7.8**: when the pre-state names a destination, the send arm's whole
effect is the base transition followed by `ipcUnwrapCaps` **at that root**.

The anti-drift device. `rendezvousCapsDestination?` exists so a declared lock
footprint can name the object the transfer writes; this is what makes the two
one fact rather than two that agree today. A refactor that changes which root
the arm installs into — or which state it reads it from — fails here. -/
theorem endpointSendDualWithCaps_reduces_to_unwrap
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (payload : SendPayload) (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (recvRoot : SeLe4n.ObjId)
    (hSend : endpointSendDual endpointId sender payload st = .ok ((), st'))
    (hDest : rendezvousCapsDestination? st endpointId sender payload = some recvRoot) :
    endpointSendDualWithCaps endpointId sender payload receiverSlotBase st
      = receiveTransferCaps (sendCapRequest st endpointId sender payload)
          recvRoot receiverSlotBase st' := by
  unfold rendezvousCapsDestination? at hDest
  unfold endpointSendDualWithCaps
  simp only [hSend]
  cases hReq : sendCapRequest st endpointId sender payload with
  | none => simp [hReq] at hDest
  | some r => simp only [hReq, Option.isNone_some, Bool.false_eq_true, ↓reduceIte] at hDest ⊢; rw [hDest]

/-- **WS-RR RR7.8**: the call arm's reduction, identically shaped — the same
condition, the same resolver, the same root. -/
theorem endpointCallWithCaps_reduces_to_unwrap
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (payload : SendPayload) (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (recvRoot : SeLe4n.ObjId)
    (hCall : endpointCall endpointId caller payload st = .ok ((), st'))
    (hDest : rendezvousCapsDestination? st endpointId caller payload = some recvRoot) :
    endpointCallWithCaps endpointId caller payload receiverSlotBase st
      = receiveTransferCaps (sendCapRequest st endpointId caller payload)
          recvRoot receiverSlotBase st' := by
  unfold rendezvousCapsDestination? at hDest
  unfold endpointCallWithCaps
  simp only [hCall]
  cases hReq : sendCapRequest st endpointId caller payload with
  | none => simp [hReq] at hDest
  | some r => simp only [hReq, Option.isNone_some, Bool.false_eq_true, ↓reduceIte] at hDest ⊢; rw [hDest]


/-- WS-ZA ZA4.7: **a WithCaps send is its send and then one transfer**: a
successful `endpointSendDualWithCaps` is the base send followed by
`receiveTransferCaps` of the sender's request at some destination (a request of
`none` installs nothing).  Every WithCaps send preservation proof goes through
this and `receiveTransferCaps_frame`, the receive's shape. -/
theorem endpointSendDualWithCaps_transfer_of
    {endpointId : SeLe4n.ObjId} {sender : SeLe4n.ThreadId} {payload : SendPayload}
    {receiverSlotBase : SeLe4n.Slot} {st stMid st' : SystemState}
    {summary : CapTransferSummary}
    (hSend : endpointSendDual endpointId sender payload st = .ok ((), stMid))
    (hStep : endpointSendDualWithCaps endpointId sender payload receiverSlotBase st =
      .ok (summary, st')) :
    ∃ recvRoot, receiveTransferCaps (sendCapRequest st endpointId sender payload) recvRoot
      receiverSlotBase stMid = .ok (summary, st') := by
  unfold endpointSendDualWithCaps at hStep
  simp only [hSend] at hStep
  cases hReq : sendCapRequest st endpointId sender payload with
  | none =>
    simp only [hReq] at hStep
    exact ⟨endpointId, hStep⟩
  | some r =>
    simp only [hReq] at hStep
    split at hStep
    · exact ⟨_, hStep⟩
    · cases hStep

/-- WS-ZA ZA4.7: the call's twin of `endpointSendDualWithCaps_transfer_of`. -/
theorem endpointCallWithCaps_transfer_of
    {endpointId : SeLe4n.ObjId} {caller : SeLe4n.ThreadId} {payload : SendPayload}
    {receiverSlotBase : SeLe4n.Slot} {st stMid st' : SystemState}
    {summary : CapTransferSummary}
    (hCall : endpointCall endpointId caller payload st = .ok ((), stMid))
    (hStep : endpointCallWithCaps endpointId caller payload receiverSlotBase st =
      .ok (summary, st')) :
    ∃ recvRoot, receiveTransferCaps (sendCapRequest st endpointId caller payload) recvRoot
      receiverSlotBase stMid = .ok (summary, st') := by
  unfold endpointCallWithCaps at hStep
  simp only [hCall] at hStep
  cases hReq : sendCapRequest st endpointId caller payload with
  | none =>
    simp only [hReq] at hStep
    exact ⟨endpointId, hStep⟩
  | some r =>
    simp only [hReq] at hStep
    split at hStep
    · exact ⟨_, hStep⟩
    · cases hStep

end SeLe4n.Kernel
