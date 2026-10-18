-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.DualQueue.Core
import SeLe4n.Kernel.Architecture.RegisterDecode
import SeLe4n.Kernel.Architecture.SyscallArgDecode
import SeLe4n.Kernel.Architecture.Fault

/-!
# The message a blocked sender holds

WS-ZA ZA4.7.  A sender that blocks keeps its message where seL4 keeps it: the
words in its saved registers and IPC buffer, what its capability contributed
(badge, grant right) in its TCB (`TCB.setSendCap`), and its extra capabilities
as addresses in its own CSpace.  The receive that takes the message reads it
there (`blockedSenderMessage`): the words through the entry's own decoder
(`decodeSyscallArgsFromState`), and the capabilities resolved in the sender's
CSpace at that moment (`resolveExtraCaps`), so a capability revoked while the
sender waits is never transferred.  A fault is the one message the kernel
writes: a thread blocked delivering one carries it as its `pendingFault`
(`TCB.ipcFaultSend`), and the receive builds the message from it
(`faultMessage`), as seL4 does from `tcbFault`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- WS-RR RR4.4: the `IpcMessage` a fault is delivered as.

The encoder (`Architecture.encodeFault`) owns the layout; this is the
model-side envelope: the encoded register array, the encoded `seL4_Fault_tag`
as the message label, the handler capability's badge (seL4 passes
`cap_endpoint_cap_get_capEPBadge(handlerCap)` to `sendIPC`, so a handler
serving several faulting threads through badged capabilities can tell them
apart), and **no capabilities**.

`capsGranted := false` is not merely the default: a fault message must never
transfer authority.  It is a diagnostic report the kernel writes about a
thread, so granting through it would let the *kernel* hand a handler
capabilities the faulting thread never offered — and it is what makes the
RR4.20 non-interference argument about a data flow alone. -/
def faultMessage (f : Fault) (ctx : FaultContext) (badge : Option SeLe4n.Badge) :
    IpcMessage :=
  { registers   := (Architecture.encodeFault f ctx).2
    caps        := #[]
    badge       := badge
    capsGranted := false
    label       := (Architecture.encodeFault f ctx).1.label }

/-- WS-RR RR4.6: the message satisfies the model's payload bound predicate. -/
theorem faultMessage_bounded (f : Fault) (ctx : FaultContext)
    (badge : Option SeLe4n.Badge) : (faultMessage f ctx badge).bounded := by
  refine ⟨Architecture.encodeFault_within_budget f ctx, ?_⟩
  simp [faultMessage, maxExtraCaps]

/-- M-D01: Resolve extra capability addresses from the sender's CSpace
into actual capabilities for IPC message transfer.

For each CPtr in `capAddrs`, resolve it via `resolveCapAddress` in the
sender's CSpace root, then look up the capability at the resolved slot.
Caps that fail to resolve are silently dropped (seL4 behavior).
Returns the resolved capabilities as an array. -/
/- W5-G: Resolves extra capabilities from IPC buffer. Failed resolutions are
   silently dropped (matching seL4 `lookupExtraCaps` behavior). This means
   the receiver gets fewer extra caps than the sender specified. For
   debugging, callers should check `extraCaps.length` against the expected
   count from `MessageInfo.extraCaps`.
   X5-I (L-4): Confirmed v0.22.17 audit — silent dropping matches seL4
   reference semantics. No security impact: caps that fail resolution
   simply don't transfer.

   **AC3-D / API-01 — Silent-drop semantics**: The returned `Array Capability`
   contains only successfully resolved capabilities. Its `.size` equals the
   count of *successfully resolved* extra caps, which may be strictly less than
   `capAddrs.size` (the sender's requested count). Receivers should compare
   the actual resolved count against the expected count from the original
   `MessageInfo.extraCaps` to detect drops. This is seL4-compatible behavior:
   `lookupExtraCaps` in the C kernel also silently discards unresolvable
   capabilities and returns only valid ones in the IPC buffer.

   **AI6-A (M-02) — Spec cross-reference**: See `docs/spec/SELE4N_SPEC.md`
   §8.10.4 "IPC Extra Capability Resolution — Silent-Drop Semantics" for the
   normative specification, including the seL4 reference C kernel equivalence. -/
def resolveExtraCaps (cspaceRoot : SeLe4n.ObjId)
    (capAddrs : Array SeLe4n.CPtr) (depth : Nat) (granted : Bool)
    (st : SystemState) : Array TransferCap :=
  -- PR #873 round 14: **the authority is checked once, where it decides
  -- something** -- a sender without the Grant right transfers nothing, so its
  -- addresses are not looked up at all.
  --
  -- WS-ZA ZA5.3: resolution is a pure read (seL4 `lookupExtraCaps`).  Each
  -- capability carries the address of the slot it was read from: the slot is
  -- its own derivation node, so the transfer that installs it records the edge
  -- from that slot, and nothing is minted here.  A send resolves its addresses
  -- at the rendezvous only, so no source address is ever held across a
  -- syscall.
  if !granted then #[] else
  capAddrs.foldl (fun acc addr =>
    match resolveCapAddress cspaceRoot addr depth st with
    | .error _ => acc
    | .ok ref =>
        match SystemState.lookupSlotCap st ref with
        | none => acc
        | some cap => acc.push (TransferCap.fromSlot cap ref)) #[]


/-- WS-ZA ZA4.7: the decode of a blocked sender's saved frame — the entry's own
decoder (`decodeSyscallArgsFromState`) on the registers the entry saved
(`registerContext`), with the overflow words read from its IPC buffer. -/
def blockedSenderDecode (st : SystemState) (sender : SeLe4n.ThreadId) (tcb : TCB) :
    Except KernelError SyscallDecodeResult :=
  Architecture.RegisterDecode.decodeSyscallArgsFromState st sender
    SeLe4n.arm64DefaultLayout tcb.registerContext 32

/-- WS-ZA ZA4.7: **the message a sender's frame holds**, given the decode of
its saved registers and what its capability contributes: the body cut to the
declared length (`extractMessageRegisters`), the capability's badge and grant
right, and no capabilities (the transfer resolves those separately).  A frame
that does not decode delivers no words.  The send that meets a waiting receiver
and the receive that takes a blocked sender both read the message here, so the
two arrival orders deliver the same words. -/
@[inline] def senderFrameMessage (decode : Except KernelError SyscallDecodeResult)
    (badge : Option SeLe4n.Badge) (grant : Bool) : IpcMessage :=
  match decode with
  | .error _ => { IpcMessage.empty with badge := badge, capsGranted := grant }
  | .ok decoded =>
      { registers := Architecture.RegisterDecode.extractMessageRegisters decoded.msgRegs
          decoded.msgInfo,
        caps := #[], badge := badge, capsGranted := grant }

/-- WS-ZA ZA4.7: **the message a blocked sender holds**, given the decode of
its saved frame.

* A thread blocked delivering a fault carries the fault (`pendingFault`), and
  its message is `faultMessage` of it under the handler capability's badge.
* Any other sender's message is its saved frame decoded as the entry decodes
  it: the body cut to the declared length (`extractMessageRegisters`), the
  badge its capability carried and its grant right.  A frame that no longer
  decodes (its registers were rewritten while it waited) delivers no words.

The extra capabilities are not part of this read: the receive that takes the
message resolves them (`blockedSenderCapRequest`) and installs them in one
step, as the send that meets a waiting receiver does, so no capability is in
flight between syscalls.  The decode is an argument so the live store
(`blockedSenderMessage`) and the frozen one read the message through this one
definition. -/
@[inline] def blockedSenderMessageOf (tcb : TCB)
    (decode : Except KernelError SyscallDecodeResult) : IpcMessage :=
  if tcb.ipcFaultSend then
    match tcb.pendingFault with
    | some tf => faultMessage tf.fault tf.context tcb.ipcBadgeView
    | none => { IpcMessage.empty with badge := tcb.ipcBadgeView }
  else senderFrameMessage decode tcb.ipcBadgeView tcb.ipcCanGrant

/-- WS-ZA ZA4.7: **the message a blocked sender holds**, read at the
rendezvous from where seL4 keeps it (`blockedSenderMessageOf` of the live
decode of its saved frame). -/
def blockedSenderMessage (st : SystemState) (sender : SeLe4n.ThreadId) (tcb : TCB) :
    IpcMessage :=
  blockedSenderMessageOf tcb (blockedSenderDecode st sender tcb)

/-- WS-ZA ZA4.7: **the capabilities a sender's frame asks to transfer**, as the
CSpace root, the addresses and the root's depth they resolve against -- or
`none` when it transfers nothing: no grant right, a frame that does not decode,
no capability addresses, or a missing CSpace root.  The send that meets a
waiting receiver and the receive that takes a blocked sender both resolve this
request at the rendezvous (`receiveTransferCaps`), so no capability is looked up
on the arm that blocks. -/
def senderFrameCapRequest (st : SystemState) (sender : SeLe4n.ThreadId) (tcb : TCB)
    (grant : Bool) : Option (SeLe4n.ObjId × Array SeLe4n.CPtr × Nat) :=
  if !grant then none else
  match blockedSenderDecode st sender tcb with
  | .error _ => none
  | .ok decoded =>
      let addrs := Architecture.SyscallArgDecode.decodeExtraCapAddrs decoded
      if addrs.isEmpty then none else
      match st.getCNode? tcb.cspaceRoot with
      | some rootCn => some (tcb.cspaceRoot, addrs, rootCn.depth)
      | none => none

/-- WS-ZA ZA4.7: **the capabilities a blocked sender asks to transfer**, as the
CSpace root, the addresses and the root's depth they resolve against -- or
`none` when it transfers nothing: a fault message, a sender without the grant
right, a frame that no longer decodes, no capability addresses, or a missing
CSpace root.  `resolveExtraCaps` of the request is what the receive installs;
`receiveInstallsCaps` is this function's `isSome`, so the receive's lock
footprint and its install read one answer. -/
def blockedSenderCapRequest (st : SystemState) (sender : SeLe4n.ThreadId) (tcb : TCB) :
    Option (SeLe4n.ObjId × Array SeLe4n.CPtr × Nat) :=
  if tcb.ipcFaultSend then none else senderFrameCapRequest st sender tcb tcb.ipcCanGrant

/-- WS-ZA ZA4.7: a blocked sender's message carries no capabilities -- the
receive resolves them separately (`blockedSenderCapRequest`). -/
@[simp] theorem blockedSenderMessage_caps (st : SystemState) (sender : SeLe4n.ThreadId)
    (tcb : TCB) : (blockedSenderMessage st sender tcb).caps = #[] := by
  unfold blockedSenderMessage blockedSenderMessageOf senderFrameMessage
  split
  · split <;> rfl
  · split <;> rfl

/-- WS-ZA ZA4.7: and it is within the payload bound: a fault encodes inside the
budget, and a decoded body is cut to at most `maxMessageRegisters` words. -/
theorem blockedSenderMessage_bounded (st : SystemState) (sender : SeLe4n.ThreadId)
    (tcb : TCB) : (blockedSenderMessage st sender tcb).bounded := by
  refine ⟨?_, by simp [maxExtraCaps]⟩
  unfold blockedSenderMessage blockedSenderMessageOf senderFrameMessage
  split
  · split
    · exact Architecture.encodeFault_within_budget _ _
    · simp [IpcMessage.empty]
  · split
    · simp [IpcMessage.empty]
    · exact Architecture.RegisterDecode.extractMessageRegisters_length _ _


/-- WS-ZA ZA4.7: **what a send carries in from its capability** -- all a send
or call is handed, as seL4's `sendIPC` is handed only the badge and the grant
right.  The words are not part of it: they are in the sender's saved registers
and IPC buffer, and whichever arm delivers them reads them there
(`sendPayloadMessage`), so a send that meets a waiting receiver and one that
blocks until a receive takes it deliver the same words.

* `frame badge grant` -- an ordinary send: the message is the sender's frame
  (`senderFrameMessage`) under its capability's badge and grant right.
* `fault f ctx badge` -- the one message the kernel writes: a fault, delivered
  under the handler capability's badge (`faultMessage`). -/
inductive SendPayload where
  | frame (badge : Option SeLe4n.Badge) (grant : Bool)
  | fault (f : Fault) (ctx : FaultContext) (badge : Option SeLe4n.Badge)

/-- The badge a send's capability carries. -/
@[inline] def SendPayload.badge : SendPayload → Option SeLe4n.Badge
  | .frame b _ => b
  | .fault _ _ b => b

/-- Whether a send may transfer capabilities: an ordinary send whose capability
had the grant right; a fault never transfers authority. -/
@[inline] def SendPayload.grant : SendPayload → Bool
  | .frame _ g => g
  | .fault _ _ _ => false

/-- WS-ZA ZA4.7: the decode of a sender's saved frame, looked up by its id: a
thread that does not exist has no frame, and its decode is a refusal. -/
def senderFrameDecode (st : SystemState) (sender : SeLe4n.ThreadId) :
    Except KernelError SyscallDecodeResult :=
  match st.getTcb? sender with
  | some tcb => blockedSenderDecode st sender tcb
  | none => .error .objectNotFound

/-- WS-ZA ZA4.7: **the message a send delivers** to a waiting receiver: the
fault message for a fault, otherwise the sender's frame under its capability's
badge and grant right -- the same read the receive that takes a blocked sender
makes (`sendPayloadMessage_frame_eq_blockedSenderMessage`). -/
@[inline] def sendPayloadMessage (st : SystemState) (sender : SeLe4n.ThreadId) :
    SendPayload → IpcMessage
  | .frame b g => senderFrameMessage (senderFrameDecode st sender) b g
  | .fault f ctx b => faultMessage f ctx b

/-- WS-ZA ZA4.7: **the capabilities a send transfers** to a waiting receiver:
the frame's request (`senderFrameCapRequest`) under the capability's grant
right, none for a fault. -/
def sendPayloadCapRequest (st : SystemState) (sender : SeLe4n.ThreadId) (tcb : TCB) :
    SendPayload → Option (SeLe4n.ObjId × Array SeLe4n.CPtr × Nat)
  | .frame _ g => senderFrameCapRequest st sender tcb g
  | .fault _ _ _ => none

/-- WS-ZA ZA4.7: **both arrival orders deliver one message**: an ordinary send
that blocks records its capability's badge and grant right (`TCB.setSendCap`),
and the receive that takes it reads what the send to a waiting receiver
delivers. -/
theorem sendPayloadMessage_frame_eq_blockedSenderMessage (st : SystemState)
    (sender : SeLe4n.ThreadId) (tcb : TCB) (badge : Option SeLe4n.Badge) (grant : Bool)
    (hT : st.getTcb? sender = some tcb) :
    blockedSenderMessageOf (tcb.setSendCap badge grant) (blockedSenderDecode st sender tcb) =
      sendPayloadMessage st sender (.frame badge grant) := by
  simp [blockedSenderMessageOf, sendPayloadMessage, senderFrameDecode, hT]

/-- WS-ZA ZA4.7: a delivered message carries no capabilities. -/
@[simp] theorem sendPayloadMessage_caps (st : SystemState) (sender : SeLe4n.ThreadId)
    (p : SendPayload) : (sendPayloadMessage st sender p).caps = #[] := by
  cases p with
  | frame b g =>
    simp only [sendPayloadMessage, senderFrameMessage]
    split <;> rfl
  | fault f ctx b => rfl

/-- WS-ZA ZA4.7: and it is within the payload bound. -/
theorem sendPayloadMessage_bounded (st : SystemState) (sender : SeLe4n.ThreadId)
    (p : SendPayload) : (sendPayloadMessage st sender p).bounded := by
  cases p with
  | frame b g =>
    refine ⟨?_, by simp [maxExtraCaps]⟩
    simp only [sendPayloadMessage, senderFrameMessage]
    split
    · simp [IpcMessage.empty]
    · exact Architecture.RegisterDecode.extractMessageRegisters_length _ _
  | fault f ctx b => exact faultMessage_bounded f ctx b

end SeLe4n.Kernel
