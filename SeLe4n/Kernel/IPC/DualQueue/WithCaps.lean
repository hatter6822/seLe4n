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

Wrapper operations that compose the dual-queue IPC operations with the
capability transfer of a rendezvous (seL4's `transferCaps`).

The transfer only occurs when a rendezvous happens.  When the sender is
enqueued (no receiver), it keeps its capability addresses in its own frame, and
the receive that later dequeues it resolves and transfers them
(`receiveTransferCaps`).

**The receiver's side of the transfer is read from the pre-state**
(`receiverCapTarget?`): its TCB, whether it has an IPC buffer the kernel may
write, and the receive slot its buffer's receive path names (`receiveSlot?`,
seL4's `getReceiveSlots`).  The lock footprint names the receive slot's CNode
from the same state (`rendezvousCapsDestination?`), so the CNode the transfer
writes and the CNode the footprint names are one expression.

**CDT tracking**: the transferred capability records a derivation edge from the
slot it was read from to the receive slot; the slots are the tree's nodes, so
revocation is precise.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The receiver's side of a capability transfer**: its TCB and receive slot,
when it has an IPC buffer the kernel may write (seL4's `doNormalTransfer`
passes `transferCaps` the receiver's buffer, and a receiver with none receives
no capabilities); `none` for a receiver that receives none. -/
def receiverCapTarget? (st : SystemState) (receiver : SeLe4n.ThreadId) :
    Option (TCB × Option CSpaceAddr) :=
  match st.getTcb? receiver with
  | none => none
  | some rtcb => if receiverHasBuffer st rtcb then some (rtcb, receiveSlot? st rtcb) else none

/-- **The receive slot of a receiver, if it can take a capability.** -/
@[inline] def receiverCapSlot? (st : SystemState) (receiver : SeLe4n.ThreadId) :
    Option CSpaceAddr :=
  (receiverCapTarget? st receiver).bind (·.2)

/-- **WS-RR RR7.8: the CNode a caps-carrying rendezvous writes**, resolved from
the **pre**-state: the receive slot's CNode, read from the state the send's
transfer reads it from (`receiverCapTarget?` of the pre-state).

`none` covers the shapes that install nothing: a send asking to transfer no
capabilities (`sendCapRequest`), an endpoint with no waiting receiver, and a
receiver with no receive slot. -/
def rendezvousCapsDestination? (st : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (payload : SendPayload) : Option SeLe4n.ObjId :=
  if (sendCapRequest st endpointId sender payload).isNone then none
  else (((st.getEndpoint? endpointId).bind (·.receiveQ.head)).bind
    (receiverCapSlot? st)).map (·.cnode)

/-- WS-ZA ZA4.7: a frame sent without the grant right asks to transfer nothing,
so it names no capability destination. -/
theorem rendezvousCapsDestination?_ungranted (st : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (badge : Option SeLe4n.Badge) :
    rendezvousCapsDestination? st endpointId sender (.frame badge false) = none := by
  unfold rendezvousCapsDestination? sendCapRequest
  split
  · rfl
  · split <;> rfl

/-- WS-ZA ZA4.7: **resolve and transfer a rendezvous's capability request** —
the capabilities a sender asked to transfer, looked up in its CSpace now
(`resolveExtraCaps`, seL4's `lookupExtraCaps`: a capability revoked while the
sender waited is never transferred), then transferred to the receiver's side
`target?` (`ipcUnwrapCaps`, seL4's `transferCaps`) for a message sent on
`endpointId` (`none` for a reply, which seL4's `doReplyTransfer` sends on no
endpoint, so nothing unwraps).  The grant right was checked when the request was formed.  No
request, nothing that resolves, or a receiver that can take no capability,
transfers nothing. -/
def receiveTransferCaps (req : Option (SeLe4n.ObjId × Array SeLe4n.CPtr × Nat))
    (endpointId : Option SeLe4n.ObjId) (target? : Option (TCB × Option CSpaceAddr)) :
    Kernel CapTransferSummary :=
  fun st =>
    match req with
    | none => .ok ({ results := #[] }, st)
    | some (root, addrs, depth) =>
        let caps := resolveExtraCaps root addrs depth true st
        if caps.isEmpty then .ok ({ results := #[] }, st)
        else
          match target? with
          | none => .ok ({ results := #[] }, st)
          | some (rtcb, slot?) => ipcUnwrapCaps caps endpointId rtcb slot? st

/-- **The capabilities a reply asks to transfer**: the request the replier's
frame makes (`senderFrameCapRequest`, read from its saved registers and IPC
buffer as a sender's is) under the reply capability's grant right `grant`
(seL4's `cap_reply_cap_get_capReplyCanGrant`, which `doReplyTransfer` passes
to `doIPCTransfer`).  A replier without that right transfers nothing. -/
def replyCapRequest (st : SystemState) (replier : SeLe4n.ThreadId) (grant : Bool) :
    Option (SeLe4n.ObjId × Array SeLe4n.CPtr × Nat) :=
  match st.getTcb? replier with
  | none => none
  | some tcb => senderFrameCapRequest st replier tcb grant

/-- **A reply's capability transfer** (seL4's `doReplyTransfer` →
`doIPCTransfer(sender, NULL, 0, grant, receiver)`): the replier's request,
transferred to the answered caller's side, both read from the pre-state `pre`,
for a message sent on no endpoint, so no capability unwraps and the first one
the caller's receive slot cannot take stops the transfer. -/
def replyTransferCaps (pre : SystemState) (replier caller : SeLe4n.ThreadId) (grant : Bool) :
    Kernel CapTransferSummary :=
  receiveTransferCaps (replyCapRequest pre replier grant) none (receiverCapTarget? pre caller)

/-- **A reply transfers nothing** when the reply capability lacks the grant
right, the caller has no IPC buffer the kernel may write, or its buffer names
no receive slot: with no endpoint nothing unwraps, so the loop stops at the
first capability (`ipcUnwrapCapsLoop`) and the report is zero. -/
theorem replyTransferCaps_of_inert (pre : SystemState) (replier caller : SeLe4n.ThreadId)
    (grant : Bool) (ct : TCB) (hT : pre.getTcb? caller = some ct)
    (hW : (!grant || !receiverHasBuffer pre ct || (receiveSlot? pre ct).isNone) = true)
    (st : SystemState) :
    replyTransferCaps pre replier caller grant st = .ok ({ results := #[] }, st) := by
  unfold replyTransferCaps receiveTransferCaps
  cases grant
  · have : replyCapRequest pre replier false = none := by
      unfold replyCapRequest; split
      · rfl
      · rfl
    rw [this]
  cases hB : receiverHasBuffer pre ct
  · have : receiverCapTarget? pre caller = none := by
      simp [receiverCapTarget?, hT, hB]
    rw [this]
    rcases replyCapRequest pre replier true with _ | ⟨_, _, _⟩
    · rfl
    · simp only []; split <;> rfl
  have hS : receiveSlot? pre ct = none := by simpa [hB] using hW
  have : receiverCapTarget? pre caller = some (ct, none) := by
    simp [receiverCapTarget?, hT, hB, hS]
  rw [this]
  rcases replyCapRequest pre replier true with _ | ⟨root, addrs, depth⟩
  · rfl
  simp only []
  split
  · rfl
  unfold ipcUnwrapCaps
  generalize resolveExtraCaps root addrs depth true st = caps
  cases hN : caps.size with
  | zero => simp [ipcUnwrapCapsLoop]
  | succ n =>
    simp only [ipcUnwrapCapsLoop]
    cases caps[0]? with
    | none => rfl
    | some tc => simp [capUnwrapsAt]

/-- M-D01: Extended send with capability transfer.

- Sends via `endpointSendDual`.
- If a receiver was waiting (immediate rendezvous): resolves the capabilities
  the sender's frame asks to transfer (`sendCapRequest`, under its capability's
  grant right) in its CSpace now, and transfers them to the receiver
  (`receiveTransferCaps`, the receive side's own transfer), whose side is read
  from the pre-state.
- If no receiver was waiting (sender enqueued): nothing is resolved or
  transferred; the receive that later dequeues the sender resolves its
  capability addresses then.

Returns the transfer summary (empty when nothing is transferred). -/
def endpointSendDualWithCaps
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (payload : SendPayload) : Kernel CapTransferSummary :=
  fun st =>
    let req := sendCapRequest st endpointId sender payload
    let recv? := (st.getEndpoint? endpointId).bind (·.receiveQ.head)
    let target? := recv?.bind (receiverCapTarget? st)
    match endpointSendDual endpointId sender payload st with
    | .error e => .error e
    | .ok ((), st') =>
        match req with
        | none => .ok ({ results := #[] }, st')
        | some _ =>
            match recv? with
            | some _ => receiveTransferCaps req endpointId target? st'
            | none => .error .invalidCapability

/-- M-D01: Extended receive with capability transfer. When a sender is
dequeued (immediate rendezvous on the receive side), the capabilities it asked
to transfer are resolved in its CSpace and transferred to the receiver, whose
side is read from the pre-state (`receiveTransferCaps`).

When no sender is waiting (receiver enqueues), no transfer occurs — the
receiver will get capabilities when a sender later arrives via
`endpointSendDualWithCaps`. -/
def endpointReceiveDualWithCaps
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) : Kernel (SeLe4n.ThreadId × CapTransferSummary) :=
  fun st =>
    -- PR #873 round 8: **did this receive dequeue anything?** Read before the
    -- transition, exactly as `endpointSendDualWithCaps` reads its receiver
    -- before the send: the blocking branch returns the receiver's own id, so
    -- only a rendezvous may transfer anything.
    let rendezvous := (receiveRendezvousSender? st endpointId).isSome
    -- WS-ZA ZA4.7: and what the dequeued sender asks to transfer, read from the
    -- same pre-state (its registers and grant right), with the receiver's side.
    let req := receiveCapRequest st endpointId
    let target? := receiverCapTarget? st receiver
    match endpointReceiveDual endpointId receiver replyId st with
    | .error e => .error e
    | .ok (senderId, st') =>
        if !rendezvous then .ok ((senderId, { results := #[] }), st') else
        match receiveTransferCaps req endpointId target? st' with
        | .error e => .error e
        | .ok (summary, st'') => .ok ((senderId, summary), st'')

/-- **M-D01 (PR #873 round 8): a receive that dequeued nothing transfers
nothing.**

`endpointReceiveDual`'s blocking branch returns the receiver's own id and leaves
`pendingMessage` untouched, so deciding by that field alone re-transferred a
message the receiver had been holding since a previous receive — an extra copy
of authority installed with no sender. The gate is the endpoint's pre-state send
queue, which is what the bare transition itself branches on. -/
theorem endpointReceiveDualWithCaps_blocked_installs_nothing
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) (st st' : SystemState) (senderId : SeLe4n.ThreadId)
    (hBlocked : receiveRendezvousSender? st endpointId = none)
    (hRecv : endpointReceiveDual endpointId receiver replyId st = .ok (senderId, st')) :
    endpointReceiveDualWithCaps endpointId receiver replyId st
      = .ok ((senderId, { results := #[] }), st') := by
  simp [endpointReceiveDualWithCaps, hRecv, hBlocked]

/-- M-D01: Extended call with capability transfer. Same structure as
`endpointSendDualWithCaps` but using `endpointCall` as the base operation. -/
def endpointCallWithCaps
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (payload : SendPayload) : Kernel CapTransferSummary :=
  fun st =>
    let req := sendCapRequest st endpointId caller payload
    let recv? := (st.getEndpoint? endpointId).bind (·.receiveQ.head)
    let target? := recv?.bind (receiverCapTarget? st)
    match endpointCall endpointId caller payload st with
    | .error e => .error e
    | .ok ((), st') =>
        match req with
        | none => .ok ({ results := #[] }, st')
        | some _ =>
            match recv? with
            | some _ => receiveTransferCaps req endpointId target? st'
            | none => .error .invalidCapability

/-- **A transfer writes the CNode its receive slot names, and only that**: the
transfer's object frame is `ipcUnwrapCaps_object_cases` at the slot of its
target. -/
theorem receiveTransferCaps_object_cases
    {req : Option (SeLe4n.ObjId × Array SeLe4n.CPtr × Nat)} {endpointId : Option SeLe4n.ObjId}
    {target? : Option (TCB × Option CSpaceAddr)} {st st' : SystemState}
    {summary : CapTransferSummary} (oid : SeLe4n.ObjId) (hObjInv : st.objects.invExt)
    (h : receiveTransferCaps req endpointId target? st = .ok (summary, st')) :
    SystemState.objectAgreesOffDerivationMetadataAt st' st oid ∨
      ∃ dst, target?.bind (·.2) = some dst ∧ oid = dst.cnode ∧
        (∃ cn, st.objects[oid]? = some (.cnode cn)) ∧
        ∃ cn', st'.objects[oid]? = some (.cnode cn') := by
  unfold receiveTransferCaps at h
  cases req with
  | none =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact .inl (.of_eq (by rw [h.2]))
  | some r =>
    obtain ⟨root, addrs, depth⟩ := r
    simp only at h
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact .inl (.of_eq (by rw [h.2]))
    · cases target? with
      | none =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact .inl (.of_eq (by rw [h.2]))
      | some t =>
        obtain ⟨rtcb, slot?⟩ := t
        simpa using ipcUnwrapCaps_object_cases _ _ _ _ _ _ _ oid hObjInv h

/-- **WS-RR RR7.8**: the CNode a send's transfer writes is the one its lock
footprint names: when the pre-state names a destination, the transfer writes
nothing but that CNode (up to derivation metadata). -/
theorem endpointSendDualWithCaps_writes_destination
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (payload : SendPayload)
    (st stMid st' : SystemState) (summary : CapTransferSummary) (oid : SeLe4n.ObjId)
    (hSend : endpointSendDual endpointId sender payload st = .ok ((), stMid))
    (hObjInv : stMid.objects.invExt)
    (hStep : endpointSendDualWithCaps endpointId sender payload st = .ok (summary, st'))
    (hNe : rendezvousCapsDestination? st endpointId sender payload ≠ some oid) :
    SystemState.objectAgreesOffDerivationMetadataAt st' stMid oid := by
  unfold endpointSendDualWithCaps at hStep
  simp only [hSend] at hStep
  cases hReq : sendCapRequest st endpointId sender payload with
  | none =>
    simp only [hReq, Except.ok.injEq, Prod.mk.injEq] at hStep
    exact .of_eq (by rw [hStep.2])
  | some r =>
    simp only [hReq] at hStep
    cases hR : (st.getEndpoint? endpointId).bind (·.receiveQ.head) with
    | none => simp [hR] at hStep
    | some rid =>
      simp only [hR, Option.bind_some] at hStep
      rcases receiveTransferCaps_object_cases oid hObjInv hStep with h | ⟨dst, hD, hO, -⟩
      · exact h
      · exfalso; apply hNe
        unfold rendezvousCapsDestination?
        simp only [hReq, Option.isNone_some, Bool.false_eq_true, ↓reduceIte, hR, Option.bind_some,
          receiverCapSlot?]
        rw [hD]; simp [hO]

/-- **WS-RR RR7.8**: the call's twin of `endpointSendDualWithCaps_writes_destination`. -/
theorem endpointCallWithCaps_writes_destination
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (payload : SendPayload)
    (st stMid st' : SystemState) (summary : CapTransferSummary) (oid : SeLe4n.ObjId)
    (hCall : endpointCall endpointId caller payload st = .ok ((), stMid))
    (hObjInv : stMid.objects.invExt)
    (hStep : endpointCallWithCaps endpointId caller payload st = .ok (summary, st'))
    (hNe : rendezvousCapsDestination? st endpointId caller payload ≠ some oid) :
    SystemState.objectAgreesOffDerivationMetadataAt st' stMid oid := by
  unfold endpointCallWithCaps at hStep
  simp only [hCall] at hStep
  cases hReq : sendCapRequest st endpointId caller payload with
  | none =>
    simp only [hReq, Except.ok.injEq, Prod.mk.injEq] at hStep
    exact .of_eq (by rw [hStep.2])
  | some r =>
    simp only [hReq] at hStep
    cases hR : (st.getEndpoint? endpointId).bind (·.receiveQ.head) with
    | none => simp [hR] at hStep
    | some rid =>
      simp only [hR, Option.bind_some] at hStep
      rcases receiveTransferCaps_object_cases oid hObjInv hStep with h | ⟨dst, hD, hO, -⟩
      · exact h
      · exfalso; apply hNe
        unfold rendezvousCapsDestination?
        simp only [hReq, Option.isNone_some, Bool.false_eq_true, ↓reduceIte, hR, Option.bind_some,
          receiverCapSlot?]
        rw [hD]; simp [hO]

/-- WS-ZA ZA4.7: **a WithCaps send is its send and then one transfer**: a
successful `endpointSendDualWithCaps` is the base send followed by
`receiveTransferCaps` of the sender's request at the receiver's side read from
the pre-state. -/
theorem endpointSendDualWithCaps_transfer_of
    {endpointId : SeLe4n.ObjId} {sender : SeLe4n.ThreadId} {payload : SendPayload}
    {st stMid st' : SystemState} {summary : CapTransferSummary}
    (hSend : endpointSendDual endpointId sender payload st = .ok ((), stMid))
    (hStep : endpointSendDualWithCaps endpointId sender payload st = .ok (summary, st')) :
    ∃ target?, receiveTransferCaps (sendCapRequest st endpointId sender payload) endpointId
      target? stMid = .ok (summary, st') := by
  unfold endpointSendDualWithCaps at hStep
  simp only [hSend] at hStep
  cases hReq : sendCapRequest st endpointId sender payload with
  | none =>
    simp only [hReq] at hStep
    exact ⟨none, hStep⟩
  | some r =>
    simp only [hReq] at hStep
    split at hStep
    · exact ⟨_, hStep⟩
    · cases hStep

/-- WS-ZA ZA4.7: the call's twin of `endpointSendDualWithCaps_transfer_of`. -/
theorem endpointCallWithCaps_transfer_of
    {endpointId : SeLe4n.ObjId} {caller : SeLe4n.ThreadId} {payload : SendPayload}
    {st stMid st' : SystemState} {summary : CapTransferSummary}
    (hCall : endpointCall endpointId caller payload st = .ok ((), stMid))
    (hStep : endpointCallWithCaps endpointId caller payload st = .ok (summary, st')) :
    ∃ target?, receiveTransferCaps (sendCapRequest st endpointId caller payload) endpointId
      target? stMid = .ok (summary, st') := by
  unfold endpointCallWithCaps at hStep
  simp only [hCall] at hStep
  cases hReq : sendCapRequest st endpointId caller payload with
  | none =>
    simp only [hReq] at hStep
    exact ⟨none, hStep⟩
  | some r =>
    simp only [hReq] at hStep
    split at hStep
    · exact ⟨_, hStep⟩
    · cases hStep

end SeLe4n.Kernel
