-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ReplyRecvReceiveAfterReply
import SeLe4n.Kernel.RefusalCarryingReplyRecvTransfer

/-!
# ReplyRecv in seL4's order, each refusal carrying the state it stopped in

The answering reply-receive of `ReplyRecvReceiveAfterReply` (the reply step,
then the receive capability's lookup, verdicts and flow gate on the state the
reply left, then the receive), with each refusal carrying the state its step
stopped in, as `replyRecvTransferOnCoreR` carries it for the entry order.

seL4's `handleInvocation` has completed the reply before `handleRecv` looks the
receive capability up, so a refusal of that lookup leaves the reply's effects
as they are.  Both arms give it one outcome, the nothing-received outcome of
D53 (the holder's deschedule where the pop handed a context back, and the
recorded server's priority-inheritance reversion):

* in the composite, the pop defers the deschedule, so a refusal of the
  receive's endpoint reports `replyRecvNothingReceived` on the state the
  caller's answer left, as a refused receive leg does;
* where the receive completes a bound notification, the reply is the `.reply`
  arm's transition (`replyTransferOnCoreChecked`), whose pop deschedules the
  holder (`applyReplyDonationOnCore`) and whose tail reverts the recorded
  server's priority inheritance (`endpointReplyCrossCoreDispatch`): the state
  it returns is already that outcome, and a later refusal carries it as it is.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open Architecture.RegisterDecode

/-- **The state a refusal-carrying computation stopped in**: the state its
refusal carries, and the state handed in where it does not refuse. -/
def RefusalCarrying.stoppedState {α : Type} (r : RefusalCarrying α) (st : SystemState) :
    SystemState :=
  match r st with
  | .error (_, s) => s
  | .ok _ => st

/-- A refusal-carrying computation that is `k` with the refusal's state
forgotten is `k` reporting the state it stopped in. -/
theorem RefusalCarrying.eq_reporting_of_mapError {α : Type} {r : RefusalCarrying α}
    {k : Kernel α} {st : SystemState} (h : (r st).mapError Prod.fst = k st) :
    r st = RefusalCarrying.ofKernelReporting (RefusalCarrying.stoppedState r) k st := by
  unfold RefusalCarrying.ofKernelReporting RefusalCarrying.stoppedState
  rw [← h]
  cases r st with
  | error es => obtain ⟨e, s⟩ := es; rfl
  | ok a => rfl

/-- **The composite in seL4's order, each refusal carrying the state its step
stopped in**: `endpointReplyRecvAnsweringBodyThen` with the pop and the
post-receive donation in their refusal-carrying forms and the reply's transfer
as its result; a refusal of the receive's endpoint (`recvEp`), of the receive
leg or of the post-receive donation reports the nothing-received outcome
(`replyRecvNothingReceived`) on the state that step was handed or returned. -/
@[noinline] def endpointReplyRecvAnsweringBodyThenR
    (answer : Option Architecture.FaultReplyOutcome)
    (recvEp : SystemState → Except KernelError SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : Concurrency.CoreId) (recordedServer : SeLe4n.ThreadId)
    (req : Option (Capability × Array SeLe4n.CPtr)) (target : Option (TCB × Option CSpaceAddr)) :
    RefusalCarrying CapTransferSummary := fun st =>
  match endpointReplyOnCore tid prevCaller msg executingCore st with
  | (s, .error e) => .error (e, s)
  | (st1, .ok _replySgi) =>
    match replyRecvPopDonationR rid prevCaller st1 with
    | .error es => .error es
    | .ok (returnedSc?, st1q) =>
      match receiveTransferCapsDone req none target st1q with
      | (replySummary, st1p) =>
      let stA := replyRecvAnswerCaller answer st1p prevCaller replySummary.capInfo
      match recvEp stA with
      | .error e =>
          .error (e, replyRecvNothingReceived recordedServer executingCore returnedSc? stA)
      | .ok epId =>
      match endpointReceiveDualWithCapsOnCore epId tid (some rid) executingCore
          (receiveReturnSchedContext true stA tid) with
      | (s, .error e) =>
          .error (e, replyRecvNothingReceived recordedServer executingCore returnedSc? s)
      | (st2, .ok (nextThread, summary, _)) =>
          match replyRecvPostReceiveDonationR tid recordedServer nextThread executingCore
              returnedSc? st2 with
          | .error (e, s) =>
              .error (e, replyRecvNothingReceived recordedServer executingCore returnedSc? s)
          | .ok ((), st3) =>
              .ok (summary, applyReceiveLegPipHandoff st3 tid nextThread recordedServer
                executingCore)

/-- The refusal-carrying composite is the composite with the refusal's state
forgotten, with no assumption. -/
theorem endpointReplyRecvAnsweringBodyThenR_eq (answer : Option Architecture.FaultReplyOutcome)
    (recvEp : SystemState → Except KernelError SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : Concurrency.CoreId) (recordedServer : SeLe4n.ThreadId)
    (req : Option (Capability × Array SeLe4n.CPtr)) (target : Option (TCB × Option CSpaceAddr))
    (st : SystemState) :
    (endpointReplyRecvAnsweringBodyThenR answer recvEp tid rid prevCaller msg executingCore
        recordedServer req target st).mapError Prod.fst =
      endpointReplyRecvAnsweringBodyThen answer recvEp tid rid prevCaller msg executingCore
        recordedServer req target st := by
  unfold endpointReplyRecvAnsweringBodyThenR endpointReplyRecvAnsweringBodyThen
  cases hL : endpointReplyOnCore tid prevCaller msg executingCore st with
  | mk st1 r1 =>
    cases r1 with
    | error e => rfl
    | ok sgi =>
      dsimp only
      rw [← replyRecvPopDonationR_eq]
      cases hP : replyRecvPopDonationR rid prevCaller st1 with
      | error es => rfl
      | ok p =>
        obtain ⟨ret, st1q⟩ := p
        rw [refusalCarrying_mapError_ok]
        dsimp only
        rw [receiveTransferCaps_eq_done]
        generalize receiveTransferCapsDone req none target st1q = d
        obtain ⟨sum, st1p⟩ := d
        dsimp only
        cases hE : recvEp (replyRecvAnswerCaller answer st1p prevCaller sum.capInfo) with
        | error e => rfl
        | ok epId =>
          dsimp only
          cases hR : endpointReceiveDualWithCapsOnCore epId tid (some rid) executingCore
              (receiveReturnSchedContext true
                (replyRecvAnswerCaller answer st1p prevCaller sum.capInfo) tid) with
          | mk st2 r2 =>
            cases r2 with
            | error e => rfl
            | ok q =>
              obtain ⟨nextThread, summary, x⟩ := q
              dsimp only
              rw [← replyRecvPostReceiveDonationR_eq]
              cases replyRecvPostReceiveDonationR tid recordedServer nextThread executingCore
                  ret st2 with
              | error es => obtain ⟨e, s⟩ := es; rfl
              | ok u => obtain ⟨⟨⟩, st3⟩ := u; rfl

/-- **The arm's transition in seL4's order, each refusal carrying the state its
step stopped in**: `replyRecvTransferThen` over the refusal-carrying composite.
A refused pop admission carries the state handed in, since it precedes every
write. -/
def replyRecvTransferThenR (recvEp : SystemState → Except KernelError SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId) (label : Nat)
    (msg : IpcMessage) (grant : Bool) (executingCore : Concurrency.CoreId) :
    RefusalCarrying CapTransferSummary := fun st =>
  if replyRecvPopAdmits st rid prevCaller then
    let answer := replyRecvCallerFaultAnswer? st prevCaller label msg
    endpointReplyRecvAnsweringBodyThenR answer recvEp tid rid prevCaller
      (replyRecvLegMessage answer msg) executingCore ((recordedReplyServer? st prevCaller).getD tid)
      (if answer.isSome then none else replyCapRequest st tid grant)
      (receiverCapTarget? st prevCaller) st
  else .error (.invalidArgument 0, st)

theorem replyRecvTransferThenR_eq (recvEp : SystemState → Except KernelError SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId) (label : Nat)
    (msg : IpcMessage) (grant : Bool) (executingCore : Concurrency.CoreId) (st : SystemState) :
    (replyRecvTransferThenR recvEp tid rid prevCaller label msg grant executingCore st).mapError
        Prod.fst =
      replyRecvTransferThen recvEp tid rid prevCaller label msg grant executingCore st := by
  unfold replyRecvTransferThenR replyRecvTransferThen
  by_cases hAd : replyRecvPopAdmits st rid prevCaller = true
  · rw [if_pos hAd, if_pos hAd]
    exact endpointReplyRecvAnsweringBodyThenR_eq _ _ _ _ _ _ _ _ _ _ st
  · rw [if_neg hAd, if_neg hAd]; rfl

/-- **The reply-receive that completes a signal, in seL4's order, each refusal
carrying the state its step stopped in**: a refusal of the `.reply` arm's
transition carries the state handed in, as the entry order's report does; a
refusal after it (the receive's endpoint, or the completion of the bound
notification) carries the state the reply left, which is already the
nothing-received outcome (the transition's pop deschedules the holder and its
tail reverts the recorded server's priority inheritance). -/
def replyRecvCompletesSignalArmThenR (ctx : LabelingContext)
    (recvEp : SystemState → Except KernelError SeLe4n.ObjId) (tid prevCaller : SeLe4n.ThreadId)
    (label : Nat) (msg : IpcMessage) (grant : Bool) (executingCore : Concurrency.CoreId) :
    RefusalCarrying Unit := fun st =>
  match replyTransferOnCoreChecked ctx tid prevCaller (replyRecvReplyMessageInfo label msg)
      msg.registers msg grant executingCore st with
  | .error e => .error (e, st)
  | .ok ((), st1) =>
      match recvEp st1 with
      | .error e => .error (e, st1)
      | .ok _ =>
        if receiveCompletesSignal ctx st1 tid && receiverIpcReady st1 tid then
          match completeSignalArm ctx tid (receiverBoundNotification st1 tid) executingCore st1 with
          | .ok r => .ok r
          | .error e => .error (e, st1)
        else .ok ((), st1)

theorem replyRecvCompletesSignalArmThenR_eq (ctx : LabelingContext)
    (recvEp : SystemState → Except KernelError SeLe4n.ObjId) (tid prevCaller : SeLe4n.ThreadId)
    (label : Nat) (msg : IpcMessage) (grant : Bool) (executingCore : Concurrency.CoreId)
    (st : SystemState) :
    (replyRecvCompletesSignalArmThenR ctx recvEp tid prevCaller label msg grant executingCore
        st).mapError Prod.fst =
      replyRecvCompletesSignalArmThen ctx recvEp tid prevCaller label msg grant executingCore st := by
  unfold replyRecvCompletesSignalArmThenR replyRecvCompletesSignalArmThen
  cases replyTransferOnCoreChecked ctx tid prevCaller (replyRecvReplyMessageInfo label msg)
      msg.registers msg grant executingCore st with
  | error e => rfl
  | ok p =>
    obtain ⟨⟨⟩, st1⟩ := p
    dsimp only
    cases recvEp st1 with
    | error e => rfl
    | ok epId =>
      dsimp only
      by_cases hC : (receiveCompletesSignal ctx st1 tid && receiverIpcReady st1 tid) = true
      · rw [if_pos hC, if_pos hC]
        cases completeSignalArm ctx tid (receiverBoundNotification st1 tid) executingCore st1 <;>
          rfl
      · rw [if_neg hC, if_neg hC]; rfl

/-- **An answering reply-receive in seL4's order, each refusal carrying the
state its step stopped in**: `replyRecvAnsweringThen` over the refusal-carrying
signal arm and transition. -/
def replyRecvAnsweringThenR (ctx : LabelingContext)
    (recvEp : SystemState → Except KernelError SeLe4n.ObjId) (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (rid : SeLe4n.ReplyId)
    (prevCaller : SeLe4n.ThreadId) (replyBadge : Option SeLe4n.Badge) (replyGrant : Bool) :
    RefusalCarrying Unit := fun st =>
  let msg : IpcMessage :=
    { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo, badge := replyBadge }
  if receiveCompletesSignal ctx st tid then
    replyRecvCompletesSignalArmThenR ctx recvEp tid prevCaller decoded.msgInfo.label msg
      replyGrant executingCore st
  else
    match replyRecvTransferThenR recvEp tid rid prevCaller decoded.msgInfo.label msg replyGrant
        executingCore st with
    | .ok (summary, st') => .ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo)
    | .error es => .error es

theorem replyRecvAnsweringThenR_eq (ctx : LabelingContext)
    (recvEp : SystemState → Except KernelError SeLe4n.ObjId) (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (rid : SeLe4n.ReplyId)
    (prevCaller : SeLe4n.ThreadId) (replyBadge : Option SeLe4n.Badge) (replyGrant : Bool)
    (st : SystemState) :
    (replyRecvAnsweringThenR ctx recvEp decoded tid executingCore rid prevCaller replyBadge
        replyGrant st).mapError Prod.fst =
      replyRecvAnsweringThen ctx recvEp decoded tid executingCore rid prevCaller replyBadge
        replyGrant st := by
  unfold replyRecvAnsweringThenR replyRecvAnsweringThen
  dsimp only
  by_cases hSig : receiveCompletesSignal ctx st tid = true
  · rw [if_pos hSig, if_pos hSig]
    exact replyRecvCompletesSignalArmThenR_eq _ _ _ _ _ _ _ _ st
  · rw [if_neg hSig, if_neg hSig, ← replyRecvTransferThenR_eq]
    cases replyRecvTransferThenR recvEp tid rid prevCaller decoded.msgInfo.label
        { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo,
          badge := replyBadge } replyGrant executingCore st with
    | error es => obtain ⟨e, s⟩ := es; rfl
    | ok r => obtain ⟨summary, st'⟩ := r; rfl

/-- **The state an answering reply-receive's refusal reports, in seL4's
order**: keyed on the reply it answers (`replyRecvAnsweringReply?`), the state
the refusing step stopped in, the receive's endpoint read after the reply
(`replyRecvReceiveEndpoint`); the state handed in where the reply answers no
caller, since the receive then runs alone. -/
def replyRecvAfterReplyAnsweringReport (ctx : LabelingContext) (gate : SyscallGate)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (st : SystemState) : SystemState :=
  match replyRecvAnsweringReply? ctx gate decoded tid st with
  | none => st
  | some (rid, prevCaller, replyBadge, replyGrant) =>
      RefusalCarrying.stoppedState
        (replyRecvAnsweringThenR ctx (replyRecvReceiveEndpoint ctx gate tid) decoded tid
          executingCore rid prevCaller replyBadge replyGrant) st

/-- An answering reply-receive in seL4's order reports, on a refusal, the
state its refusing step stopped in (`replyRecvAfterReplyAnsweringReport`). -/
theorem replyRecvAnsweringThenR_eq_reporting {ctx : LabelingContext} {gate : SyscallGate}
    {decoded : SyscallDecodeResult} {tid : SeLe4n.ThreadId} {executingCore : Concurrency.CoreId}
    {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId} {replyBadge : Option SeLe4n.Badge}
    {replyGrant : Bool} {st : SystemState}
    (hAns : replyRecvAnsweringReply? ctx gate decoded tid st =
      some (rid, prevCaller, replyBadge, replyGrant)) :
    replyRecvAnsweringThenR ctx (replyRecvReceiveEndpoint ctx gate tid) decoded tid executingCore
        rid prevCaller replyBadge replyGrant st =
      RefusalCarrying.ofKernelReporting
        (fun _ => replyRecvAfterReplyAnsweringReport ctx gate decoded tid executingCore st)
        (replyRecvAnsweringThen ctx (replyRecvReceiveEndpoint ctx gate tid) decoded tid
          executingCore rid prevCaller replyBadge replyGrant) st := by
  have h := RefusalCarrying.eq_reporting_of_mapError
    (replyRecvAnsweringThenR_eq ctx (replyRecvReceiveEndpoint ctx gate tid) decoded tid
      executingCore rid prevCaller replyBadge replyGrant st)
  rw [h]
  unfold replyRecvAfterReplyAnsweringReport
  rw [hAns]
  rfl

end SeLe4n.Kernel
