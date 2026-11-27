-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ReplyStepCNodeSlotsKept

/-!
# ReplyRecv's receive capability, resolved after the reply

seL4-MCS's `SysReplyRecv` runs `handleInvocation` on the reply capability and
then `handleRecv`, which looks the receive capability up on the state the reply
left: its lookup, its kind and its receive right.  A bad receive capability
raises `CapFault(epCPtr, true)` after the caller has its answer.

`dispatchReplyRecvAfterReply` is the `.replyRecv` syscall in that order.  Where
the reply answers a caller, the reply step runs first and the receive's
endpoint is then read off the post-reply state (`replyRecvReceiveEndpoint`:
the lookup, the kind, the right, then the receive's flow gate, before anything
the receive makes observable).  Every other case runs the receive alone on the
state it was handed, where the order is immaterial, and is the dispatch it
always was.

Where the receive capability resolves on the entry state, the reply step keeps
that resolution (`replyRecvReplyStep_cnodeSlotsKept`), so the new order is the
old one (`dispatchReplyRecvAfterReply_eq_of_entryResolved`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open Architecture.RegisterDecode

/-- **The receive's endpoint, read on the state it is handed** (seL4's
`handleRecv`): the receive capability's resolution, its kind, its receive
right, then the receive's flow gate from the endpoint to the receiver, in
`syscallInvokeTyped`'s and the arm's order. -/
def replyRecvReceiveEndpoint (ctx : LabelingContext) (gate : SyscallGate)
    (tid : SeLe4n.ThreadId) (st : SystemState) : Except KernelError SeLe4n.ObjId :=
  match syscallResolveCap gate st with
  | .error e => .error e
  | .ok (cap, _) =>
    if !syscallTargetAccepted .replyRecv st cap then .error (.invalidCapability 0)
    else if !cap.hasRight gate.requiredRight then .error (syscallMissingRightError .replyRecv)
    else
      match cap.target with
      | .object epId =>
        if endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) then
          .ok epId
        else .error .flowDenied
      | _ => .error (.invalidCapability 0)

/-- **A receive capability good on entry is good after the reply**: over a step
that keeps every CNode, the receive capability resolves to the same endpoint
capability with the same verdicts, and the flow gate reads the endpoint alone. -/
theorem replyRecvReceiveEndpoint_of_cnodeSlotsKept {ctx : LabelingContext}
    {gate : SyscallGate} {tid : SeLe4n.ThreadId} {st st' : SystemState} {cap : Capability}
    {epId : SeLe4n.ObjId} (hK : CNodeSlotsKept st st')
    (hR : syscallResolveCap gate st = .ok (cap, st))
    (hA : syscallTargetAccepted .replyRecv st cap = true)
    (hRt : cap.hasRight gate.requiredRight = true) (hT : cap.target = .object epId)
    (hF : endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) = true) :
    replyRecvReceiveEndpoint ctx gate tid st' = .ok epId := by
  obtain ⟨hR', hA'⟩ := replyRecvReceiveCap_of_cnodeSlotsKept hK gate hR hA
  unfold replyRecvReceiveEndpoint
  rw [hR']
  dsimp only
  rw [hA', hRt, if_neg (by decide), if_neg (by decide), hT]
  dsimp only
  rw [if_pos hF]

/-- **The reply-receive composite, its receive's endpoint read after the
reply**: `endpointReplyRecvAnsweringBody` with the endpoint the receive runs on
read by `recvEp` on the state the reply step left (the reply leg, the pop, the
reply's capability transfer and the caller's answer), before the receive's
return of a bound notification's context and its leg. -/
def endpointReplyRecvAnsweringBodyThen (answer : Option Architecture.FaultReplyOutcome)
    (recvEp : SystemState → Except KernelError SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : Concurrency.CoreId) (recordedServer : SeLe4n.ThreadId)
    (req : Option (Capability × Array SeLe4n.CPtr)) (target : Option (TCB × Option CSpaceAddr))
    (st : SystemState) : Except KernelError (CapTransferSummary × SystemState) :=
    match endpointReplyOnCore tid prevCaller msg executingCore st with
    | (_, .error e) => .error e
    | (st1, .ok _replySgi) =>
        match replyRecvPopDonation rid prevCaller st1 with
        | .error e => .error e
        | .ok (returnedSc?, st1q) =>
        match receiveTransferCaps req none target st1q with
        | .error e => .error e
        | .ok (replySummary, st1p) =>
        let stA := replyRecvAnswerCaller answer st1p prevCaller replySummary.capInfo
        match recvEp stA with
        | .error e => .error e
        | .ok epId =>
        match endpointReceiveDualWithCapsOnCore epId tid (some rid) executingCore
            (receiveReturnSchedContext true stA tid) with
        | (_, .error e) => .error e
        | (st2, .ok (nextThread, summary, _)) =>
            match replyRecvPostReceiveDonation tid recordedServer nextThread executingCore
                returnedSc? st2 with
            | .error e => .error e
            | .ok ((), st3) =>
                .ok (summary, applyReceiveLegPipHandoff st3 tid nextThread recordedServer
                  executingCore)

/-- **Where the endpoint the reply step leaves is the entry's, the composite
is the composite on that endpoint**: `recvEp` answers `epId` on every state
that keeps the entry's CNodes, and the reply step is such a state
(`replyRecvReplyStep_cnodeSlotsKept`). -/
theorem endpointReplyRecvAnsweringBodyThen_eq {answer : Option Architecture.FaultReplyOutcome}
    {recvEp : SystemState → Except KernelError SeLe4n.ObjId} {epId : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId}
    {msg : IpcMessage} {executingCore : Concurrency.CoreId} {recordedServer : SeLe4n.ThreadId}
    {req : Option (Capability × Array SeLe4n.CPtr)} {target : Option (TCB × Option CSpaceAddr)}
    {st : SystemState} (hInv : st.objects.invExt)
    (hEp : ∀ s, CNodeSlotsKept st s → recvEp s = .ok epId) :
    endpointReplyRecvAnsweringBodyThen answer recvEp tid rid prevCaller msg executingCore
        recordedServer req target st =
      endpointReplyRecvAnsweringBody answer epId tid rid prevCaller msg executingCore
        recordedServer req target st := by
  unfold endpointReplyRecvAnsweringBodyThen endpointReplyRecvAnsweringBody
  cases hL : endpointReplyOnCore tid prevCaller msg executingCore st with
  | mk st1 r1 =>
    cases r1 with
    | error e => rfl
    | ok sgi =>
      dsimp only
      cases hP : replyRecvPopDonation rid prevCaller st1 with
      | error e => rfl
      | ok p =>
        obtain ⟨ret, st1q⟩ := p
        dsimp only
        cases hX : receiveTransferCaps req none target st1q with
        | error e => rfl
        | ok q =>
          obtain ⟨sum, st1p⟩ := q
          dsimp only
          rw [hEp _ (replyRecvReplyStep_cnodeSlotsKept hInv hL hP hX)]
          rfl

/-- **The arm's transition, its receive's endpoint read after the reply**:
`replyRecvTransferOnCore` over `endpointReplyRecvAnsweringBodyThen`. -/
def replyRecvTransferThen (recvEp : SystemState → Except KernelError SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId) (label : Nat)
    (msg : IpcMessage) (grant : Bool) (executingCore : Concurrency.CoreId) (st : SystemState) :
    Except KernelError (CapTransferSummary × SystemState) :=
  if replyRecvPopAdmits st rid prevCaller then
    endpointReplyRecvAnsweringBodyThen (replyRecvCallerFaultAnswer? st prevCaller label msg) recvEp
      tid rid prevCaller (replyRecvLegMessage (replyRecvCallerFaultAnswer? st prevCaller label msg) msg)
      executingCore ((recordedReplyServer? st prevCaller).getD tid)
      (if (replyRecvCallerFaultAnswer? st prevCaller label msg).isSome then none
        else replyCapRequest st tid grant)
      (receiverCapTarget? st prevCaller) st
  else .error (.invalidArgument 0)

theorem replyRecvTransferThen_eq {recvEp : SystemState → Except KernelError SeLe4n.ObjId}
    {epId : SeLe4n.ObjId} {tid : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    {prevCaller : SeLe4n.ThreadId} {label : Nat} {msg : IpcMessage} {grant : Bool}
    {executingCore : Concurrency.CoreId} {st : SystemState} (hInv : st.objects.invExt)
    (hEp : ∀ s, CNodeSlotsKept st s → recvEp s = .ok epId) :
    replyRecvTransferThen recvEp tid rid prevCaller label msg grant executingCore st =
      replyRecvTransferOnCore epId tid rid prevCaller label msg grant executingCore st := by
  unfold replyRecvTransferThen replyRecvTransferOnCore
  by_cases hAd : replyRecvPopAdmits st rid prevCaller = true
  · rw [if_pos hAd, if_pos hAd, endpointReplyRecvAnsweringOnCore_eq_checked]
    unfold endpointReplyRecvAnsweringOnCoreChecked
    exact endpointReplyRecvAnsweringBodyThen_eq hInv hEp
  · rw [if_neg hAd, if_neg hAd]

/-- **The reply-receive that completes a signal, its receive capability read
after the reply**: the `.reply` arm's transition, then the receive's endpoint
(`recvEp`, its lookup, verdicts and flow gate) on the state it left, then the
completion of the bound notification. -/
def replyRecvCompletesSignalArmThen (ctx : LabelingContext)
    (recvEp : SystemState → Except KernelError SeLe4n.ObjId) (tid prevCaller : SeLe4n.ThreadId)
    (label : Nat) (msg : IpcMessage) (grant : Bool) (executingCore : Concurrency.CoreId) :
    Kernel Unit :=
  fun st =>
    match replyTransferOnCoreChecked ctx tid prevCaller (replyRecvReplyMessageInfo label msg)
        msg.registers msg grant executingCore st with
    | .error e => .error e
    | .ok ((), st1) =>
        match recvEp st1 with
        | .error e => .error e
        | .ok _ =>
          if receiveCompletesSignal ctx st1 tid && receiverIpcReady st1 tid then
            completeSignalArm ctx tid (receiverBoundNotification st1 tid) executingCore st1
          else .ok ((), st1)

theorem replyRecvCompletesSignalArmThen_eq {ctx : LabelingContext}
    {recvEp : SystemState → Except KernelError SeLe4n.ObjId} {epId : SeLe4n.ObjId}
    {tid prevCaller : SeLe4n.ThreadId} {label : Nat} {msg : IpcMessage} {grant : Bool}
    {executingCore : Concurrency.CoreId} {st : SystemState} (hInv : st.objects.invExt)
    (hEp : ∀ s, CNodeSlotsKept st s → recvEp s = .ok epId) :
    replyRecvCompletesSignalArmThen ctx recvEp tid prevCaller label msg grant executingCore st =
      replyRecvCompletesSignalArm ctx tid prevCaller label msg grant executingCore st := by
  unfold replyRecvCompletesSignalArmThen replyRecvCompletesSignalArm
  cases hR : replyTransferOnCoreChecked ctx tid prevCaller (replyRecvReplyMessageInfo label msg)
      msg.registers msg grant executingCore st with
  | error e => rfl
  | ok p =>
    obtain ⟨⟨⟩, st1⟩ := p
    dsimp only
    rw [hEp _ (replyTransferOnCoreChecked_cnodeSlotsKept hInv hR)]

/-- **The reply a reply-receive answers before its receive**: none where an
extra capability does not look up (the reply is skipped, WS-SX SX6.1), where
the reply capability does not resolve, has no caller, or does not answer it;
the resolved reply otherwise. -/
def replyRecvAnsweringReply? (ctx : LabelingContext) (gate : SyscallGate)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (st : SystemState) :
    Option (SeLe4n.ReplyId × SeLe4n.ThreadId × Option SeLe4n.Badge × Bool) :=
  match callerExtraCapsFault? st tid decoded.msgInfo.extraCaps with
  | some _ => none
  | none =>
    match resolveReplyRecvReply gate decoded st with
    | .ok (some (rid, prevCaller, replyBadge, replyGrant)) =>
      if replyRecvReplyAnswers ctx st tid prevCaller then
        some (rid, prevCaller, replyBadge, replyGrant)
      else none
    | _ => none

/-- **An answering reply-receive, its receive capability read after the
reply**: the `.replyRecv` arm's answering case with the receive's endpoint
read by `recvEp` once the caller is answered. -/
def replyRecvAnsweringThen (ctx : LabelingContext)
    (recvEp : SystemState → Except KernelError SeLe4n.ObjId) (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (rid : SeLe4n.ReplyId)
    (prevCaller : SeLe4n.ThreadId) (replyBadge : Option SeLe4n.Badge) (replyGrant : Bool) :
    Kernel Unit :=
  fun st =>
    let msg : IpcMessage :=
      { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo, badge := replyBadge }
    if receiveCompletesSignal ctx st tid then
      replyRecvCompletesSignalArmThen ctx recvEp tid prevCaller decoded.msgInfo.label msg
        replyGrant executingCore st
    else
      match replyRecvTransferThen recvEp tid rid prevCaller decoded.msgInfo.label msg replyGrant
          executingCore st with
      | .ok (summary, st') => .ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo)
      | .error e => .error e

/-- **The `.replyRecv` syscall in seL4's order** (`SysReplyRecv`:
`handleInvocation` on the reply capability, then `handleRecv`): where the reply
answers a caller, the reply step, then the receive capability's lookup, kind,
right and flow gate on the state it left (`replyRecvReceiveEndpoint`), then the
receive; otherwise the receive alone, through the syscall gate on the state
handed in, as before. -/
def dispatchReplyRecvAfterReply (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate) :
    Kernel Unit :=
  fun st =>
    match replyRecvAnsweringReply? ctx gate decoded tid st with
    | none =>
      syscallInvokeTyped .replyRecv gate none
        (dispatchWithCapChecked ctx decoded tid executingCore gate) st
    | some (rid, prevCaller, replyBadge, replyGrant) =>
      replyRecvAnsweringThen ctx (replyRecvReceiveEndpoint ctx gate tid) decoded tid executingCore
        rid prevCaller replyBadge replyGrant st

/-- **Where the receive capability resolves on entry, seL4's order is the
entry's order**: the reply step keeps the receive capability's resolution, its
verdicts and so its endpoint (`replyRecvReceiveEndpoint_of_cnodeSlotsKept`), so
the receive runs on the endpoint the entry resolved. -/
theorem dispatchReplyRecvAfterReply_eq_of_entryResolved {ctx : LabelingContext}
    {decoded : SyscallDecodeResult} {tid : SeLe4n.ThreadId} {executingCore : Concurrency.CoreId}
    {gate : SyscallGate} {st : SystemState} {cap : Capability} {epId : SeLe4n.ObjId}
    (hSid : decoded.syscallId = .replyRecv) (hInv : st.objects.invExt)
    (hR : syscallResolveCap gate st = .ok (cap, st))
    (hA : syscallTargetAccepted .replyRecv st cap = true)
    (hRt : cap.hasRight gate.requiredRight = true) (hT : cap.target = .object epId)
    (hF : endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) = true) :
    dispatchReplyRecvAfterReply ctx decoded tid executingCore gate st =
      syscallInvokeTyped .replyRecv gate none
        (dispatchWithCapChecked ctx decoded tid executingCore gate) st := by
  have hEp : ∀ s, CNodeSlotsKept st s → replyRecvReceiveEndpoint ctx gate tid s = .ok epId :=
    fun _ hK => replyRecvReceiveEndpoint_of_cnodeSlotsKept hK hR hA hRt hT hF
  unfold dispatchReplyRecvAfterReply
  cases hAns : replyRecvAnsweringReply? ctx gate decoded tid st with
  | none => rfl
  | some a =>
    obtain ⟨rid, prevCaller, replyBadge, replyGrant⟩ := a
    dsimp only
    unfold syscallInvokeTyped
    rw [hR]
    dsimp only
    rw [hA, hRt, if_neg (by decide), if_pos rfl]
    unfold replyRecvAnsweringReply? at hAns
    obtain ⟨capAddr, mi, sid, regs, ic, oc, cr, rp⟩ := decoded
    dsimp only at hSid
    subst hSid
    obtain ⟨target, rights, badge⟩ := cap
    dsimp only at hT
    subst hT
    unfold dispatchWithCapChecked dispatchCapabilityOnly
    dsimp only
    rw [hF, if_neg (by decide)]
    dsimp only at hAns
    cases hX : callerExtraCapsFault? st tid mi.extraCaps with
    | some _ => rw [hX] at hAns; cases hAns
    | none =>
      rw [hX] at hAns
      dsimp only at hAns ⊢
      cases hRr : resolveReplyRecvReply gate ⟨capAddr, mi, .replyRecv, regs, ic, oc, cr, rp⟩ st with
      | error e => rw [hRr] at hAns; cases hAns
      | ok r =>
        rw [hRr] at hAns
        cases r with
        | none => cases hAns
        | some q =>
          obtain ⟨rid', pc', b', g'⟩ := q
          dsimp only at hAns ⊢
          by_cases hAw : replyRecvReplyAnswers ctx st tid pc' = true
          · rw [if_pos hAw] at hAns
            cases hAns
            rw [if_pos hAw]
            unfold replyRecvAnsweringThen
            dsimp only
            by_cases hSig : receiveCompletesSignal ctx st tid = true
            · rw [if_pos hSig, if_pos hSig]
              exact replyRecvCompletesSignalArmThen_eq hInv hEp
            · rw [if_neg hSig, if_neg hSig, replyRecvTransferThen_eq hInv hEp]
              rcases replyRecvTransferOnCore epId tid rid prevCaller mi.label _ replyGrant
                executingCore st with e | ⟨summary, st'⟩ <;> rfl
          · rw [if_neg hAw] at hAns; cases hAns

end SeLe4n.Kernel
