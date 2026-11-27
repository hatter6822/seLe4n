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

The definitions are in `SeLe4n.Kernel.API`, beside the dispatcher that runs
them (`dispatchSyscallArmChecked`); this module holds their theorems.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open Architecture.RegisterDecode

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

/-- The receive's endpoint on a state where its capability resolves, is of
the receive's kind, carries its right, names `epId` and passes the flow gate. -/
theorem replyRecvReceiveEndpoint_of_resolved {ctx : LabelingContext}
    {gate : SyscallGate} {tid : SeLe4n.ThreadId} {st : SystemState} {cap : Capability}
    {epId : SeLe4n.ObjId}
    (hR : syscallResolveCap gate st = .ok (cap, st))
    (hA : syscallTargetAccepted .replyRecv st cap = true)
    (hRt : cap.hasRight gate.requiredRight = true) (hT : cap.target = .object epId)
    (hF : endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) = true) :
    replyRecvReceiveEndpoint ctx gate tid st = .ok epId := by
  unfold replyRecvReceiveEndpoint
  rw [hR]
  dsimp only
  rw [hA, hRt, if_neg (by decide), if_neg (by decide), hT]
  dsimp only
  rw [if_pos hF]

/-- **An answering reply-receive whose receive capability resolves on entry is
the entry's order**: the reply step keeps the receive capability's resolution,
its verdicts and so its endpoint (`replyRecvReceiveEndpoint_of_cnodeSlotsKept`),
so the receive read after the reply runs on the endpoint the entry resolved. -/
theorem replyRecvAnsweringThen_eq_of_entryResolved {ctx : LabelingContext}
    {decoded : SyscallDecodeResult} {tid : SeLe4n.ThreadId} {executingCore : Concurrency.CoreId}
    {gate : SyscallGate} {st : SystemState} {cap : Capability} {epId : SeLe4n.ObjId}
    {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId} {replyBadge : Option SeLe4n.Badge}
    {replyGrant : Bool}
    (hSid : decoded.syscallId = .replyRecv) (hInv : st.objects.invExt)
    (hR : syscallResolveCap gate st = .ok (cap, st))
    (hA : syscallTargetAccepted .replyRecv st cap = true)
    (hRt : cap.hasRight gate.requiredRight = true) (hT : cap.target = .object epId)
    (hF : endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) = true)
    (hAns : replyRecvAnsweringReply? ctx gate decoded tid st =
      some (rid, prevCaller, replyBadge, replyGrant)) :
    replyRecvAnsweringThen ctx (replyRecvReceiveEndpoint ctx gate tid) decoded tid executingCore
        rid prevCaller replyBadge replyGrant st =
      syscallInvokeTyped .replyRecv gate none
        (dispatchWithCapChecked ctx decoded tid executingCore gate) st := by
  have hEp : ∀ s, CNodeSlotsKept st s → replyRecvReceiveEndpoint ctx gate tid s = .ok epId :=
    fun _ hK => replyRecvReceiveEndpoint_of_cnodeSlotsKept hK hR hA hRt hT hF
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
        · rw [if_neg hAw] at hAns; cases hAns


/-- **Where the receive capability resolves on entry, the dispatch is the
entry's order**: the reply-receive in seL4's order reads the entry's resolution
there by construction. -/
theorem dispatchReplyRecvAfterReply_eq_of_entryResolved {ctx : LabelingContext}
    {decoded : SyscallDecodeResult} {tid : SeLe4n.ThreadId} {executingCore : Concurrency.CoreId}
    {gate : SyscallGate} {st : SystemState} {cap : Capability} {epId : SeLe4n.ObjId}
    (hR : syscallResolveCap gate st = .ok (cap, st))
    (hA : syscallTargetAccepted .replyRecv st cap = true)
    (hRt : cap.hasRight gate.requiredRight = true) (hT : cap.target = .object epId)
    (hF : endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) = true) :
    dispatchReplyRecvAfterReply ctx decoded tid executingCore gate st =
      syscallInvokeTyped .replyRecv gate none
        (dispatchWithCapChecked ctx decoded tid executingCore gate) st := by
  unfold dispatchReplyRecvAfterReply
  cases replyRecvAnsweringReply? ctx gate decoded tid st with
  | none => rfl
  | some a =>
    obtain ⟨rid, prevCaller, replyBadge, replyGrant⟩ := a
    dsimp only
    rw [replyRecvReceiveEndpoint_of_resolved hR hA hRt hT hF]

/-- **The dispatch is seL4's order** (`SysReplyRecv`: `handleInvocation` on the
reply capability, then `handleRecv`): on a state whose object store is well
formed, an answering reply-receive is the reply step, then the receive
capability's lookup, verdicts and flow gate on the state the reply step left,
then the receive.  Where the entry refuses the receive capability the dispatch
reads it after the reply by construction; where the entry resolves it, the
reply step keeps that resolution (`replyRecvAnsweringThen_eq_of_entryResolved`). -/
theorem dispatchReplyRecvAfterReply_eq_sel4Order {ctx : LabelingContext}
    {decoded : SyscallDecodeResult} {tid : SeLe4n.ThreadId} {executingCore : Concurrency.CoreId}
    {gate : SyscallGate} {st : SystemState} {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId}
    {replyBadge : Option SeLe4n.Badge} {replyGrant : Bool}
    (hSid : decoded.syscallId = .replyRecv) (hInv : st.objects.invExt)
    (hAns : replyRecvAnsweringReply? ctx gate decoded tid st =
      some (rid, prevCaller, replyBadge, replyGrant)) :
    dispatchReplyRecvAfterReply ctx decoded tid executingCore gate st =
      replyRecvAnsweringThen ctx (replyRecvReceiveEndpoint ctx gate tid) decoded tid executingCore
        rid prevCaller replyBadge replyGrant st := by
  unfold dispatchReplyRecvAfterReply
  rw [hAns]
  dsimp only
  cases hEp0 : replyRecvReceiveEndpoint ctx gate tid st with
  | error _ => rfl
  | ok epId =>
    dsimp only
    obtain ⟨cap, hL, hA, hT⟩ := replyRecvReceiveEndpoint_resolved hEp0
    obtain ⟨_, -, -, hRt, -⟩ := syscallLookupCap_implies_capability_held gate st cap st hL
    exact (replyRecvAnsweringThen_eq_of_entryResolved hSid hInv
      (syscallResolveCap_of_lookup gate st cap st hL) hA hRt hT
      (replyRecvReceiveEndpoint_flow hEp0) hAns).symm

/-! ### The receive capability's verdicts after the reply

On an answering reply-receive, the receive capability's type and right are
checked on the state the reply step left.  Over a well-formed object store the
reply step keeps every CNode (`replyRecvReplyStep_cnodeSlotsKept`), so a
capability refused on entry is refused again after the reply, with the same
verdict: the dispatch is the reply step, then that refusal.  The two theorems
below are the answering counterparts of the dispatch's type-before-rights and
right-after-type orders. -/

/-- The composite reads the receive's endpoint only on a state that keeps the
entry's CNodes, so two readers that agree there give one composite. -/
theorem endpointReplyRecvAnsweringBodyThen_congr {answer : Option Architecture.FaultReplyOutcome}
    {recvEp recvEp' : SystemState → Except KernelError SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId}
    {msg : IpcMessage} {executingCore : Concurrency.CoreId} {recordedServer : SeLe4n.ThreadId}
    {req : Option (Capability × Array SeLe4n.CPtr)} {target : Option (TCB × Option CSpaceAddr)}
    {st : SystemState} (hInv : st.objects.invExt)
    (hEq : ∀ s, CNodeSlotsKept st s → recvEp s = recvEp' s) :
    endpointReplyRecvAnsweringBodyThen answer recvEp tid rid prevCaller msg executingCore
        recordedServer req target st =
      endpointReplyRecvAnsweringBodyThen answer recvEp' tid rid prevCaller msg executingCore
        recordedServer req target st := by
  unfold endpointReplyRecvAnsweringBodyThen
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
          rw [hEq _ (replyRecvReplyStep_cnodeSlotsKept hInv hL hP hX)]

theorem replyRecvTransferThen_congr
    {recvEp recvEp' : SystemState → Except KernelError SeLe4n.ObjId} {tid : SeLe4n.ThreadId}
    {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId} {label : Nat} {msg : IpcMessage}
    {grant : Bool} {executingCore : Concurrency.CoreId} {st : SystemState}
    (hInv : st.objects.invExt) (hEq : ∀ s, CNodeSlotsKept st s → recvEp s = recvEp' s) :
    replyRecvTransferThen recvEp tid rid prevCaller label msg grant executingCore st =
      replyRecvTransferThen recvEp' tid rid prevCaller label msg grant executingCore st := by
  unfold replyRecvTransferThen
  by_cases hAd : replyRecvPopAdmits st rid prevCaller = true
  · rw [if_pos hAd, if_pos hAd]
    exact endpointReplyRecvAnsweringBodyThen_congr hInv hEq
  · rw [if_neg hAd, if_neg hAd]

/-- **An answering reply-receive depends on its receive's reader only after the
reply**: two readers of the receive's endpoint that agree on every state
keeping the entry's CNodes give one dispatch. -/
theorem replyRecvAnsweringThen_congr {ctx : LabelingContext}
    {recvEp recvEp' : SystemState → Except KernelError SeLe4n.ObjId}
    {decoded : SyscallDecodeResult} {tid : SeLe4n.ThreadId} {executingCore : Concurrency.CoreId}
    {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId} {replyBadge : Option SeLe4n.Badge}
    {replyGrant : Bool} {st : SystemState} (hInv : st.objects.invExt)
    (hEq : ∀ s, CNodeSlotsKept st s → recvEp s = recvEp' s) :
    replyRecvAnsweringThen ctx recvEp decoded tid executingCore rid prevCaller replyBadge
        replyGrant st =
      replyRecvAnsweringThen ctx recvEp' decoded tid executingCore rid prevCaller replyBadge
        replyGrant st := by
  unfold replyRecvAnsweringThen
  dsimp only
  by_cases hSig : receiveCompletesSignal ctx st tid = true
  · rw [if_pos hSig, if_pos hSig]
    unfold replyRecvCompletesSignalArmThen
    cases hR : replyTransferOnCoreChecked ctx tid prevCaller
        (replyRecvReplyMessageInfo decoded.msgInfo.label
          { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo,
            badge := replyBadge })
        (extractMessageRegisters decoded.msgRegs decoded.msgInfo)
        { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo, badge := replyBadge }
        replyGrant executingCore st with
    | error e => rfl
    | ok p =>
      obtain ⟨⟨⟩, st1⟩ := p
      dsimp only
      rw [hEq _ (replyTransferOnCoreChecked_cnodeSlotsKept hInv hR)]
  · rw [if_neg hSig, if_neg hSig, replyRecvTransferThen_congr hInv hEq]

/-- **An answering reply-receive refuses a receive capability of the wrong type
after the reply, whatever rights it carries** (seL4's `handleRecv`, run after
`handleInvocation` on the reply capability): over a well-formed object store, a
receive capability that resolves on entry to a capability not of the receive's
type makes the dispatch the reply step, then `.invalidCapability 0`.  The reply
may rewrite an untyped capability's free index, never its target, and the type
verdict reads the target alone.  The answering counterpart of
`dispatchSyscallChecked_type_before_rights`; there is no `hasRight` hypothesis. -/
theorem dispatchReplyRecvAfterReply_type_after_reply {ctx : LabelingContext}
    {decoded : SyscallDecodeResult} {tid : SeLe4n.ThreadId} {executingCore : Concurrency.CoreId}
    {gate : SyscallGate} {st : SystemState} {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId}
    {replyBadge : Option SeLe4n.Badge} {replyGrant : Bool} {cap : Capability}
    (hSid : decoded.syscallId = .replyRecv) (hInv : st.objects.invExt)
    (hAns : replyRecvAnsweringReply? ctx gate decoded tid st =
      some (rid, prevCaller, replyBadge, replyGrant))
    (hR : syscallResolveCap gate st = .ok (cap, st))
    (hType : syscallTargetAccepted .replyRecv st cap = false) :
    dispatchReplyRecvAfterReply ctx decoded tid executingCore gate st =
      replyRecvAnsweringThen ctx (fun _ => .error (.invalidCapability 0)) decoded tid
        executingCore rid prevCaller replyBadge replyGrant st := by
  rw [dispatchReplyRecvAfterReply_eq_sel4Order hSid hInv hAns]
  apply replyRecvAnsweringThen_congr hInv
  intro s hK
  obtain ⟨c', hc', hT', -⟩ := syscallResolveCap_target_of_cnodeSlotsKept hK gate hR
  unfold replyRecvReceiveEndpoint
  rw [hc']
  dsimp only
  rw [syscallTargetAccepted_congr_target .replyRecv s hT',
    syscallTargetAccepted_of_cnodeSlotsKept hK, hType]
  rfl

/-- **An answering reply-receive refuses a receive capability without the
receive right after the reply, once its type is checked**: over a well-formed
object store, a receive capability of the receive's type that resolves on entry
without the gate's right makes the dispatch the reply step, then the receive's
missing-right answer.  The answering counterpart of
`dispatchSyscallChecked_right_after_type`. -/
theorem dispatchReplyRecvAfterReply_right_after_reply {ctx : LabelingContext}
    {decoded : SyscallDecodeResult} {tid : SeLe4n.ThreadId} {executingCore : Concurrency.CoreId}
    {gate : SyscallGate} {st : SystemState} {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId}
    {replyBadge : Option SeLe4n.Badge} {replyGrant : Bool} {cap : Capability}
    (hSid : decoded.syscallId = .replyRecv) (hInv : st.objects.invExt)
    (hAns : replyRecvAnsweringReply? ctx gate decoded tid st =
      some (rid, prevCaller, replyBadge, replyGrant))
    (hR : syscallResolveCap gate st = .ok (cap, st))
    (hType : syscallTargetAccepted .replyRecv st cap = true)
    (hRight : cap.hasRight gate.requiredRight = false) :
    dispatchReplyRecvAfterReply ctx decoded tid executingCore gate st =
      replyRecvAnsweringThen ctx (fun _ => .error (syscallMissingRightError .replyRecv)) decoded
        tid executingCore rid prevCaller replyBadge replyGrant st := by
  rw [dispatchReplyRecvAfterReply_eq_sel4Order hSid hInv hAns]
  apply replyRecvAnsweringThen_congr hInv
  intro s hK
  obtain ⟨hR', hA'⟩ := replyRecvReceiveCap_of_cnodeSlotsKept hK gate hR hType
  unfold replyRecvReceiveEndpoint
  rw [hR']
  dsimp only
  rw [hA', hRight]
  rfl

end SeLe4n.Kernel
