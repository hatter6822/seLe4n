-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RefusalCarryingEndpoint
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecvInPlace
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecvDonatedInPlace
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecvUnheldInPlace
import SeLe4n.Kernel.IPC.CrossCore.FaultAnswerInPlace
import SeLe4n.Kernel.IPC.CrossCore.LongReplyRecvInPlace
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvCapsDelivered
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvTakeInPlace
import SeLe4n.Kernel.IPC.CrossCore.LongReplyRecvPopInPlace
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvDonatedCallTakeInPlace
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvCallTakeInPlace

/-!
# Reply-receive, refusing in the state it was refused in

WS-ZA ZA4.7.  The checked reply-receive arm on a message read in registers,
proven equal to `RefusalCarrying.ofKernel` of the specification's dispatch
(`dispatchReplyRecvCheckedR_eq`).  The reply capability at MR0 is resolved in
continuation form, so no gate, slot reference or result cell is built for it;
a reply-receive that answers a caller blocked on this server and then blocks
on an endpoint no sender waits on writes in place
(`replyRecvOnCore_blocks_delivered`); any other takes the specification's
path.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open Architecture.RegisterDecode
open Architecture.SyscallArgDecode

/-- `resolveReplyRecvReply` on the message length and registers alone, with the
gate the caller's own CSpace gives (`resolveReplyRecvReplyR_eq`). -/
def resolveReplyRecvReplyR (st : SystemState) (tid : SeLe4n.ThreadId) (len : Nat)
    (regs : Array SeLe4n.RegValue) :
    Except KernelError (SeLe4n.ReplyId × SeLe4n.ThreadId × Option SeLe4n.Badge × Bool) :=
  if len == 0 then .error .replyCapInvalid else
  match Architecture.SyscallArgDecode.requireMsgReg regs 0 with
  | .error e => .error e
  | .ok r0 =>
      let gate : SyscallGate :=
        { callerId := tid
          cspaceRoot := callerCspaceRoot st tid
          capAddr := SeLe4n.CPtr.ofNat r0.val
          capDepth := callerCspaceDepth st tid
          requiredRight := .write }
      match syscallLookupArgumentCap replyRecvReplyCapNumber gate st with
      | .error e => .error e
      | .ok (rcap, _) =>
          match extractReplyId rcap with
          | .error e => .error (e.forArgumentCap replyRecvReplyCapNumber)
          | .ok rid =>
              match replyAnsweredCaller? st rid with
              | some prevCaller => .ok (rid, prevCaller, rcap.badge, rcap.rights.mem .grant)
              | none => .error .replyCapInvalid

theorem resolveReplyRecvReplyR_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (decoded : SyscallDecodeResult)
    (hCaller : gate.callerId = tid)
    (hRoot : gate.cspaceRoot = callerCspaceRoot st tid)
    (hDepth : gate.capDepth = callerCspaceDepth st tid) :
    resolveReplyRecvReplyR st tid decoded.msgInfo.length decoded.msgRegs =
      resolveReplyRecvReply gate decoded st := by
  unfold resolveReplyRecvReplyR resolveReplyRecvReply
  split
  · rfl
  · simp only [Architecture.SyscallArgDecode.decodeReplyRecvArgs, bind, Except.bind, pure,
      Except.pure]
    cases Architecture.SyscallArgDecode.requireMsgReg decoded.msgRegs 0 with
    | error e => rfl
    | ok r0 =>
      rcases gate with ⟨c, r, a, d, rr⟩
      simp only at hCaller hRoot hDepth
      subst hCaller hRoot hDepth
      rfl

/-- The checked reply-receive arm (`dispatchWithCapChecked`'s `.replyRecv`
case) through the specification's path, refusing in the state it was handed
(`endpointReplyRecvCheckedArmGeneralR_eq`). -/
def endpointReplyRecvCheckedArmGeneralR (ctx : LabelingContext) (mi : MessageInfo)
    (regs : Array SeLe4n.RegValue) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (cap : Capability) : RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object epId =>
      if !endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) then
        .error (.flowDenied, st)
      else
        match resolveReplyRecvReplyR st tid mi.length regs with
        | .error e => .error (e, st)
        | .ok (rid, prevCaller, replyBadge, replyGrant) =>
            let full := extractMessageRegisters regs mi
            let msg : IpcMessage :=
              { registers := full.extract 1 full.size, badge := replyBadge }
            if securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf prevCaller) then
              match replyRecvTransferOnCore epId tid rid prevCaller mi.label msg
                  replyGrant executingCore st with
              | .ok (summary, st') =>
                  .ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo)
              | .error e => .error (e, st)
            else .error (.replyCapInvalid, st)
    | _ => .error (.invalidCapability 0, st)

theorem endpointReplyRecvCheckedArmGeneralR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (st : SystemState)
    (hRR : decoded.syscallId = .replyRecv)
    (hCaller : gate.callerId = tid)
    (hRoot : gate.cspaceRoot = callerCspaceRoot st tid)
    (hDepth : gate.capDepth = callerCspaceDepth st tid) :
    endpointReplyRecvCheckedArmGeneralR ctx decoded.msgInfo decoded.msgRegs tid executingCore cap
        st =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap)
        st := by
  simp only [endpointReplyRecvCheckedArmGeneralR, RefusalCarrying.ofKernel,
    dispatchWithCapChecked, dispatchCapabilityOnly, hRR]
  cases cap.target with
  | object epId =>
    simp only []
    split
    · rfl
    · rw [resolveReplyRecvReplyR_eq st tid gate decoded hCaller hRoot hDepth]
      cases resolveReplyRecvReply gate decoded st with
      | error e => rfl
      | ok r =>
        obtain ⟨rid, prevCaller, replyBadge, replyGrant⟩ := r
        simp only [← hRoot]
        split
        · rcases replyRecvTransferOnCore epId tid rid prevCaller decoded.msgInfo.label _
            replyGrant executingCore st with _ | ⟨summary, st'⟩ <;> rfl
        · rfl
  | _ => rfl

/-- The reply capability a reply-receive names, checked as
`resolveReplyRecvReplyR` checks it once its slot is found: present, not the idle
thread's, carrying the write right, naming a reply object with an outstanding
caller.  The reply object, its caller and the capability's badge go to `onOk`,
a refusal to `onErr`, so no `Except` or tuple cell is built. -/
@[inline] def replyRecvCapK {α : Type} (st : SystemState) (cap? : Option Capability)
    (onErr : KernelError → α)
    (onOk : SeLe4n.ReplyId → SeLe4n.ThreadId → Option SeLe4n.Badge → Bool → α) : α :=
  match cap? with
  | none => onErr (.invalidCapability 0)
  | some cap =>
      if SeLe4n.Kernel.capTargetsReservedKernelObject cap then onErr (.invalidCapability 0)
      else if !cap.hasRight .write then onErr .illegalAuthority
      else
        match cap.target with
        | .replyCap rid =>
            match replyAnsweredCaller? st rid with
            | some c => onOk rid c cap.badge (cap.rights.mem .grant)
            | none => onErr .replyCapInvalid
        | _ => onErr (.invalidCapability 0)

/-- `resolveReplyRecvReplyR` in continuation form (`resolveReplyRecvK_eq`), on
the message length and the first message register: the slot is resolved
through `resolveCapAddressKUnrolled`, as the operand is.  WS-ZA ZA4.7. -/
@[inline] def resolveReplyRecvK {α : Type} (st : SystemState) (tid : SeLe4n.ThreadId)
    (len : Nat) (replyAddr : SeLe4n.CPtr) (onErr : KernelError → α)
    (onOk : SeLe4n.ReplyId → SeLe4n.ThreadId → Option SeLe4n.Badge → Bool → α) : α :=
  if len = 0 then onErr .replyCapInvalid else
  resolveCapAddressKUnrolled (callerCspaceRoot st tid) replyAddr
    (callerCspaceDepth st tid) st (KernelError.argumentCapRefusal replyRecvReplyCapNumber onErr)
    (fun cnode slot =>
      replyRecvCapK st (SystemState.lookupSlotCap st { cnode := cnode, slot := slot })
        (KernelError.argumentCapRefusal replyRecvReplyCapNumber onErr) onOk)

theorem resolveReplyRecvK_eq {α : Type} (st : SystemState) (tid : SeLe4n.ThreadId)
    (len : Nat) (replyAddr : SeLe4n.CPtr) (regs : Array SeLe4n.RegValue)
    (onErr : KernelError → α)
    (onOk : SeLe4n.ReplyId → SeLe4n.ThreadId → Option SeLe4n.Badge → Bool → α)
    (hReplyAddr : len ≠ 0 → regs[0]? = some ⟨replyAddr.word⟩) :
    resolveReplyRecvK st tid len replyAddr onErr onOk =
      match resolveReplyRecvReplyR st tid len regs with
      | .error e => onErr e
      | .ok (rid, c, b, g) => onOk rid c b g := by
  unfold resolveReplyRecvK resolveReplyRecvReplyR
  by_cases h0 : len = 0
  · simp [h0]
  · have hR : requireMsgReg regs 0 = .ok ⟨replyAddr.word⟩ := by
      have h := hReplyAddr h0
      rw [Array.getElem?_eq_some_iff] at h
      obtain ⟨hs, hv⟩ := h
      simp only [requireMsgReg, hs, ↓reduceDIte, hv]
    have hL : (len == 0) = false := by simp [h0]
    simp only [h0, ↓reduceIte, hL, Bool.false_eq_true, hR, syscallLookupArgumentCap, syscallLookupCap,
      syscallResolveCap, KernelError.argumentCapRefusal, SeLe4n.RegValue.val_mk,
      SeLe4n.CPtr.ofNat_word_toNat]
    rw [resolveCapAddressKUnrolled_eq, resolveCapAddressK_eq]
    cases resolveCapAddress (callerCspaceRoot st tid) replyAddr
        (callerCspaceDepth st tid) st with
    | error e => rfl
    | ok ref =>
      simp only [replyRecvCapK]
      cases SystemState.lookupSlotCap st ref with
      | none => rfl
      | some cap =>
        simp only []
        by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
        · simp only [hIdle, ↓reduceIte] <;> rfl
        · by_cases hRight : cap.hasRight .write = true
          · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true, Bool.not_true]
            unfold extractReplyId
            cases cap.target <;> try rfl
            rename_i rid
            simp only []
            cases replyAnsweredCaller? st rid <;> rfl
          · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true, Bool.not_false] <;> rfl

/-- WS-ZA ZA4.7: a reply-receive answers a caller blocked on this server and
then blocks, every write in its slot: the caller's reply leg may write in place
(`replyWakesInPlace`), no sender waits on the endpoint, the server may block
there in place and its reply object, consumed by the reply leg, is free, not
stashed and in its slot for the stasher record (`replyRecordsInPlace`).  Each
check reads the pre-state; `replyRecvBlocksFast_spec` carries
them to `replyRecvOnCore_blocks_delivered`. -/
@[inline] def replyRecvBlocksFast (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) : Bool :=
  tid.val != c.val &&
  (match st.getTcb? c with
   | some ct =>
       (match ct.ipcState with
        | .blockedOnReply _ (some server) => server.val == tid.val
        | _ => false) &&
       ct.replyObjectCode == rid.val + 1 &&
       replyWakesInPlace st c ct rid
   | none => false) &&
  (match st.getEndpoint? epId with
   | some ep =>
       ep.sendQ.head.isNone &&
       (match st.getTcb? tid with
        | some rt => receiveBlockAdmits rt && enqueuesInPlaceCode st epId tid ep.recvTailCode
        | none => false)
   | none => false) &&
  (match st.getReply? rid with
   | some rp => rp.consumedIsFree && !st.replyStashedAt rid rp &&
       replyRecordsInPlace st (rid.val + 1)
   | none => false)

theorem replyRecvBlocksFast_spec {st : SystemState} {epId : SeLe4n.ObjId}
    {tid c : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    (h : replyRecvBlocksFast st epId tid c rid = true) :
    ∃ (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply),
      st.objects[c.toObjId]? = some (.tcb ct) ∧
      ct.ipcState = .blockedOnReply ep0 (some tid) ∧ ct.replyObject = some rid ∧
      replyWakesInPlace st c ct rid = true ∧ tid ≠ c ∧
      st.objects[epId]? = some (.endpoint ep) ∧ ep.sendQ.head = none ∧
      st.objects[tid.toObjId]? = some (.tcb rt) ∧ receiveBlockAdmits rt = true ∧
      enqueuesInPlace st epId tid ep.receiveQ.tail = true ∧
      st.objects[rid.toObjId]? = some (.reply rp) ∧ rp.consumed.isFree = true ∧
      st.replyStashedAt rid rp = false ∧ replyRecordsInPlace st (rid.val + 1) = true ∧
      receiveQueueTailCode st epId = ep.recvTailCode := by
  unfold replyRecvBlocksFast at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hNe, hC⟩, hE⟩, hRp⟩ := h
  have hNe' : tid ≠ c := fun e => by subst e; simp at hNe
  cases hTc : st.getTcb? c with
  | none => rw [hTc] at hC; cases hC
  | some ct =>
  rw [hTc] at hC
  simp only [Bool.and_eq_true] at hC
  obtain ⟨⟨hIpc, hRO⟩, hW⟩ := hC
  obtain ⟨ep0, hIpc'⟩ : ∃ ep0, ct.ipcState = .blockedOnReply ep0 (some tid) := by
    revert hIpc
    split
    · next ep0 server hS =>
      intro e
      have : server = tid := by
        cases server; cases tid; simp only [beq_iff_eq] at e; subst e; rfl
      subst this
      exact ⟨ep0, hS⟩
    · intro e; cases e
  cases hEp : st.getEndpoint? epId with
  | none => rw [hEp] at hE; cases hE
  | some ep =>
  rw [hEp] at hE
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hE
  obtain ⟨hS, hT⟩ := hE
  cases hTt : st.getTcb? tid with
  | none => rw [hTt] at hT; cases hT
  | some rt =>
  rw [hTt] at hT
  simp only [Bool.and_eq_true] at hT
  obtain ⟨hA, hEnq⟩ := hT
  cases hR : st.getReply? rid with
  | none => rw [hR] at hRp; cases hRp
  | some rp =>
  rw [hR] at hRp
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hRp
  obtain ⟨⟨hFree, hStash⟩, hRecR⟩ := hRp
  refine ⟨ct, ep0, rt, ep, rp, (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc, hIpc', ?_, hW,
    hNe', (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp, hS,
    (SystemState.getTcb?_eq_some_iff _ _ _).mp hTt, hA, ?_,
    (SystemState.getReply?_eq_some_iff _ _ _).mp hR, (Reply.consumedIsFree_eq rp).symm.trans hFree,
    hStash, hRecR, ?_⟩
  · simp only [TCB.replyObject, beq_iff_eq.mp hRO, SeLe4n.ReplyId.ofOptCode]
  · rw [enqueuesInPlaceCode_eq, Endpoint.ofOptCode_recvTailCode] at hEnq; exact hEnq
  · simp only [receiveQueueTailCode, hEp]

/-- **The reply-receive's reply leg transfers no capability, decided in place**:
the reply capability lacks the grant right, or the replier `tid`'s frame names
no extra capability, or the answered caller `c` has no IPC buffer the kernel may
write or names no receive slot there (`replyTransferInertW`); a caller with no
TCB takes none.  Every in-place form of the arm answering an unfaulted caller is
taken only then, because none of them runs seL4's `doReplyTransfer` capability
transfer (`replyRecvReplyInertW_spec`, then `replyRecvReplyTransfer_of_inert`).
A word-only reply (no extra capability) passes on the count alone, whatever
receive path the caller configured. -/
@[inline] def replyRecvReplyInertW (st : SystemState) (tid c : SeLe4n.ThreadId) (grant : Bool) :
    Bool :=
  match st.getTcb? c with
  | some ct => replyTransferInertW st tid ct grant
  | none => true

theorem replyRecvReplyInertW_spec {st : SystemState} {tid c : SeLe4n.ThreadId} {grant : Bool}
    {ct : TCB} (h : replyRecvReplyInertW st tid c grant = true)
    (hT : st.objects[c.toObjId]? = some (.tcb ct)) :
    replyTransferInert st tid ct grant = true := by
  unfold replyRecvReplyInertW at h
  rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hT] at h
  exact replyTransferInert_of_W h

/-- The checked reply-receive once its reply capability is resolved, through the
specification's path (`replyRecvTransferOnCore`, which answers a faulted caller
with its fault reply).  Out of line, so the reply's message record is built only
here. -/
@[noinline] def replyRecvRendezvousR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    match replyRecvTransferOnCore epId tid rid c label
        { registers := Architecture.regReplyRecvBody layout rf len, badge := badge }
        grant executingCore st with
    | .ok (summary, st') =>
        .ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo)
    | .error e => .error (e, st)

/-- WS-ZA ZA6.34: **a reply-receive answering a caller recording no server that
may block in place**, read on the pre-state: the caller `c` blocked on reply
object `rid` with no server recorded (its server finalised, seL4-MCS's
`finaliseCap`), the unheld pop's checks (`replyUnheldPopsInPlace`), no sender
waiting on the endpoint, the replier a thread that may block there in place and
the reply object not stashed and in its slot for the stasher record.  Every
read is a code. -/
@[inline] def replyRecvUnheldBlocks (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) : Bool :=
  tid.val != c.val &&
  (match st.getTcb? c with
   | some ct =>
       (match ct.ipcState with
        | .blockedOnReply _ none => true
        | _ => false) &&
       ct.replyObjectCode == rid.val + 1
   | none => false) &&
  replyUnheldPopsInPlace st c rid &&
  (match st.getEndpoint? epId with
   | some ep =>
       ep.sendQ.head.isNone &&
       (match st.getTcb? tid with
        | some rt => receiveBlockAdmits rt && enqueuesInPlaceCode st epId tid ep.recvTailCode
        | none => false)
   | none => false) &&
  (match st.getReply? rid with
   | some rp => !st.replyStashedAt rid rp && replyRecordsInPlace st (rid.val + 1)
   | none => false)

theorem replyRecvUnheldBlocks_spec {st : SystemState} {epId : SeLe4n.ObjId}
    {tid c : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    (h : replyRecvUnheldBlocks st epId tid c rid = true) :
    ∃ (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply),
      st.objects[c.toObjId]? = some (.tcb ct) ∧
      ct.ipcState = .blockedOnReply ep0 none ∧ ct.replyObject = some rid ∧
      replyUnheldPopsInPlace st c rid = true ∧ tid ≠ c ∧
      st.objects[epId]? = some (.endpoint ep) ∧ ep.sendQ.head = none ∧
      st.objects[tid.toObjId]? = some (.tcb rt) ∧ receiveBlockAdmits rt = true ∧
      enqueuesInPlace st epId tid ep.receiveQ.tail = true ∧
      st.objects[rid.toObjId]? = some (.reply rp) ∧
      st.replyStashedAt rid rp = false ∧ replyRecordsInPlace st (rid.val + 1) = true ∧
      receiveQueueTailCode st epId = ep.recvTailCode := by
  unfold replyRecvUnheldBlocks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hNe, hC⟩, hU⟩, hE⟩, hRp⟩ := h
  have hNe' : tid ≠ c := fun e => by subst e; simp at hNe
  cases hTc : st.getTcb? c with
  | none => rw [hTc] at hC; cases hC
  | some ct =>
  rw [hTc] at hC
  simp only [Bool.and_eq_true] at hC
  obtain ⟨hIpc, hRO⟩ := hC
  obtain ⟨ep0, hIpc'⟩ : ∃ ep0, ct.ipcState = .blockedOnReply ep0 none := by
    revert hIpc
    split
    · next ep0 hS => intro _; exact ⟨ep0, hS⟩
    · intro e; cases e
  cases hEp : st.getEndpoint? epId with
  | none => rw [hEp] at hE; cases hE
  | some ep =>
  rw [hEp] at hE
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hE
  obtain ⟨hS, hT⟩ := hE
  cases hTt : st.getTcb? tid with
  | none => rw [hTt] at hT; cases hT
  | some rt =>
  rw [hTt] at hT
  simp only [Bool.and_eq_true] at hT
  obtain ⟨hA, hEnq⟩ := hT
  cases hR : st.getReply? rid with
  | none => rw [hR] at hRp; cases hRp
  | some rp =>
  rw [hR] at hRp
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hRp
  obtain ⟨hStash, hRecR⟩ := hRp
  refine ⟨ct, ep0, rt, ep, rp, (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc, hIpc', ?_, hU,
    hNe', (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp, hS,
    (SystemState.getTcb?_eq_some_iff _ _ _).mp hTt, hA, ?_,
    (SystemState.getReply?_eq_some_iff _ _ _).mp hR, hStash, hRecR, ?_⟩
  · simp only [TCB.replyObject, beq_iff_eq.mp hRO, SeLe4n.ReplyId.ofOptCode]
  · rw [enqueuesInPlaceCode_eq, Endpoint.ofOptCode_recvTailCode] at hEnq; exact hEnq
  · simp only [receiveQueueTailCode, hEp]

/-- **The checked reply-receive whose reply leg transfers capabilities**, its
caller unfaulted: from a replier whose frame routes as a reply-receive, under
the grant right, a reply of at most four words: the reply's writes, the
transfer in place (seL4's `doReplyTransfer`; every CNode it writes keeps its
kind), then the receive leg (seL4's `receiveIPC`) on each shape that blocks in place: the plain one
(`performReplyRecvBlockCapsDelivered`), the donated one
(`performReplyRecvDonatedCapsDelivered`) and the one answering a caller
recording no server (`performReplyRecvUnheldCapsDelivered`).  The replier and
the caller enter as the words the transfer reads of them, read before any
write.  Any other takes the specification's path (`replyRecvCapsArmR_eq`). -/
@[inline] def replyRecvCapsArmR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    match st.getTcb? tid with
    | some stcb =>
        match Architecture.RegisterDecode.registerRoutedSyscallOf SeLe4n.arm64DefaultLayout
            stcb.registerContext with
        | .replyRecv _ _ =>
            match st.getTcb? c with
            | some ct =>
                if grant && decide (Architecture.regMessageLength layout len - 1 ≤ 4) then
                  if replyRecvBlocksFast st epId tid c rid then
                    .ok ((), performReplyRecvBlockCapsDelivered st c tid rid epId
                      (receiveQueueTailCode st epId) layout rf len badge executingCore
                      stcb.vspaceRoot stcb.ipcBuffer stcb.cspaceRoot
                      (routedExtraCaps stcb.registerContext) ct.vspaceRoot ct.ipcBuffer
                      ct.cspaceRoot)
                  else if replyRecvDonatedBlocks st epId tid c rid then
                    .ok ((), performReplyRecvDonatedCapsDelivered st c tid rid
                      ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) epId
                      (receiveQueueTailCode st epId) layout rf len badge executingCore
                      stcb.vspaceRoot stcb.ipcBuffer stcb.cspaceRoot
                      (routedExtraCaps stcb.registerContext) ct.vspaceRoot ct.ipcBuffer
                      ct.cspaceRoot)
                  else if replyRecvUnheldBlocks st epId tid c rid then
                    .ok ((), performReplyRecvUnheldCapsDelivered st c tid rid
                      ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) epId
                      (receiveQueueTailCode st epId) layout rf len badge executingCore
                      stcb.vspaceRoot stcb.ipcBuffer stcb.cspaceRoot
                      (routedExtraCaps stcb.registerContext) ct.vspaceRoot ct.ipcBuffer
                      ct.cspaceRoot)
                  else replyRecvRendezvousR epId tid c rid badge grant layout rf len label
                    executingCore st
                else replyRecvRendezvousR epId tid c rid badge grant layout rf len label
                  executingCore st
            | none => replyRecvRendezvousR epId tid c rid badge grant layout rf len label
                executingCore st
        | _ => replyRecvRendezvousR epId tid c rid badge grant layout rf len label executingCore st
    | none => replyRecvRendezvousR epId tid c rid badge grant layout rf len label executingCore st

/-- On an unfaulted caller the capability-transferring arm is the
specification's path. -/
theorem replyRecvCapsArmR_eq (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (hNoF : threadHasPendingFault st c = false) :
    replyRecvCapsArmR epId tid c rid badge grant layout rf len label executingCore st =
      replyRecvRendezvousR epId tid c rid badge grant layout rf len label executingCore st := by
  unfold replyRecvCapsArmR
  split
  · next stcb hS =>
    split
    · next capAddr mi hR =>
      split
      · next ct0 hTc0 =>
        have hTc0' := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc0
        split
        · next hG =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hG
          obtain ⟨hGr, hSz⟩ := hG
          subst hGr
          have hReq := replyCapRequest_of_routedReplyRecv st tid stcb capAddr mi hS hR
          unfold replyRecvRendezvousR
          rw [replyRecvTransferOnCore_of_no_fault (h := hNoF)]
          split
          · next hF =>
            obtain ⟨ct, ep0, rt, ep, rp, hT, hIpc, hRO, hWk, hNe, hE, hS', hR', hA, hEnq, hRp,
              hFree, hStash, hRecR, hTail⟩ := replyRecvBlocksFast_spec hF
            obtain rfl : ct = ct0 := by rw [hT] at hTc0'; cases hTc0'; rfl
            rw [hTail]
            have h := replyRecvOnCore_blocks_capsDelivered st epId tid c rid layout rf len badge executingCore ct ep0 rt ep rp stcb _ hSz hT hIpc hRO hWk hNe hE hS' hR' hA hEnq hRp hFree hStash hRecR hReq
            generalize endpointReplyRecvOnCore epId tid rid c
              { registers := Architecture.regReplyRecvBody layout rf len, badge := badge } true
              executingCore st = r at h ⊢
            rcases r with e | ⟨a, st'⟩
            · cases h
            · simp only [Except.ok.injEq] at h ⊢
              exact h.symm
          · split
            · next hF =>
              obtain ⟨ct, ep0, rt, ep, rp, hT, hIpc, hRO, hP, hSRes, hE, hS', hR', hA, hEnq, hRp,
                hStash, hRecR⟩ := replyRecvDonatedBlocks_spec hF
              obtain rfl : ct = ct0 := by rw [hT] at hTc0'; cases hTc0'; rfl
              have hTail : receiveQueueTailCode st epId = ep.recvTailCode := by
                simp only [receiveQueueTailCode, (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE]
              rw [hTail]
              have h := replyRecvOnCore_donated_capsDelivered st epId tid c rid layout rf len badge executingCore ct ep0 rt ep rp stcb _ hSz hT hIpc hRO hSRes hP hE hS' hR' hA hEnq hRp hStash hRecR hReq
              generalize endpointReplyRecvOnCore epId tid rid c
                { registers := Architecture.regReplyRecvBody layout rf len, badge := badge } true
                executingCore st = r at h ⊢
              rcases r with e | ⟨a, st'⟩
              · cases h
              · simp only [Except.ok.injEq] at h ⊢
                exact h.symm
            · split
              · next hF =>
                obtain ⟨ct, ep0, rt, ep, rp, hT, hIpc, hRO, hU, hNe, hE, hS', hR', hA, hEnq, hRp,
                  hStash, hRecR, hTail⟩ := replyRecvUnheldBlocks_spec hF
                obtain rfl : ct = ct0 := by rw [hT] at hTc0'; cases hTc0'; rfl
                rw [hTail]
                have h := replyRecvOnCore_unheld_capsDelivered st epId tid c rid layout rf len badge executingCore ct ep0 rt ep rp stcb _ hSz hT hIpc hRO hU hNe hE hS' hR' hA hEnq hRp hStash hRecR hReq
                generalize endpointReplyRecvOnCore epId tid rid c
                  { registers := Architecture.regReplyRecvBody layout rf len, badge := badge } true
                  executingCore st = r at h ⊢
                rcases r with e | ⟨a, st'⟩
                · cases h
                · simp only [Except.ok.injEq] at h ⊢
                  exact h.symm
              · rfl
        · rfl
      · rfl
    · rfl
  · rfl

/-- **The installing reply-receive does not reach the general path when its
checks pass**: on a replier whose frame routes as a reply-receive under the
default layout, with the grant right, a reply of at most four words and the
transfer's stores in place -- every check read on the pre-state, before any
write -- a receive leg that blocks in place runs the plain performer.  The
general path (`replyRecvRendezvousR`) is reached only when one of those checks
fails, on the state the arm was handed. -/
theorem replyRecvCapsArmR_blocks_inPlace (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) (st : SystemState) (stcb ct : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hS : st.getTcb? tid = some stcb)
    (hR : Architecture.RegisterDecode.registerRoutedSyscallOf SeLe4n.arm64DefaultLayout
      stcb.registerContext = .replyRecv capAddr mi)
    (hC : st.getTcb? c = some ct)
    (hAdm : (grant && decide (Architecture.regMessageLength layout len - 1 ≤ 4)) = true)
    (hB : replyRecvBlocksFast st epId tid c rid = true) :
    replyRecvCapsArmR epId tid c rid badge grant layout rf len label executingCore st =
      .ok ((), performReplyRecvBlockCapsDelivered st c tid rid epId
        (receiveQueueTailCode st epId) layout rf len badge executingCore stcb.vspaceRoot stcb.ipcBuffer stcb.cspaceRoot
        (routedExtraCaps stcb.registerContext) ct.vspaceRoot ct.ipcBuffer ct.cspaceRoot) := by
  unfold replyRecvCapsArmR
  simp only [hS, hR, hC, hAdm, hB, if_true]

/-- The same for the donated shape (`replyRecvDonatedBlocks`), when the plain
one does not hold. -/
theorem replyRecvCapsArmR_donated_inPlace (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) (st : SystemState) (stcb ct : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hS : st.getTcb? tid = some stcb)
    (hR : Architecture.RegisterDecode.registerRoutedSyscallOf SeLe4n.arm64DefaultLayout
      stcb.registerContext = .replyRecv capAddr mi)
    (hC : st.getTcb? c = some ct)
    (hAdm : (grant && decide (Architecture.regMessageLength layout len - 1 ≤ 4)) = true)
    (hB : replyRecvBlocksFast st epId tid c rid = false)
    (hD : replyRecvDonatedBlocks st epId tid c rid = true) :
    replyRecvCapsArmR epId tid c rid badge grant layout rf len label executingCore st =
      .ok ((), performReplyRecvDonatedCapsDelivered st c tid rid
        ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) epId
        (receiveQueueTailCode st epId) layout rf len badge executingCore stcb.vspaceRoot stcb.ipcBuffer stcb.cspaceRoot
        (routedExtraCaps stcb.registerContext) ct.vspaceRoot ct.ipcBuffer ct.cspaceRoot) := by
  unfold replyRecvCapsArmR
  simp only [hS, hR, hC, hAdm, hB, hD, if_true, Bool.false_eq_true, if_false]

/-- The same for the shape answering a caller recording no server
(`replyRecvUnheldBlocks`), when neither other shape holds. -/
theorem replyRecvCapsArmR_unheld_inPlace (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) (st : SystemState) (stcb ct : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hS : st.getTcb? tid = some stcb)
    (hR : Architecture.RegisterDecode.registerRoutedSyscallOf SeLe4n.arm64DefaultLayout
      stcb.registerContext = .replyRecv capAddr mi)
    (hC : st.getTcb? c = some ct)
    (hAdm : (grant && decide (Architecture.regMessageLength layout len - 1 ≤ 4)) = true)
    (hB : replyRecvBlocksFast st epId tid c rid = false)
    (hD : replyRecvDonatedBlocks st epId tid c rid = false)
    (hU : replyRecvUnheldBlocks st epId tid c rid = true) :
    replyRecvCapsArmR epId tid c rid badge grant layout rf len label executingCore st =
      .ok ((), performReplyRecvUnheldCapsDelivered st c tid rid
        ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) epId
        (receiveQueueTailCode st epId) layout rf len badge executingCore stcb.vspaceRoot stcb.ipcBuffer stcb.cspaceRoot
        (routedExtraCaps stcb.registerContext) ct.vspaceRoot ct.ipcBuffer ct.cspaceRoot) := by
  unfold replyRecvCapsArmR
  simp only [hS, hR, hC, hAdm, hB, hD, hU, if_true, Bool.false_eq_true, if_false]

/-- **A reply-receive answering a caller blocked on this server whose receive
leg takes a waiting sender**, every write in its slot: the caller's reply leg
may write in place (`replyWakesInPlace`), the reply object is there, and the
sender at the head of the endpoint's send queue is not the caller, delivers no
fault and may be taken in place (`receiveTakesInPlace`).  Each check reads the
pre-state; `replyRecvTakes_spec` carries them to
`replyRecvOnCore_take_delivered` and `replyRecvOnCore_take_capsDelivered`. -/
@[inline] def replyRecvTakes (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) : Bool :=
  tid.val != c.val &&
  (match st.getTcb? c with
   | some ct =>
       (match ct.ipcState with
        | .blockedOnReply _ (some server) => server.val == tid.val
        | _ => false) &&
       ct.replyObjectCode == rid.val + 1 &&
       replyWakesInPlace st c ct rid
   | none => false) &&
  (match st.getEndpoint? epId with
   | some ep =>
       (match ep.sendQ.head with
        | some s =>
            s.val != c.val &&
            (match st.getTcb? s with
             | some sTcb => !sTcb.ipcFaultSend && receiveTakesInPlace st epId tid s sTcb
             | none => false)
        | none => false)
   | none => false) &&
  (match st.getReply? rid with
   | some _ => true
   | none => false)

theorem replyRecvTakes_spec {st : SystemState} {epId : SeLe4n.ObjId}
    {tid c : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    (h : replyRecvTakes st epId tid c rid = true) :
    ∃ (ct : TCB) (ep0 : SeLe4n.ObjId) (rp : Reply) (ep : Endpoint) (s : SeLe4n.ThreadId)
      (sTcb : TCB),
      st.objects[c.toObjId]? = some (.tcb ct) ∧
      ct.ipcState = .blockedOnReply ep0 (some tid) ∧ ct.replyObject = some rid ∧
      replyWakesInPlace st c ct rid = true ∧ tid ≠ c ∧
      st.objects[rid.toObjId]? = some (.reply rp) ∧
      st.getEndpoint? epId = some ep ∧ ep.sendQ.head = some s ∧
      st.getTcb? s = some sTcb ∧ s ≠ c ∧ sTcb.ipcFaultSend = false ∧
      receiveTakesInPlace st epId tid s sTcb = true := by
  unfold replyRecvTakes at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hNe, hC⟩, hE⟩, hRp⟩ := h
  have hNe' : tid ≠ c := fun e => by subst e; simp at hNe
  cases hTc : st.getTcb? c with
  | none => rw [hTc] at hC; cases hC
  | some ct =>
  rw [hTc] at hC
  simp only [Bool.and_eq_true] at hC
  obtain ⟨⟨hIpc, hRO⟩, hW⟩ := hC
  obtain ⟨ep0, hIpc'⟩ : ∃ ep0, ct.ipcState = .blockedOnReply ep0 (some tid) := by
    revert hIpc
    split
    · next ep0 server hS =>
      intro e
      have : server = tid := by
        cases server; cases tid; simp only [beq_iff_eq] at e; subst e; rfl
      subst this
      exact ⟨ep0, hS⟩
    · intro e; cases e
  cases hEp : st.getEndpoint? epId with
  | none => rw [hEp] at hE; cases hE
  | some ep =>
  rw [hEp] at hE
  dsimp only at hE
  cases hH : ep.sendQ.head with
  | none => rw [hH] at hE; cases hE
  | some s =>
  rw [hH] at hE
  simp only [Bool.and_eq_true] at hE
  obtain ⟨hSC, hT⟩ := hE
  have hSC' : s ≠ c := fun e => by subst e; simp at hSC
  cases hTs : st.getTcb? s with
  | none => rw [hTs] at hT; cases hT
  | some sTcb =>
  rw [hTs] at hT
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hT
  obtain ⟨hF, hG⟩ := hT
  cases hR : st.getReply? rid with
  | none => rw [hR] at hRp; cases hRp
  | some rp =>
  refine ⟨ct, ep0, rp, ep, s, sTcb, (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc, hIpc', ?_, hW,
    hNe', (SystemState.getReply?_eq_some_iff _ _ _).mp hR, rfl, hH, hTs, hSC', hF, hG⟩
  simp only [TCB.replyObject, beq_iff_eq.mp hRO, SeLe4n.ReplyId.ofOptCode]

/-- Whether the thread at the head of the endpoint's send queue blocked with a
routed capability-free call, read from its saved registers. -/
@[inline] def replyRecvQueuedCallRoutes (st : SystemState) (epId : SeLe4n.ObjId) : Bool :=
  match st.getEndpoint? epId with
  | some ep =>
    match ep.sendQ.head with
    | some s =>
      match st.getTcb? s with
      | some sTcb =>
        match Architecture.RegisterDecode.registerRoutedSyscallOf SeLe4n.arm64DefaultLayout
            sTcb.registerContext with
        | .call _ _ => true
        | _ => false
      | none => false
    | none => false
  | none => false

/-- Whether a reply-receive of at most four words, its reply leg transferring no
capability (`replyRecvReplyInertW`), takes in place a caller queued by a routed
capability-free call and is donated that caller's context
(`replyRecvCallTakes`).  Out of line, so the checks are one call and nothing
they read is held across the writes. -/
@[noinline] def replyRecvCallTakeAdmits (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (grant : Bool) (layout : SeLe4n.SyscallRegisterLayout) (len : Nat)
    (st : SystemState) : Bool :=
  decide (Architecture.regMessageLength layout len - 1 ≤ 4) &&
    replyRecvCallTakes st epId tid c rid && replyRecvQueuedCallRoutes st epId &&
    replyRecvReplyInertW st tid c grant

/-- **The checked reply-receive whose receive leg takes a donating caller**
(seL4-MCS's `handleReplyRecv` on a passive server answering a caller that did
not donate: `doReplyTransfer`, then `receiveIPC` taking a caller queued by a
`Call` and `reply_push (canDonate)` handing that caller's context to the
server): in place when `replyRecvCallTakeAdmits` passes
(`performReplyRecvCallTakeDelivered`, `replyRecvOnCore_callTake_delivered`),
every context, core and word it takes read on the pre-state;
`replyRecvCapsArmR` otherwise.  An admitted shape whose reads then disagree,
which `replyRecvCallTakeAdmits` rules out, takes the specification's path, so
the next arm is reached from one site and is inlined once. -/
@[inline] def replyRecvCallTakeArmR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    if replyRecvCallTakeAdmits epId tid c rid grant layout len st then
      match st.getEndpoint? epId with
      | some ep =>
        match ep.sendQ.head with
        | some s =>
          match st.getTcb? s with
          | some sTcb =>
            match Architecture.RegisterDecode.registerRoutedSyscallOf SeLe4n.arm64DefaultLayout
                sTcb.registerContext with
            | .call _ mi =>
              .ok ((), performReplyRecvCallTakeDelivered st c tid rid epId s sTcb.queueNextCode
                ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s) (determineTargetCore st tid)
                executingCore layout rf len badge sTcb.registerContext mi.length
                (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged)
            | _ =>
                replyRecvRendezvousR epId tid c rid badge grant layout rf len label executingCore st
          | none =>
              replyRecvRendezvousR epId tid c rid badge grant layout rf len label executingCore st
        | none =>
            replyRecvRendezvousR epId tid c rid badge grant layout rf len label executingCore st
      | none =>
          replyRecvRendezvousR epId tid c rid badge grant layout rf len label executingCore st
    else replyRecvCapsArmR epId tid c rid badge grant layout rf len label executingCore st

theorem replyRecvCallTakeArmR_of_not_admits (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (hA : replyRecvCallTakeAdmits epId tid c rid grant layout len st = false) :
    replyRecvCallTakeArmR epId tid c rid badge grant layout rf len label executingCore st =
      replyRecvCapsArmR epId tid c rid badge grant layout rf len label executingCore st := by
  unfold replyRecvCallTakeArmR
  simp only [hA, Bool.false_eq_true, ↓reduceIte]

/-- On an unfaulted caller, once admitted, the arm is the specification's path. -/
theorem replyRecvCallTakeArmR_of_admits (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (hNoF : threadHasPendingFault st c = false)
    (hA : replyRecvCallTakeAdmits epId tid c rid grant layout len st = true) :
    replyRecvCallTakeArmR epId tid c rid badge grant layout rf len label executingCore st =
      replyRecvRendezvousR epId tid c rid badge grant layout rf len label executingCore st := by
  have hA' := hA
  unfold replyRecvCallTakeAdmits at hA'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hA'
  obtain ⟨⟨⟨hSz4, hTk⟩, hRoute⟩, hI⟩ := hA'
  obtain ⟨ct, ep0, rp, ep, s, sTcb, hT, hIpc, hRO, hW, hNe, hRp, hEp, hH, hTs, hSC, hF, hGt⟩ :=
    replyRecvCallTakes_spec hTk
  have hE := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp
  have hS := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTs
  unfold replyRecvQueuedCallRoutes at hRoute
  simp only [hEp, hH, hTs] at hRoute
  unfold replyRecvCallTakeArmR
  simp only [hA, ↓reduceIte, hEp, hH, hTs]
  split
  · next capAddr mi hR =>
    have h := replyRecvOnCore_callTake_delivered st epId tid c rid layout rf len badge grant
      executingCore ct ep0 rp ep s sTcb capAddr mi hSz4 hT hIpc hRO hW hNe hRp
      (replyRecvReplyInertW_spec hI hT) hE hH hS hSC hF hGt
      ((Architecture.RegisterDecode.registerRoutedSyscall_default _).trans hR)
    unfold replyRecvRendezvousR
    rw [replyRecvTransferOnCore_of_no_fault (h := hNoF)]
    generalize endpointReplyRecvOnCore epId tid rid c
      { registers := Architecture.regReplyRecvBody layout rf len, badge := badge } grant
      executingCore st = r at h ⊢
    rcases r with e | ⟨a, st'⟩
    · cases h
    · simp only [Except.ok.injEq] at h ⊢
      exact h.symm
  · next hNot =>
    exfalso
    split at hRoute
    · next capAddr mi hR => exact hNot capAddr mi hR
    · cases hRoute

/-- On an unfaulted caller the call-take arm is the specification's path. -/
theorem replyRecvCallTakeArmR_eq (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (hNoF : threadHasPendingFault st c = false) :
    replyRecvCallTakeArmR epId tid c rid badge grant layout rf len label executingCore st =
      replyRecvRendezvousR epId tid c rid badge grant layout rf len label executingCore st := by
  cases hA : replyRecvCallTakeAdmits epId tid c rid grant layout len st
  · rw [replyRecvCallTakeArmR_of_not_admits _ _ _ _ _ _ _ _ _ _ _ _ hA]
    exact replyRecvCapsArmR_eq epId tid c rid badge grant layout rf len label executingCore st hNoF
  · exact replyRecvCallTakeArmR_of_admits _ _ _ _ _ _ _ _ _ _ _ _ hNoF hA

/-- Whether a reply-receive of at most four words answering a caller blocked on
this server takes a waiting sender in place (`replyRecvTakes`).  Out of line, so
the checks are one call and nothing they read is held across the writes. -/
@[noinline] def replyRecvTakeAdmits (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (layout : SeLe4n.SyscallRegisterLayout) (len : Nat)
    (st : SystemState) : Bool :=
  decide (Architecture.regMessageLength layout len - 1 ≤ 4) && replyRecvTakes st epId tid c rid

/-- **The checked reply-receive whose receive leg takes a waiting sender**
(seL4-MCS's `handleReplyRecv`: `doReplyTransfer`, then `receiveIPC` meeting a
sender already queued -- the ordinary server loop under load): when
`replyRecvTakeAdmits` passes and the sender's saved frame routes as a
capability-free send, the reply's writes, the reply leg's transfer, the take and
the three frames, the sender's six words read from its saved registers before
any write.  A reply leg transferring no capability (`replyRecvReplyInertW`)
runs `performReplyRecvTakeDelivered`; a granting one whose frame routes as a
reply-receive, its transfer's stores in place, runs
`performReplyRecvTakeCapsDelivered`.  When the receive leg instead takes a
caller queued by a `Call` and is donated its context, the call-take arm
(`replyRecvCallTakeArmR`).  Any other takes the specification's path
(`replyRecvTakeArmR_eq`). -/
@[inline] def replyRecvTakeArmR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    if replyRecvTakeAdmits epId tid c rid layout len st then
      match st.getEndpoint? epId with
      | some ep =>
        match ep.sendQ.head with
        | some s =>
          match st.getTcb? s with
          | some sTcb =>
            match Architecture.RegisterDecode.registerRoutedSyscallOf SeLe4n.arm64DefaultLayout
                sTcb.registerContext with
            | .send _ mi =>
              if replyRecvReplyInertW st tid c grant then
                let f := Architecture.regMessageFrameW SeLe4n.arm64DefaultLayout
                  sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged
                .ok ((), performReplyRecvTakeDelivered st c tid rid epId s sTcb.queueNextCode
                  executingCore layout rf len badge f.x0 f.x1 f.x2 f.x3 f.x4 f.x5)
              else
                match st.getTcb? tid with
                | some stcb =>
                  match Architecture.RegisterDecode.registerRoutedSyscallOf
                      SeLe4n.arm64DefaultLayout stcb.registerContext with
                  | .replyRecv _ _ =>
                    match st.getTcb? c with
                    | some ct =>
                      if grant then
                        let f := Architecture.regMessageFrameW SeLe4n.arm64DefaultLayout
                          sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge)
                          sTcb.ipcBadged
                        .ok ((), performReplyRecvTakeCapsDelivered st c tid rid epId s
                          sTcb.queueNextCode executingCore layout rf len badge
                          f.x0 f.x1 f.x2 f.x3 f.x4 f.x5 stcb.vspaceRoot stcb.ipcBuffer
                          stcb.cspaceRoot (routedExtraCaps stcb.registerContext) ct.vspaceRoot
                          ct.ipcBuffer ct.cspaceRoot)
                      else replyRecvRendezvousR epId tid c rid badge grant layout rf len label
                        executingCore st
                    | none => replyRecvRendezvousR epId tid c rid badge grant layout rf len label
                        executingCore st
                  | _ => replyRecvRendezvousR epId tid c rid badge grant layout rf len label
                      executingCore st
                | none => replyRecvRendezvousR epId tid c rid badge grant layout rf len label
                    executingCore st
            | _ => replyRecvRendezvousR epId tid c rid badge grant layout rf len label
                executingCore st
          | none => replyRecvRendezvousR epId tid c rid badge grant layout rf len label
              executingCore st
        | none => replyRecvRendezvousR epId tid c rid badge grant layout rf len label
            executingCore st
      | none => replyRecvRendezvousR epId tid c rid badge grant layout rf len label
          executingCore st
    else replyRecvCallTakeArmR epId tid c rid badge grant layout rf len label executingCore st

/-- On an unfaulted caller the take arm is the specification's path. -/
theorem replyRecvTakeArmR_eq (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (hNoF : threadHasPendingFault st c = false) :
    replyRecvTakeArmR epId tid c rid badge grant layout rf len label executingCore st =
      replyRecvRendezvousR epId tid c rid badge grant layout rf len label executingCore st := by
  unfold replyRecvTakeArmR
  split
  · next hA =>
    unfold replyRecvTakeAdmits at hA
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hA
    obtain ⟨hSz4, hTk⟩ := hA
    obtain ⟨ct, ep0, rp, ep, s, sTcb, hT, hIpc, hRO, hW, hNe, hRp, hEp, hH, hTs, hSC, hF, hG⟩ :=
      replyRecvTakes_spec hTk
    have hE := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp
    have hS := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTs
    simp only [hEp, hH, hTs]
    split
    · next capAddr mi hR =>
      split
      · next hI =>
        have h := replyRecvOnCore_take_delivered st epId tid c rid layout rf len badge grant
          executingCore ct ep0 rp ep s sTcb capAddr mi hSz4 hT hIpc hRO hW hNe hRp
          (replyRecvReplyInertW_spec hI hT) hE hH hS hSC hG
          ((Architecture.RegisterDecode.registerRoutedSyscall_default _).trans hR) hF
        rw [Architecture.regMessageFrameW_eq, ← TCB.ipcBadgeView_eq_opt]
        unfold replyRecvRendezvousR
        rw [replyRecvTransferOnCore_of_no_fault (h := hNoF)]
        generalize endpointReplyRecvOnCore epId tid rid c
          { registers := Architecture.regReplyRecvBody layout rf len, badge := badge } grant
          executingCore st = r at h ⊢
        rcases r with e | ⟨a, st'⟩
        · cases h
        · simp only [Except.ok.injEq] at h ⊢
          exact h.symm
      · split
        · next stcb hS' =>
          split
          · next capAddr' mi' hR' =>
            split
            · next ct0 hTc0 =>
              have hTc0' := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc0
              obtain rfl : ct = ct0 := by rw [hT] at hTc0'; cases hTc0'; rfl
              split
              · next hGr =>
                subst hGr
                have hReq := replyCapRequest_of_routedReplyRecv st tid stcb capAddr' mi' hS' hR'
                have h := replyRecvOnCore_take_capsDelivered st epId tid c rid layout rf len badge
                  executingCore ct ep0 rp ep s sTcb capAddr mi stcb _ hSz4 hT hIpc hRO hW hNe hRp
                  hE hH hS hSC hG ((Architecture.RegisterDecode.registerRoutedSyscall_default _).trans hR)
                  hF hReq
                rw [Architecture.regMessageFrameW_eq, ← TCB.ipcBadgeView_eq_opt]
                unfold replyRecvRendezvousR
                rw [replyRecvTransferOnCore_of_no_fault (h := hNoF)]
                generalize endpointReplyRecvOnCore epId tid rid c
                  { registers := Architecture.regReplyRecvBody layout rf len, badge := badge } true
                  executingCore st = r at h ⊢
                rcases r with e | ⟨a, st'⟩
                · cases h
                · simp only [Except.ok.injEq] at h ⊢
                  exact h.symm
              · rfl
            · rfl
          · rfl
        · rfl
    · rfl
  · exact replyRecvCallTakeArmR_eq epId tid c rid badge grant layout rf len label executingCore
      st hNoF

/-- WS-ZA ZA6.34: whether a reply-receive of at most four words answering a
caller recording no server may block in place (`replyRecvUnheldBlocks`), its
reply leg transferring no capability (`replyRecvReplyInertW`).  Out of
line, so the checks are one call and nothing they read is held across the
writes. -/
@[noinline] def replyRecvUnheldAdmits (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (grant : Bool) (layout : SeLe4n.SyscallRegisterLayout) (len : Nat)
    (st : SystemState) : Bool :=
  decide (Architecture.regMessageLength layout len - 1 ≤ 4) && replyRecvUnheldBlocks st epId tid c rid &&
    replyRecvReplyInertW st tid c grant

/-- The checked reply-receive answering a caller recording no server (seL4-MCS's
`doReplyTransfer` by a holder of the reply capability, then `reply_pop` handing
the context the reply object heads to the caller): in place when
`replyRecvUnheldAdmits` passes (`performReplyRecvUnheldDelivered`,
`replyRecvOnCore_unheld_delivered`), the context the reply object heads and the
caller's home read on the pre-state; the specification's otherwise. -/
@[inline] def replyRecvUnheldArmR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    if replyRecvUnheldAdmits epId tid c rid grant layout len st then
      .ok ((), performReplyRecvUnheldDelivered st c tid rid ⟨replyHeadContextCode st rid - 1⟩
        (determineTargetCore st c) epId (receiveQueueTailCode st epId) layout rf len badge
        executingCore)
    else replyRecvTakeArmR epId tid c rid badge grant layout rf len label executingCore st

/-- Whether a donated reply-receive of at most four words, its reply leg
transferring no capability (`replyRecvReplyInertW`), takes in place a caller
queued by a routed capability-free call and is donated that caller's context
(`replyRecvDonatedCallTakes`).  Out of line, so the checks are one call and
nothing they read is held across the writes. -/
@[noinline] def replyRecvDonatedCallTakeAdmits (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (grant : Bool) (layout : SeLe4n.SyscallRegisterLayout) (len : Nat)
    (st : SystemState) : Bool :=
  decide (Architecture.regMessageLength layout len - 1 ≤ 4) &&
    replyRecvDonatedCallTakes st epId tid c rid && replyRecvQueuedCallRoutes st epId &&
    replyRecvReplyInertW st tid c grant

/-- **The checked donated reply-receive whose receive leg takes a donating
caller** (seL4-MCS's `handleReplyRecv` on a passive server under load:
`doReplyTransfer`, `reply_pop` handing the context back to the answered
caller, then `receiveIPC` taking a caller queued by a `Call` and
`schedContext_donate` handing that caller's context to the server): in place
when `replyRecvDonatedCallTakeAdmits` passes (`performReplyRecvDonatedCallTakeDelivered`,
`replyRecvOnCore_donatedCallTake_delivered`), every context, core and word it
takes read on the pre-state; `replyRecvUnheldArmR` otherwise. -/
@[inline] def replyRecvDonatedCallTakeArmR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    if replyRecvDonatedCallTakeAdmits epId tid c rid grant layout len st then
      match st.getEndpoint? epId with
      | some ep =>
        match ep.sendQ.head with
        | some s =>
          match st.getTcb? s with
          | some sTcb =>
            match Architecture.RegisterDecode.registerRoutedSyscallOf SeLe4n.arm64DefaultLayout
                sTcb.registerContext with
            | .call _ mi =>
              .ok ((), performReplyRecvDonatedCallTakeDelivered st c tid rid
                ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) epId s
                sTcb.queueNextCode ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s)
                (determineTargetCore st tid) executingCore layout rf len badge sTcb.registerContext
                mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged)
            | _ => replyRecvUnheldArmR epId tid c rid badge grant layout rf len label executingCore st
          | none => replyRecvUnheldArmR epId tid c rid badge grant layout rf len label executingCore st
        | none => replyRecvUnheldArmR epId tid c rid badge grant layout rf len label executingCore st
      | none => replyRecvUnheldArmR epId tid c rid badge grant layout rf len label executingCore st
    else replyRecvUnheldArmR epId tid c rid badge grant layout rf len label executingCore st

theorem replyRecvDonatedCallTakeArmR_of_not_admits (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (hA : replyRecvDonatedCallTakeAdmits epId tid c rid grant layout len st = false) :
    replyRecvDonatedCallTakeArmR epId tid c rid badge grant layout rf len label executingCore st =
      replyRecvUnheldArmR epId tid c rid badge grant layout rf len label executingCore st := by
  unfold replyRecvDonatedCallTakeArmR
  simp only [hA, Bool.false_eq_true, ↓reduceIte]

/-- On an unfaulted caller, once admitted, the arm is the specification's path. -/
theorem replyRecvDonatedCallTakeArmR_of_admits (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (hNoF : threadHasPendingFault st c = false)
    (hA : replyRecvDonatedCallTakeAdmits epId tid c rid grant layout len st = true) :
    replyRecvDonatedCallTakeArmR epId tid c rid badge grant layout rf len label executingCore st =
      replyRecvRendezvousR epId tid c rid badge grant layout rf len label executingCore st := by
  have hA' := hA
  unfold replyRecvDonatedCallTakeAdmits at hA'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hA'
  obtain ⟨⟨⟨hSz4, hTk⟩, hRoute⟩, hI⟩ := hA'
  obtain ⟨ct, ep0, ep, s, sTcb, hT, hIpc, hRO, hP, hSRes, hEp, hH, hTs, hSC, hF, hGt⟩ :=
    replyRecvDonatedCallTakes_spec hTk
  have hE := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp
  have hS := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTs
  unfold replyRecvQueuedCallRoutes at hRoute
  simp only [hEp, hH, hTs] at hRoute
  unfold replyRecvDonatedCallTakeArmR
  simp only [hA, ↓reduceIte, hEp, hH, hTs]
  split
  · next capAddr mi hR =>
    have h := replyRecvOnCore_donatedCallTake_delivered st epId tid c rid layout rf len badge grant
      executingCore ct ep0 ep s sTcb capAddr mi hSz4 hT hIpc hRO hSRes hP
      (replyRecvReplyInertW_spec hI hT) hE hH hS hSC hF hGt
      ((Architecture.RegisterDecode.registerRoutedSyscall_default _).trans hR)
    unfold replyRecvRendezvousR
    rw [replyRecvTransferOnCore_of_no_fault (h := hNoF)]
    generalize endpointReplyRecvOnCore epId tid rid c
      { registers := Architecture.regReplyRecvBody layout rf len, badge := badge } grant
      executingCore st = r at h ⊢
    rcases r with e | ⟨a, st'⟩
    · cases h
    · simp only [Except.ok.injEq] at h ⊢
      exact h.symm
  · next hNot =>
    exfalso
    split at hRoute
    · next capAddr mi hR => exact hNot capAddr mi hR
    · cases hRoute

/-- WS-ZA ZA6.33: whether a donated reply-receive of at most four words may
block in place (`replyRecvDonatedBlocks`), its reply leg transferring no
capability (`replyRecvReplyInertW`).  Out of line, so the checks are one
call and nothing they read is held across the writes. -/
@[noinline] def replyRecvDonatedAdmits (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (grant : Bool) (layout : SeLe4n.SyscallRegisterLayout) (len : Nat)
    (st : SystemState) : Bool :=
  decide (Architecture.regMessageLength layout len - 1 ≤ 4) && replyRecvDonatedBlocks st epId tid c rid &&
    replyRecvReplyInertW st tid c grant

/-- The checked reply-receive on a reply whose reply object heads the stack of
the context the server holds on loan (seL4-MCS's `reply_pop` between the legs):
in place when `replyRecvDonatedAdmits` passes (`performReplyRecvDonatedDelivered`,
`replyRecvOnCore_donated_delivered`), the context the reply object heads and
the caller's home read on the pre-state; when a caller is queued instead, the
arm that takes it and is donated its context (`replyRecvDonatedCallTakeArmR`). -/
@[inline] def replyRecvDonatedArmR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    if replyRecvDonatedAdmits epId tid c rid grant layout len st then
      .ok ((), performReplyRecvDonatedDelivered st c tid rid ⟨replyHeadContextCode st rid - 1⟩
        (determineTargetCore st c) epId (receiveQueueTailCode st epId) layout rf len badge
        executingCore)
    else replyRecvDonatedCallTakeArmR epId tid c rid badge grant layout rf len label executingCore
      st

/-- **The checked reply-receive answering a faulted caller**: in place on every
shape whose writes stay in their slots, the caller's fault words read off the
pre-state and the fault answered from them and the reply's registers past MR0,
the answer the `.reply` arm applies (`performFaultAnswer`): the reply-receive
that blocks (`replyRecvBlocksFast`, `performReplyRecvFaultAnswer`), the donated
one (`replyRecvDonatedBlocks`, `performReplyRecvDonatedFaultAnswer`) and the one
answering a caller recording no server (`replyRecvUnheldBlocks`,
`performReplyRecvUnheldFaultAnswer`); the specification's otherwise
(`replyRecvFaultArmR_eq`).  The caller's words are read before the writes and
its TCB is not held across them. -/
@[inline] def replyRecvFaultArmR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    match st.getTcb? c with
    | some ct =>
        if replyRecvBlocksFast st epId tid c rid then
          .ok ((), performReplyRecvFaultAnswer st c tid rid epId (receiveQueueTailCode st epId)
            executingCore ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0
            ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7
            layout rf len)
        else if replyRecvDonatedBlocks st epId tid c rid then
          .ok ((), performReplyRecvDonatedFaultAnswer st c tid rid
            ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) epId
            (receiveQueueTailCode st epId) executingCore ct.faultKind label ct.faultIp ct.faultSp
            ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5
            ct.faultX6 ct.faultX7 layout rf len)
        else if replyRecvUnheldBlocks st epId tid c rid then
          .ok ((), performReplyRecvUnheldFaultAnswer st c tid rid
            ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) epId
            (receiveQueueTailCode st epId) executingCore ct.faultKind label ct.faultIp ct.faultSp
            ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5
            ct.faultX6 ct.faultX7 layout rf len)
        else replyRecvRendezvousR epId tid c rid badge grant layout rf len label executingCore st
    | none => replyRecvRendezvousR epId tid c rid badge grant layout rf len label executingCore st

/-- On a faulted caller the arm is the specification's path. -/
theorem replyRecvFaultArmR_eq (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (hF : threadHasPendingFault st c = true) :
    replyRecvFaultArmR epId tid c rid badge grant layout rf len label executingCore st =
      replyRecvRendezvousR epId tid c rid badge grant layout rf len label executingCore st := by
  unfold replyRecvFaultArmR
  split
  · next ct0 hTc0 =>
    have hTc0' := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc0
    obtain ⟨tf, hPF⟩ : ∃ tf, ct0.pendingFault = some tf := by
      unfold threadHasPendingFault at hF
      rw [hTc0] at hF
      exact Option.isSome_iff_exists.mp hF
    split
    · next hB =>
      obtain ⟨ct, ep0, rt, ep, rp, hT, hIpc, hRO, hW, hNe, hE, hS, hR, hA, hEnq, hRp,
        hFree, hStash, hRecR, hTail⟩ := replyRecvBlocksFast_spec hB
      obtain rfl : ct = ct0 := by
        rw [hT] at hTc0'; cases hTc0'; rfl
      unfold replyRecvRendezvousR
      rw [replyRecvTransferOnCore_fault_blocks_inPlace st epId tid c rid label layout rf len badge
        grant executingCore ct ep0 rt ep rp tf hPF hT hIpc hRO hW hNe hE hS hR hA hEnq hRp hFree
        hStash hRecR]
      simp only [CapTransferSummary.capInfo_empty]
      rw [hTail, performReplyRecvFaultAnswer_staged st epId tid c rid executingCore _ _ _ _ _ _ _
        _ _ _ _ _ _ layout rf len ct ep0 rt ep rp hT hIpc hW hNe hE hR hA hEnq hRp hFree hStash
        hRecR]
    · split
      · next hB =>
        obtain ⟨ct, ep0, rt, ep, rp, hT, hIpc, hRO, hP, hSRes, hE, hS, hR, hA, hEnq, hRp,
          hStash, hRecR⟩ := replyRecvDonatedBlocks_spec hB
        obtain rfl : ct = ct0 := by
          rw [hT] at hTc0'; cases hTc0'; rfl
        have hTail : receiveQueueTailCode st epId = ep.recvTailCode := by
          simp only [receiveQueueTailCode, (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE]
        obtain ⟨hEq, hStg⟩ := replyRecvTransferOnCore_fault_donated_inPlace st epId tid c rid label
          layout rf len badge grant executingCore ct ep0
          rt ep rp tf hPF hT hIpc hRO hSRes hP hE hS hR hA hEnq hRp hStash hRecR
        unfold replyRecvRendezvousR
        rw [hEq]
        simp only [CapTransferSummary.capInfo_empty]
        rw [hTail, hStg]
      · split
        · next hB =>
          obtain ⟨ct, ep0, rt, ep, rp, hT, hIpc, hRO, hU, hNe, hE, hS, hR, hA, hEnq, hRp,
            hStash, hRecR, hTail⟩ := replyRecvUnheldBlocks_spec hB
          obtain rfl : ct = ct0 := by
            rw [hT] at hTc0'; cases hTc0'; rfl
          obtain ⟨hEq, hStg⟩ := replyRecvTransferOnCore_fault_unheld_inPlace st epId tid c rid label
            layout rf len badge grant executingCore ct ep0
            rt ep rp tf hPF hT hIpc hRO hU hNe hE hS hR hA hEnq hRp hStash hRecR
          unfold replyRecvRendezvousR
          rw [hEq]
          simp only [CapTransferSummary.capInfo_empty]
          rw [hTail, hStg]
        · rfl
  · rfl

/-- The checked reply-receive once its reply capability resolved to reply object
`rid`, answering caller `c` with badge `badge`: the reply leg's flow gate, then a
caller carrying a fault answered through the specification's path (its fault
reply: `replyRecvFaultArmR`, in place when the receive blocks), and for any
other caller the in-place path when
it may be taken (`replyRecvBlocksFast`, a reply of at most four words whose reply
leg transfers no capability, `replyRecvReplyInertW`; `replyRecvDonatedArmR` on a
donated reply; `replyRecvCapsArmR` when the reply leg installs under the grant
right, its transfer run in place between the reply's writes and the receive),
the specification's otherwise.  Every
in-place path delivers the reply as a message, which is the answer only for a
caller carrying no fault, so the fault test runs first. -/
@[inline] def replyRecvResolvedR (ctx : LabelingContext) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    if securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf c) then
      if threadHasPendingFault st c then
        replyRecvFaultArmR epId tid c rid badge grant layout rf len label executingCore st
      else if decide (Architecture.regMessageLength layout len - 1 ≤ 4) &&
          replyRecvBlocksFast st epId tid c rid && replyRecvReplyInertW st tid c grant then
        .ok ((), performReplyRecvBlockDelivered st c tid rid epId (receiveQueueTailCode st epId)
          layout rf len badge executingCore)
      else replyRecvDonatedArmR epId tid c rid badge grant layout rf len label executingCore st
    else .error (.replyCapInvalid, st)

/-- The general reply-receive arm on a message read in registers. -/
@[inline] def endpointReplyRecvCheckedArmRegsR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability) :
    RefusalCarrying Unit :=
  endpointReplyRecvCheckedArmGeneralR ctx
    { length := len, extraCaps := extraCaps, label := label }
    (Architecture.regMessageRegs layout rf) tid executingCore cap

/-- WS-ZA ZA4.7: the checked reply-receive arm (`dispatchWithCapChecked`'s
`.replyRecv` case) on a message read in registers, refusing in the state it was
handed (`endpointReplyRecvCheckedArmR_eq`).  The reply capability at MR0 is
resolved in continuation form; a reply-receive that may block in place
(`replyRecvBlocksFast`) writes in place (`performReplyRecvBlockDelivered`). -/
@[inline] def endpointReplyRecvCheckedArmR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability) :
    RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object epId =>
      if !endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) then
        .error (.flowDenied, st)
      else
      if h0 : 0 < layout.msgRegs.size then
        let resolved := fun rid c badge grant =>
          replyRecvResolvedR ctx epId tid c rid badge grant layout rf len label executingCore st
        resolveReplyRecvK st tid len
          (SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf (layout.msgRegs[0]'h0)))
          (fun e => .error (e, st)) resolved
      else endpointReplyRecvCheckedArmRegsR ctx layout rf len extraCaps label tid executingCore
          cap st
    | _ => .error (.invalidCapability 0, st)

theorem endpointReplyRecvCheckedArmR_eq_general (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability) :
    endpointReplyRecvCheckedArmR ctx layout rf len extraCaps label tid executingCore cap =
      endpointReplyRecvCheckedArmRegsR ctx layout rf len extraCaps label tid executingCore cap := by
  funext st
  unfold endpointReplyRecvCheckedArmR endpointReplyRecvCheckedArmRegsR
  split
  · next epId hTgt =>
    simp only [endpointReplyRecvCheckedArmGeneralR, hTgt]
    have hExt : extractMessageRegisters (Architecture.regMessageRegs layout rf)
        { length := len, extraCaps := extraCaps, label := label } =
        Architecture.regMessageBody layout rf len := rfl
    have hB : (Architecture.regMessageBody layout rf len).extract 1
        (Architecture.regMessageBody layout rf len).size =
        Architecture.regReplyRecvBody layout rf len := rfl
    rw [hExt, hB]
    split
    · rfl
    · split
      · next h0 =>
        rw [resolveReplyRecvK_eq st tid len _ (Architecture.regMessageRegs layout rf) _ _
          (fun _ => by
            simp [Architecture.regMessageRegs, h0, SeLe4n.readReg_eq_word, SeLe4n.CPtr.ofWord])]
        cases resolveReplyRecvReplyR st tid len (Architecture.regMessageRegs layout rf) with
        | error e => rfl
        | ok r =>
          obtain ⟨rid, c, badge, grant⟩ := r
          simp only [replyRecvResolvedR]
          split
          · next hFlow =>
            split
            · next hFault =>
              rw [replyRecvFaultArmR_eq epId tid c rid badge grant layout rf len label executingCore st
                hFault]
              simp only [replyRecvRendezvousR]
            rename_i hNoFault
            rw [replyRecvTransferOnCore_of_no_fault (h := by simpa using hNoFault)]
            split
            · next hG =>
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hG
              obtain ⟨⟨hSz, hF⟩, hI⟩ := hG
              obtain ⟨ct, ep0, rt, ep, rp, hT, hIpc, hRO, hW, hNe, hE, hS, hR, hA, hEnq, hRp,
                hFree, hStash, hRecR, hTail⟩ := replyRecvBlocksFast_spec hF
              have hInert := replyRecvReplyInertW_spec hI hT
              have hSz4 : (Architecture.regReplyRecvBody layout rf len).size ≤ 4 := by
                rw [Architecture.regReplyRecvBody_size]; exact hSz
              have h := replyRecvOnCore_blocks_delivered st epId tid c rid
                { registers := Architecture.regReplyRecvBody layout rf len,
                  badge := badge } grant executingCore
                ct ep0 rt ep rp (by simp only; unfold maxMessageRegisters; omega) hSz4 hT hIpc
                hRO hW hNe hE hS hR hA hEnq hRp hFree hStash hRecR hInert
              rw [Architecture.returnFrameOfMessage_regReplyRecvBody,
                replyRecvOnCore_blocks_inPlace st epId tid c rid _ _ _ ct ep0 rt ep rp
                  (by simp only; unfold maxMessageRegisters; omega) hT hIpc hRO hW hNe hE hS hR
                  hA hEnq hRp hFree hStash hRecR hInert] at h
              simp only [CapTransferSummary.capInfo_empty] at h
              rw [hTail, replyRecvOnCore_blocks_inPlace st epId tid c rid _ _ _ ct ep0 rt ep rp
                  ?_ hT hIpc hRO hW hNe hE hS hR hA hEnq hRp hFree hStash hRecR hInert]
              · simp only [CapTransferSummary.capInfo_empty]
                have h2 := congrArg Prod.snd (Except.ok.inj h)
                dsimp only at h2
                rw [h2]
                rfl
              · show ¬ (Architecture.regReplyRecvBody layout rf len).size > maxMessageRegisters
                unfold maxMessageRegisters; omega
            · unfold replyRecvDonatedArmR
              split
              · next hG =>
                unfold replyRecvDonatedAdmits at hG
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hG
                obtain ⟨⟨hSz, hF⟩, hI⟩ := hG
                obtain ⟨ct, ep0, rt, ep, rp, hT, hIpc, hRO, hP, hSRes, hE, hS, hR, hA, hEnq, hRp,
                  hStash, hRecR⟩ := replyRecvDonatedBlocks_spec hF
                have hInert := replyRecvReplyInertW_spec hI hT
                have hTail : receiveQueueTailCode st epId = ep.recvTailCode := by
                  simp only [receiveQueueTailCode, (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE]
                have hSz4 : (Architecture.regReplyRecvBody layout rf len).size ≤ 4 := by
                  rw [Architecture.regReplyRecvBody_size]; exact hSz
                have h := replyRecvOnCore_donated_delivered st epId tid c rid
                  { registers := Architecture.regReplyRecvBody layout rf len,
                    badge := badge } grant executingCore
                  ct ep0 rt ep rp (by simp only; unfold maxMessageRegisters; omega) hSz4 hT hIpc
                  hRO hSRes hP hE hS hR hA hEnq hRp hStash hRecR hInert
                rw [Architecture.returnFrameOfMessage_regReplyRecvBody,
                  (replyRecvOnCore_donated_inPlace st epId tid c rid _ _ _ ct ep0 rt ep rp
                    (by simp only; unfold maxMessageRegisters; omega) hT hIpc hRO hSRes hP hE hS hR
                    hA hEnq hRp hStash hRecR hInert).1] at h
                simp only [CapTransferSummary.capInfo_empty] at h
                rw [hTail, (replyRecvOnCore_donated_inPlace st epId tid c rid _ _ _ ct ep0 rt ep rp
                    ?_ hT hIpc hRO hSRes hP hE hS hR hA hEnq hRp hStash hRecR hInert).1]
                · simp only [CapTransferSummary.capInfo_empty]
                  have h2 := congrArg Prod.snd (Except.ok.inj h)
                  dsimp only at h2
                  rw [h2]
                  rfl
                · show ¬ (Architecture.regReplyRecvBody layout rf len).size > maxMessageRegisters
                  unfold maxMessageRegisters; omega
              · by_cases hDT : replyRecvDonatedCallTakeAdmits epId tid c rid grant layout len st
                · rw [replyRecvDonatedCallTakeArmR_of_admits epId tid c rid badge grant layout rf len
                    label executingCore st (by simpa using hNoFault) hDT]
                  simp only [replyRecvRendezvousR]
                  rw [replyRecvTransferOnCore_of_no_fault (h := by simpa using hNoFault)]
                rw [replyRecvDonatedCallTakeArmR_of_not_admits epId tid c rid badge grant layout rf len
                  label executingCore st (by simpa using hDT)]
                unfold replyRecvUnheldArmR
                split
                · next hG =>
                  unfold replyRecvUnheldAdmits at hG
                  simp only [Bool.and_eq_true, decide_eq_true_eq] at hG
                  obtain ⟨⟨hSz, hF⟩, hI⟩ := hG
                  obtain ⟨ct, ep0, rt, ep, rp, hT, hIpc, hRO, hU, hNe, hE, hS, hR, hA, hEnq, hRp,
                    hStash, hRecR, hTail⟩ := replyRecvUnheldBlocks_spec hF
                  have hInert := replyRecvReplyInertW_spec hI hT
                  have hSz4 : (Architecture.regReplyRecvBody layout rf len).size ≤ 4 := by
                    rw [Architecture.regReplyRecvBody_size]; exact hSz
                  have h := replyRecvOnCore_unheld_delivered st epId tid c rid
                    { registers := Architecture.regReplyRecvBody layout rf len,
                      badge := badge } grant executingCore
                    ct ep0 rt ep rp (by simp only; unfold maxMessageRegisters; omega) hSz4 hT hIpc
                    hRO hU hNe hE hS hR hA hEnq hRp hStash hRecR hInert
                  rw [Architecture.returnFrameOfMessage_regReplyRecvBody,
                    (replyRecvOnCore_unheld_inPlace st epId tid c rid _ _ _ ct ep0 rt ep rp
                      (by simp only; unfold maxMessageRegisters; omega) hT hIpc hRO hU hNe hE hS hR
                      hA hEnq hRp hStash hRecR hInert).1] at h
                  simp only [CapTransferSummary.capInfo_empty] at h
                  rw [hTail, (replyRecvOnCore_unheld_inPlace st epId tid c rid _ _ _ ct ep0 rt ep rp
                      ?_ hT hIpc hRO hU hNe hE hS hR hA hEnq hRp hStash hRecR hInert).1]
                  · simp only [CapTransferSummary.capInfo_empty]
                    have h2 := congrArg Prod.snd (Except.ok.inj h)
                    dsimp only at h2
                    rw [h2]
                    rfl
                  · show ¬ (Architecture.regReplyRecvBody layout rf len).size > maxMessageRegisters
                    unfold maxMessageRegisters; omega
                · rw [replyRecvTakeArmR_eq epId tid c rid badge grant layout rf len label executingCore
                    st (by simpa using hNoFault)]
                  simp only [replyRecvRendezvousR]
                  rw [replyRecvTransferOnCore_of_no_fault (h := by simpa using hNoFault)]
          · rfl
      · rfl
  · next hTgt =>
    unfold endpointReplyRecvCheckedArmGeneralR
    split
    · next epId h => exact absurd h (hTgt epId)
    · rfl

theorem endpointReplyRecvCheckedArmR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (st : SystemState)
    (hRR : decoded.syscallId = .replyRecv)
    (hRegs : Architecture.regMessageRegs layout rf = decoded.msgRegs)
    (hCaller : gate.callerId = tid)
    (hRoot : gate.cspaceRoot = callerCspaceRoot st tid)
    (hDepth : gate.capDepth = callerCspaceDepth st tid) :
    endpointReplyRecvCheckedArmR ctx layout rf decoded.msgInfo.length decoded.msgInfo.extraCaps
        decoded.msgInfo.label tid executingCore cap st =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap)
        st := by
  rw [endpointReplyRecvCheckedArmR_eq_general]
  unfold endpointReplyRecvCheckedArmRegsR
  rw [hRegs]
  exact endpointReplyRecvCheckedArmGeneralR_eq ctx decoded tid executingCore gate cap st hRR
    hCaller hRoot hDepth

/-- The caller a reply-receive's reply leg reaches, read from the pre-state
before the arm, as its code (`SeLe4n.ThreadId.optCode`): the caller recorded
by the reply object the capability at MR0 names (`replyRecvReplyLegEdges`).
The slot is resolved in continuation form, so nothing is built. -/
@[inline] def replyRecvTaintCallerCode (st : SystemState) (tid : SeLe4n.ThreadId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat) : Nat :=
  if len = 0 then 0 else
  if h0 : 0 < layout.msgRegs.size then
    resolveCapAddressKUnrolled (callerCspaceRoot st tid)
      (SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf (layout.msgRegs[0]'h0)))
      (callerCspaceDepth st tid) st (fun _ => 0)
      (fun cnode slot =>
        match SystemState.lookupSlotCap st { cnode := cnode, slot := slot } with
        | some rc =>
            match rc.target with
            | .replyCap rid =>
                match st.getReply? rid with
                | some r => r.callerCode
                | none => 0
            | _ => 0
        | none => 0)
  else 0

theorem replyRecvReplyLegEdges_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (tcb : TCB) (rootCn : CNode)
    (hTcb : st.getObject? tid.toObjId = some (.tcb tcb))
    (hRoot : st.getObject? tcb.cspaceRoot = some (.cnode rootCn))
    (rest : Array SeLe4n.RegValue) (hRest : rest = #[] ∨ 0 < layout.msgRegs.size)
    (hRegs : Architecture.regMessageRegs layout rf ++ rest = decoded.msgRegs) :
    replyRecvReplyLegEdges st tid decoded =
      match replyRecvTaintCallerCode st tid layout rf decoded.msgInfo.length with
      | 0 => []
      | k + 1 => [{ sink := (⟨k⟩ : SeLe4n.ThreadId).toObjId, source := tid.toObjId }] := by
  have hCR : callerCspaceRoot st tid = tcb.cspaceRoot := by simp only [callerCspaceRoot, hTcb]
  have hCD : callerCspaceDepth st tid = rootCn.depth := by
    simp only [callerCspaceDepth, hTcb, hRoot]
  have hOp : ∀ p, syscallOperandCap? st tid p =
      match resolveCapAddress tcb.cspaceRoot p rootCn.depth st with
      | .error _ => none
      | .ok ref => SystemState.lookupSlotCap st ref := by
    intro p
    simp only [SystemState.getObject?_eq_getElem] at hTcb hRoot
    simp only [syscallOperandCap?, SystemState.getTcb?, SystemState.getCNode?, hTcb, hRoot]
    cases resolveCapAddress tcb.cspaceRoot p rootCn.depth st <;> rfl
  unfold replyRecvReplyLegEdges replyRecvTaintCallerCode
  by_cases hL : decoded.msgInfo.length = 0
  · simp [hL]
  · have hL' : (decoded.msgInfo.length == 0) = false := by simp [hL]
    simp only [hL', Bool.false_eq_true, ↓reduceIte, hL]
    by_cases h0 : 0 < layout.msgRegs.size
    · rw [dif_pos h0]
      have hArgs : Architecture.SyscallArgDecode.decodeReplyRecvArgs decoded =
          .ok { replyCPtr := SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf (layout.msgRegs[0]'h0)) } := by
        have hs0 : 0 < (Architecture.regMessageRegs layout rf).size := by
          simp [Architecture.regMessageRegs, h0]
        have hs : 0 < decoded.msgRegs.size := by
          rw [← hRegs, Array.size_append]; omega
        simp only [Architecture.SyscallArgDecode.decodeReplyRecvArgs, requireMsgReg, hs,
          ↓reduceDIte, bind, Except.bind, pure, Except.pure]
        congr 2
        have hE : decoded.msgRegs[0]'hs = (Architecture.regMessageRegs layout rf)[0]'hs0 := by
          simp only [← hRegs]; exact Array.getElem_append_left hs0
        rw [hE]
        simp only [Architecture.regMessageRegs, Array.getElem_map,
          SeLe4n.readReg_val_eq_word, SeLe4n.CPtr.ofWord_eq_ofNat]
      rw [hArgs]
      simp only [hOp, hCR, hCD]
      rw [resolveCapAddressKUnrolled_eq, resolveCapAddressK_eq]
      cases resolveCapAddress tcb.cspaceRoot _ rootCn.depth st with
      | error e => rfl
      | ok ref =>
        simp only []
        cases SystemState.lookupSlotCap st ref with
        | none => rfl
        | some rc =>
          simp only []
          cases rc.target <;> try rfl
          rename_i rid
          simp only [replyTaintEdges]
          cases st.getReply? rid with
          | none => rfl
          | some r =>
            simp only [Option.bind_some, Reply.caller]
            cases r.callerCode <;> rfl
    · rw [dif_neg h0]
      have hArgs : ∃ e, Architecture.SyscallArgDecode.decodeReplyRecvArgs decoded = .error e := by
        have hs : ¬ 0 < decoded.msgRegs.size := by
          rcases hRest with rfl | hP
          · rw [← hRegs, Array.append_empty]; simpa [Architecture.regMessageRegs] using h0
          · exact absurd hP h0
        exact ⟨.invalidMessageInfo, by simp only [Architecture.SyscallArgDecode.decodeReplyRecvArgs,
          requireMsgReg, hs, ↓reduceDIte, bind, Except.bind]⟩
      obtain ⟨e, he⟩ := hArgs
      rw [he]

/-- The reply leg's caller code for the capability the operand resolved to:
`replyRecvTaintCallerCode` when it names an endpoint, the only target a
reply-receive declares edges for, and none otherwise. -/
@[inline] def replyRecvTaintCallerCodeOf (st : SystemState) (tid : SeLe4n.ThreadId)
    (cap : Capability) (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (len : Nat) : Nat :=
  match cap.target with
  | .object _ => replyRecvTaintCallerCode st tid layout rf len
  | _ => 0

/-- The reply-receive's taint step, without the plan: the receive leg's sender
words `wS` join the server's, then the server's words `wT` — both captured
before the arm, so the server's are its pre-state's — join the answered
caller's (`replyRecvTaintStep_eq`). -/
@[inline] def replyRecvTaintStep (sourceCode callerCode : Nat) (tid : SeLe4n.ThreadId)
    (wS wT : TaintWords) (post : SystemState) : SystemState :=
  sendTaintStep callerCode tid wT (receiveTaintStep sourceCode tid wS post)

theorem replyRecvTaintStep_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (hRR : decoded.syscallId = .replyRecv)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (tcb : TCB) (rootCn : CNode)
    (hTcb : st.getObject? tid.toObjId = some (.tcb tcb))
    (hRoot : st.getObject? tcb.cspaceRoot = some (.cnode rootCn))
    (rest : Array SeLe4n.RegValue) (hRest : rest = #[] ∨ 0 < layout.msgRegs.size)
    (hRegs : Architecture.regMessageRegs layout rf ++ rest = decoded.msgRegs)
    (preEpoch : Nat) (preLength : Nat) (wS : Capability → TaintWords) (wT : TaintWords)
    (hS : ∀ cap, (wS cap).decode =
      st.declassificationTaint (threadObjOfCode (receiveTaintSourceCode st cap)))
    (hT : wT.decode = st.declassificationTaint tid.toObjId)
    (post : SystemState) :
    applySyscallTaintAfter (syscallTaintPlan st tid decoded) preEpoch preLength
        st.declassificationTaint post =
      (match syscallOperandCap? st tid decoded.capAddr with
        | some cap => replyRecvTaintStep (receiveTaintSourceCode st cap)
            (replyRecvTaintCallerCodeOf st tid cap layout rf decoded.msgInfo.length) tid (wS cap)
            wT post
        | none => post) := by
  simp only [syscallTaintPlan, contentFlowClass, hRR, contentFlowEdges, contentFlowClears,
    contentFlowBypassed]
  rcases syscallOperandCap? st tid decoded.capAddr with _ | cap
  · simp [applySyscallTaintAfter, syscallRecordsDeclassification,
      applyOrigination, applyTaintClears, applyTaintFlow, applyTaintStep]
  · have h := hS cap
    rcases cap with ⟨target, _, _⟩
    cases target with
    | object epId =>
      simp only [receiveTaintSourceCode, receiverTaintEdges, replyRecvTaintCallerCodeOf,
        replyRecvReplyLegEdges_eq st tid decoded layout rf tcb rootCn hTcb hRoot rest hRest hRegs,
        replyRecvTaintStep] at h ⊢
      generalize replyRecvTaintCallerCode st tid layout rf decoded.msgInfo.length = k
      revert h
      cases st.getEndpoint? epId with
      | none =>
        intro _
        cases k <;>
          simp [receiveTaintStep, sendTaintStep, applySyscallTaintAfter,
            syscallRecordsDeclassification, applyOrigination, applyTaintClears, applyTaintFlow,
            applyTaintStep, joinTaintAt_toWords_of_decode _ _ hT]
      | some ep =>
        simp only [Option.bind_some, ← Endpoint.ofOptCode_sendHeadCode]
        cases ep.sendHeadCode <;> cases k <;> intro h <;>
          simp only [threadObjOfCode, Nat.add_sub_cancel] at h <;>
          simp [receiveTaintStep, sendTaintStep, SeLe4n.ThreadId.ofOptCode,
            applySyscallTaintAfter, syscallRecordsDeclassification, applyOrigination,
            applyTaintClears, applyTaintFlow, applyTaintStep,
            joinTaintAt_toWords_of_decode _ _ hT, joinTaintAt_toWords_of_decode _ _ h]
    | _ =>
      simp [receiveTaintSourceCode, replyRecvTaintCallerCodeOf, replyRecvTaintStep,
        receiveTaintStep, sendTaintStep, applySyscallTaintAfter,
        syscallRecordsDeclassification, applyOrigination, applyTaintClears, applyTaintFlow, applyTaintStep]

/-- WS-ZA ZA4.7: the reply-receive's slot check, gate, arm and taint step on
the capability its operand resolved to.  Every refusal carries the state it was
handed (`replyRecvOperandArmThenTaintR_eq`). -/
@[inline] def replyRecvOperandArmThenTaintR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (requiredRight : AccessRight)
    (operand : Option Capability) : RefusalCarrying Unit :=
  fun st =>
    match operand with
    | none => .error (.invalidCapability 0, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedKernelObject cap then .error (.invalidCapability 0, st)
        else if !syscallTargetAccepted .replyRecv st cap then .error (.invalidCapability 0, st)
        else if cap.hasRight requiredRight then
          let sourceCode := receiveTaintSourceCode st cap
          let callerCode := replyRecvTaintCallerCodeOf st tid cap layout rf len
          withTaintWordsAt st (threadObjOfCode sourceCode) fun a0 a1 a2 a3 a4 a5 a6 a7 ac as =>
          withTaintWordsAt st tid.toObjId fun b0 b1 b2 b3 b4 b5 b6 b7 bc bs =>
          match endpointReplyRecvCheckedArmR ctx layout rf len extraCaps label tid executingCore
              cap st with
          | .error refusal => .error refusal
          | .ok ((), stPost) =>
              .ok ((), replyRecvTaintStep sourceCode callerCode tid
                ⟨a0, a1, a2, a3, a4, a5, a6, a7, ac, as⟩ ⟨b0, b1, b2, b3, b4, b5, b6, b7, bc, bs⟩
                stPost)
        else .error (syscallMissingRightError .replyRecv, st)

theorem replyRecvOperandArmThenTaintR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId)
    (preEpoch : Nat) (preLength : Nat)
    (st : SystemState) (tcb : TCB) (rootCn : CNode) (ref : CSpaceAddr)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (hRR : decoded.syscallId = .replyRecv)
    (hRegs : Architecture.regMessageRegs layout rf = decoded.msgRegs)
    (hTcb : st.getObject? tid.toObjId = some (.tcb tcb))
    (hRoot : st.getObject? tcb.cspaceRoot = some (.cnode rootCn))
    (hRef : resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth st = .ok ref) :
    replyRecvOperandArmThenTaintR ctx layout rf decoded.msgInfo.length decoded.msgInfo.extraCaps
        decoded.msgInfo.label tid executingCore
        (syscallRequiredRight decoded.syscallId) (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore
        { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
          capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
        (syscallTaintPlan st tid decoded) preEpoch preLength st.declassificationTaint) st := by
  have hOperand := syscallOperandCap?_of_resolved st tid _ tcb rootCn ref hTcb hRoot hRef
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel,
    hRR, ↓reduceIte, syscallInvokeTyped, syscallResolveCap, hRef]
  simp only [replyRecvTaintStep_eq st tid decoded hRR layout rf tcb rootCn hTcb hRoot #[] (Or.inl rfl)
    (by rw [Array.append_empty]; exact hRegs)
    (wS := fun cap => st.taintWordsAt (threadObjOfCode (receiveTaintSourceCode st cap)))
    (wT := st.taintWordsAt tid.toObjId) (hS := fun _ => decode_taintWordsAt st _)
    (hT := decode_taintWordsAt st _), hOperand]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [replyRecvOperandArmThenTaintR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hType : syscallTargetAccepted .replyRecv st cap = false
      · simp only [hIdle, hType, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      replace hType : syscallTargetAccepted .replyRecv st cap = true := by simpa using hType
      by_cases hRight : cap.hasRight (syscallRequiredRight .replyRecv) = true
      · simp only [hIdle, hType, Bool.not_true, Bool.false_eq_true, hRight, ↓reduceIte, Bool.false_eq_true, withTaintWordsAt_eq,
          TaintWords.mk_fields]
        rw [endpointReplyRecvCheckedArmR_eq ctx decoded tid executingCore
          { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
            capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
          cap layout rf st hRR hRegs rfl (by simp only [callerCspaceRoot, hTcb])
          (by simp only [callerCspaceDepth, hTcb, hRoot])]
        simp only [RefusalCarrying.ofKernel, hRR]
        rcases dispatchWithCapChecked ctx decoded tid executingCore
          { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
            capDepth := rootCn.depth, requiredRight := syscallRequiredRight .replyRecv }
          cap st with _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hType, Bool.not_true, Bool.false_eq_true, hRight, ↓reduceIte, Bool.false_eq_true]

/-- WS-ZA ZA4.7: the reply-receive's dispatch: `dispatchOperandCheckedR` with
the reply-receive's arm (`dispatchReplyRecvCheckedR_eq`).

A specification: the compiled entry runs the arm out of line
(`syscallEntryRoutedK`), so no code is generated for it. -/
noncomputable def dispatchReplyRecvCheckedR (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore
    (replyRecvOperandArmThenTaintR ctx layout rf len extraCaps label tid executingCore
      (syscallRequiredRight .replyRecv))

theorem dispatchReplyRecvCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (hRR : decoded.syscallId = .replyRecv)
    (hRegs : Architecture.regMessageRegs layout rf = decoded.msgRegs) :
    dispatchReplyRecvCheckedR ctx decoded.capAddr layout rf decoded.msgInfo.length
        decoded.msgInfo.extraCaps decoded.msgInfo.label tid executingCore =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) := by
  apply dispatchOperandCheckedR_eq ctx decoded tid executingCore _ (by rw [hRR]; decide)
  intro st tcb rootCn ref hTcb hRoot hRef
  have hArm := replyRecvOperandArmThenTaintR_eq ctx decoded tid executingCore
    st.declassificationAuditEpoch st.declassificationAudit.length
    st tcb rootCn ref layout rf hRR hRegs hTcb hRoot hRef
  simp only [hRR] at hArm ⊢
  exact hArm

/-! ### The long reply-receive -/

/-- The long reply-receive's rendezvous through the specification's path, its
message read in the replier's registers and IPC buffer (`longReplyRecvRegs`). -/
@[noinline] def replyRecvLongRendezvousR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool) (rf : SeLe4n.RegisterFile)
    (len label : Nat) (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    match replyRecvTransferOnCore epId tid rid c label
        { registers := longReplyRecvRegs rf st tid len, badge := badge }
        grant executingCore st with
    | .ok (summary, st') =>
        .ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo)
    | .error e => .error (e, st)

/-- Whether the long reply-receive's transferring arm may block in place: the
grant right, an unfaulted caller and `replyRecvBlocksFast`.  Out of line, so
the checks are one call. -/
@[noinline] def replyRecvLongCapsAdmits (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (grant : Bool) : Bool :=
  grant && !threadHasPendingFault st c && replyRecvBlocksFast st epId tid c rid

/-- The same for the donated shape (`replyRecvDonatedBlocks`). -/
@[noinline] def replyRecvLongDonatedCapsAdmits (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (grant : Bool) : Bool :=
  grant && !threadHasPendingFault st c && replyRecvDonatedBlocks st epId tid c rid

/-- The same for the shape answering a caller recording no server
(`replyRecvUnheldBlocks`). -/
@[noinline] def replyRecvLongUnheldCapsAdmits (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (grant : Bool) : Bool :=
  grant && !threadHasPendingFault st c && replyRecvUnheldBlocks st epId tid c rid

/-- The long reply-receive whose reply leg transfers, its caller unfaulted:
under the grant right, on each shape whose receive leg blocks in place -- the
plain one (`replyRecvBlocksFast`), the donated one (`replyRecvDonatedBlocks`)
and the one answering a caller recording no server (`replyRecvUnheldBlocks`) --
the reply's writes, the transfer in place, then the receive's
block and the long frame (`performReplyRecvBlockCapsDeliveredLong`,
`performReplyRecvDonatedCapsDeliveredLong`,
`performReplyRecvUnheldCapsDeliveredLong`); the specification's path otherwise
(`replyRecvLongCapsR_eq`).  Each shape's guard is one out-of-line call, so a
test it shares with the inert arm's is not hoisted into a closure the inert path
builds. -/
@[inline] def replyRecvLongCapsR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (rf : SeLe4n.RegisterFile) (len label : Nat) (executingCore : Concurrency.CoreId) :
    RefusalCarrying Unit :=
  fun st =>
    if replyRecvLongCapsAdmits st epId tid c rid grant then
      match st.getTcb? tid with
      | some stcb =>
          match st.getTcb? c with
          | some ct =>
              .ok ((), performReplyRecvBlockCapsDeliveredLong st c tid rid epId
                (receiveQueueTailCode st epId) rf len badge executingCore stcb.vspaceRoot
                stcb.ipcBuffer stcb.cspaceRoot (routedExtraCaps rf) ct.vspaceRoot ct.ipcBuffer
                ct.cspaceRoot)
          | none => replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
      | none => replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
    else if replyRecvLongDonatedCapsAdmits st epId tid c rid grant then
      match st.getTcb? tid with
      | some stcb =>
          match st.getTcb? c with
          | some ct =>
              .ok ((), performReplyRecvDonatedCapsDeliveredLong st c tid rid
                ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) epId
                (receiveQueueTailCode st epId) rf len badge executingCore stcb.vspaceRoot
                stcb.ipcBuffer stcb.cspaceRoot (routedExtraCaps rf) ct.vspaceRoot ct.ipcBuffer
                ct.cspaceRoot)
          | none => replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
      | none => replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
    else if replyRecvLongUnheldCapsAdmits st epId tid c rid grant then
      match st.getTcb? tid with
      | some stcb =>
          match st.getTcb? c with
          | some ct =>
              .ok ((), performReplyRecvUnheldCapsDeliveredLong st c tid rid
                ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) epId
                (receiveQueueTailCode st epId) rf len badge executingCore stcb.vspaceRoot
                stcb.ipcBuffer stcb.cspaceRoot (routedExtraCaps rf) ct.vspaceRoot ct.ipcBuffer
                ct.cspaceRoot)
          | none => replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
      | none => replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
    else replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st

/-- Whether a donated long reply-receive whose reply leg transfers no capability
may block in place: an unfaulted caller, `replyRecvDonatedBlocks` and
`replyRecvReplyInertW`.  Out of line, so the checks are one call. -/
@[noinline] def replyRecvLongDonatedAdmits (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (grant : Bool) : Bool :=
  !threadHasPendingFault st c && replyRecvDonatedBlocks st epId tid c rid &&
    replyRecvReplyInertW st tid c grant

/-- The same for the shape answering a caller recording no server
(`replyRecvUnheldBlocks`). -/
@[noinline] def replyRecvLongUnheldAdmits (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (grant : Bool) : Bool :=
  !threadHasPendingFault st c && replyRecvUnheldBlocks st epId tid c rid &&
    replyRecvReplyInertW st tid c grant

/-- The long reply-receive whose reply pops a donation, its reply leg
transferring no capability: the donated shape
(`performReplyRecvDonatedDeliveredLong`) and the one answering a caller
recording no server (`performReplyRecvUnheldDeliveredLong`), the context the
reply object heads and the caller's home read on the pre-state; the
transferring arm (`replyRecvLongCapsR`) otherwise (`replyRecvLongPopR_eq`). -/
@[inline] def replyRecvLongPopR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (rf : SeLe4n.RegisterFile) (len label : Nat) (executingCore : Concurrency.CoreId) :
    RefusalCarrying Unit :=
  fun st =>
    if replyRecvLongDonatedAdmits st epId tid c rid grant then
      .ok ((), performReplyRecvDonatedDeliveredLong st c tid rid ⟨replyHeadContextCode st rid - 1⟩
        (determineTargetCore st c) epId (receiveQueueTailCode st epId) rf len badge executingCore)
    else if replyRecvLongUnheldAdmits st epId tid c rid grant then
      .ok ((), performReplyRecvUnheldDeliveredLong st c tid rid ⟨replyHeadContextCode st rid - 1⟩
        (determineTargetCore st c) epId (receiveQueueTailCode st epId) rf len badge executingCore)
    else replyRecvLongCapsR epId tid c rid badge grant rf len label executingCore st

/-- The long transferring arm is the specification's path, the replier's frame
asking for its routed capabilities under the grant right (`hReqOf`). -/
theorem replyRecvLongCapsR_eq (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (rf : SeLe4n.RegisterFile) (len label : Nat) (executingCore : Concurrency.CoreId)
    (st : SystemState) (hLen : 5 ≤ len)
    (hSzL : ¬ (longReplyRecvRegs rf st tid len).size > maxMessageRegisters)
    (hReqOf : ∀ stcb, st.getTcb? tid = some stcb →
      replyCapRequest st tid true = frameCapRequestOf st stcb (routedExtraCaps rf)) :
    replyRecvLongCapsR epId tid c rid badge grant rf len label executingCore st =
      replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st := by
  unfold replyRecvLongCapsR
  split
  · next hG =>
    unfold replyRecvLongCapsAdmits at hG
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hG
    obtain ⟨⟨hGr, hNoFault⟩, hF⟩ := hG
    subst hGr
    obtain ⟨ct, ep0, rt, ep, rp, hT, hIpc, hRO, hW, hNe, hE, hS, hR', hA, hEnq, hRp,
      hFree, hStash, hRecR, hTail⟩ := replyRecvBlocksFast_spec hF
    split
    · next stcb hS' =>
      split
      · next ct0 hTc0 =>
        obtain rfl : ct = ct0 := by
          rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp hTc0] at hT; cases hT; rfl
        unfold replyRecvLongRendezvousR
        rw [replyRecvTransferOnCore_of_no_fault (h := hNoFault)]
        have h := replyRecvOnCore_blocks_capsDeliveredLong st epId tid c rid rf len
          badge executingCore ct ep0 rt ep rp stcb _ hLen hSzL hT hIpc hRO hW hNe
          hE hS hR' hA hEnq hRp hFree hStash hRecR (hReqOf stcb hS')
        rw [hTail]
        generalize endpointReplyRecvOnCore epId tid rid c
          { registers := longReplyRecvRegs rf st tid len, badge := badge } true
          executingCore st = r at h ⊢
        rcases r with e | ⟨a, st'⟩
        · cases h
        · simp only [Except.ok.injEq] at h ⊢
          exact h.symm
      · rfl
    · rfl
  · split
    · next hG =>
      unfold replyRecvLongDonatedCapsAdmits at hG
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hG
      obtain ⟨⟨hGr, hNoFault⟩, hF⟩ := hG
      subst hGr
      obtain ⟨ct, ep0, rt, ep, rp, hT, hIpc, hRO, hP, hSRes, hE, hS, hR', hA, hEnq, hRp,
        hStash, hRecR⟩ := replyRecvDonatedBlocks_spec hF
      have hTail : receiveQueueTailCode st epId = ep.recvTailCode := by
        simp only [receiveQueueTailCode, (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE]
      split
      · next stcb hS' =>
        split
        · next ct0 hTc0 =>
          obtain rfl : ct = ct0 := by
            rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp hTc0] at hT; cases hT; rfl
          unfold replyRecvLongRendezvousR
          rw [replyRecvTransferOnCore_of_no_fault (h := hNoFault)]
          have h := replyRecvOnCore_donated_capsDeliveredLong st epId tid c rid rf len badge
            executingCore ct ep0 rt ep rp stcb _ hLen hSzL hT hIpc hRO hSRes hP hE hS hR' hA
            hEnq hRp hStash hRecR (hReqOf stcb hS')
          rw [hTail]
          generalize endpointReplyRecvOnCore epId tid rid c
            { registers := longReplyRecvRegs rf st tid len, badge := badge } true
            executingCore st = r at h ⊢
          rcases r with e | ⟨a, st'⟩
          · cases h
          · simp only [Except.ok.injEq] at h ⊢
            exact h.symm
        · rfl
      · rfl
    · split
      · next hG =>
        unfold replyRecvLongUnheldCapsAdmits at hG
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hG
        obtain ⟨⟨hGr, hNoFault⟩, hF⟩ := hG
        subst hGr
        obtain ⟨ct, ep0, rt, ep, rp, hT, hIpc, hRO, hU, hNe, hE, hS, hR', hA, hEnq, hRp,
          hStash, hRecR, hTail⟩ := replyRecvUnheldBlocks_spec hF
        split
        · next stcb hS' =>
          split
          · next ct0 hTc0 =>
            obtain rfl : ct = ct0 := by
              rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp hTc0] at hT; cases hT; rfl
            unfold replyRecvLongRendezvousR
            rw [replyRecvTransferOnCore_of_no_fault (h := hNoFault)]
            have h := replyRecvOnCore_unheld_capsDeliveredLong st epId tid c rid rf len badge
              executingCore ct ep0 rt ep rp stcb _ hLen hSzL hT hIpc hRO hU hNe hE hS hR' hA
              hEnq hRp hStash hRecR (hReqOf stcb hS')
            rw [hTail]
            generalize endpointReplyRecvOnCore epId tid rid c
              { registers := longReplyRecvRegs rf st tid len, badge := badge } true
              executingCore st = r at h ⊢
            rcases r with e | ⟨a, st'⟩
            · cases h
            · simp only [Except.ok.injEq] at h ⊢
              exact h.symm
          · rfl
        · rfl
      · rfl

/-- The long arm whose reply pops a donation is the specification's path. -/
theorem replyRecvLongPopR_eq (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (rf : SeLe4n.RegisterFile) (len label : Nat) (executingCore : Concurrency.CoreId)
    (st : SystemState) (hLen : 5 ≤ len)
    (hSzL : ¬ (longReplyRecvRegs rf st tid len).size > maxMessageRegisters)
    (hReqOf : ∀ stcb, st.getTcb? tid = some stcb →
      replyCapRequest st tid true = frameCapRequestOf st stcb (routedExtraCaps rf)) :
    replyRecvLongPopR epId tid c rid badge grant rf len label executingCore st =
      replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st := by
  unfold replyRecvLongPopR
  split
  · next hG =>
    unfold replyRecvLongDonatedAdmits at hG
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hG
    obtain ⟨⟨hNoFault, hF⟩, hI⟩ := hG
    obtain ⟨ct, ep0, rt, ep, rp, hT, hIpc, hRO, hP, hSRes, hE, hS, hR, hA, hEnq, hRp,
      hStash, hRecR⟩ := replyRecvDonatedBlocks_spec hF
    have hTail : receiveQueueTailCode st epId = ep.recvTailCode := by
      simp only [receiveQueueTailCode, (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE]
    unfold replyRecvLongRendezvousR
    rw [replyRecvTransferOnCore_of_no_fault (h := hNoFault), hTail]
    have h := replyRecvOnCore_donated_deliveredLong st epId tid c rid rf len badge grant
      executingCore ct ep0 rt ep rp hLen hSzL hT hIpc hRO hSRes hP hE hS hR hA hEnq hRp hStash
      hRecR (replyRecvReplyInertW_spec hI hT)
    generalize endpointReplyRecvOnCore epId tid rid c
      { registers := longReplyRecvRegs rf st tid len, badge := badge } grant
      executingCore st = r at h ⊢
    rcases r with e | ⟨a, st'⟩
    · cases h
    · simp only [Except.ok.injEq] at h ⊢
      exact h.symm
  · split
    · next hG =>
      unfold replyRecvLongUnheldAdmits at hG
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hG
      obtain ⟨⟨hNoFault, hF⟩, hI⟩ := hG
      obtain ⟨ct, ep0, rt, ep, rp, hT, hIpc, hRO, hU, hNe, hE, hS, hR, hA, hEnq, hRp,
        hStash, hRecR, hTail⟩ := replyRecvUnheldBlocks_spec hF
      unfold replyRecvLongRendezvousR
      rw [replyRecvTransferOnCore_of_no_fault (h := hNoFault), hTail]
      have h := replyRecvOnCore_unheld_deliveredLong st epId tid c rid rf len badge grant
        executingCore ct ep0 rt ep rp hLen hSzL hT hIpc hRO hU hNe hE hS hR hA hEnq hRp hStash
        hRecR (replyRecvReplyInertW_spec hI hT)
      generalize endpointReplyRecvOnCore epId tid rid c
        { registers := longReplyRecvRegs rf st tid len, badge := badge } grant
        executingCore st = r at h ⊢
      rcases r with e | ⟨a, st'⟩
      · cases h
      · simp only [Except.ok.injEq] at h ⊢
        exact h.symm
    · exact replyRecvLongCapsR_eq epId tid c rid badge grant rf len label executingCore st hLen
        hSzL hReqOf

/-- The long reply-receive answering a caller carrying a fault: the long fault
answer (`performFaultAnswerLong`, the reply's words past MR0 read in the
replier's registers and IPC buffer) on each shape whose receive leg blocks in
place -- the plain one (`replyRecvBlocksFast`,
`performReplyRecvFaultAnswerLong`), the donated one (`replyRecvDonatedBlocks`,
`performReplyRecvDonatedFaultAnswerLong`) and the one answering a caller
recording no server (`replyRecvUnheldBlocks`,
`performReplyRecvUnheldFaultAnswerLong`); the specification's path otherwise
(`replyRecvLongFaultArmR_eq`).  The caller's words are read before the writes
and its TCB is not held across them. -/
@[inline] def replyRecvLongFaultArmR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (rf : SeLe4n.RegisterFile) (len label : Nat) (executingCore : Concurrency.CoreId) :
    RefusalCarrying Unit :=
  fun st =>
    match st.getTcb? c with
    | some ct =>
        if replyRecvBlocksFast st epId tid c rid then
          .ok ((), performReplyRecvFaultAnswerLong st c tid rid epId (receiveQueueTailCode st epId)
            executingCore ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0
            ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 rf len)
        else if replyRecvDonatedBlocks st epId tid c rid then
          .ok ((), performReplyRecvDonatedFaultAnswerLong st c tid rid
            ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) epId
            (receiveQueueTailCode st epId) executingCore ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0
            ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 rf len)
        else if replyRecvUnheldBlocks st epId tid c rid then
          .ok ((), performReplyRecvUnheldFaultAnswerLong st c tid rid
            ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) epId
            (receiveQueueTailCode st epId) executingCore ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0
            ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 rf len)
        else replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
    | none => replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st

/-- On a faulted caller the long arm is the specification's path. -/
theorem replyRecvLongFaultArmR_eq (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (rf : SeLe4n.RegisterFile) (len label : Nat) (executingCore : Concurrency.CoreId)
    (st : SystemState) (hLen : 4 ≤ len) (hF : threadHasPendingFault st c = true) :
    replyRecvLongFaultArmR epId tid c rid badge grant rf len label executingCore st =
      replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st := by
  unfold replyRecvLongFaultArmR
  split
  · next ct0 hTc0 =>
    have hTc0' := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc0
    obtain ⟨tf, hPF⟩ : ∃ tf, ct0.pendingFault = some tf := by
      unfold threadHasPendingFault at hF
      rw [hTc0] at hF
      exact Option.isSome_iff_exists.mp hF
    split
    · next hB =>
      obtain ⟨ct, ep0, rt, ep, rp, hT, hIpc, hRO, hW, hNe, hE, hS, hR, hA, hEnq, hRp,
        hFree, hStash, hRecR, hTail⟩ := replyRecvBlocksFast_spec hB
      obtain rfl : ct = ct0 := by
        rw [hT] at hTc0'; cases hTc0'; rfl
      obtain ⟨hEq, hStg⟩ := replyRecvTransferOnCore_fault_blocks_inPlaceLong st epId tid c rid
        label rf len badge grant executingCore ct ep0 rt ep rp tf hLen hPF hT hIpc hRO hW hNe hE
        hS hR hA hEnq hRp hFree hStash hRecR
      unfold replyRecvLongRendezvousR
      rw [hEq]
      simp only [CapTransferSummary.capInfo_empty]
      rw [hTail, hStg]
    · split
      · next hB =>
        obtain ⟨ct, ep0, rt, ep, rp, hT, hIpc, hRO, hP, hSRes, hE, hS, hR, hA, hEnq, hRp,
          hStash, hRecR⟩ := replyRecvDonatedBlocks_spec hB
        obtain rfl : ct = ct0 := by
          rw [hT] at hTc0'; cases hTc0'; rfl
        have hTail : receiveQueueTailCode st epId = ep.recvTailCode := by
          simp only [receiveQueueTailCode, (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE]
        obtain ⟨hEq, hStg⟩ := replyRecvTransferOnCore_fault_donated_inPlaceLong st epId tid c rid
          label rf len badge grant executingCore ct ep0 rt ep rp tf hLen hPF hT hIpc hRO hSRes hP
          hE hS hR hA hEnq hRp hStash hRecR
        unfold replyRecvLongRendezvousR
        rw [hEq]
        simp only [CapTransferSummary.capInfo_empty]
        rw [hTail, hStg]
      · split
        · next hB =>
          obtain ⟨ct, ep0, rt, ep, rp, hT, hIpc, hRO, hU, hNe, hE, hS, hR, hA, hEnq, hRp,
            hStash, hRecR, hTail⟩ := replyRecvUnheldBlocks_spec hB
          obtain rfl : ct = ct0 := by
            rw [hT] at hTc0'; cases hTc0'; rfl
          obtain ⟨hEq, hStg⟩ := replyRecvTransferOnCore_fault_unheld_inPlaceLong st epId tid c
            rid label rf len badge grant executingCore ct ep0 rt ep rp tf hLen hPF hT hIpc hRO hU
            hNe hE hS hR hA hEnq hRp hStash hRecR
          unfold replyRecvLongRendezvousR
          rw [hEq]
          simp only [CapTransferSummary.capInfo_empty]
          rw [hTail, hStg]
        · rfl
  · rfl

/-- The checked long reply-receive once its reply capability resolved to reply
object `rid`, answering caller `c`: the reply leg's flow gate, then a caller
carrying a fault answered by the long fault answer (`replyRecvLongFaultArmR`, in
place when the receive blocks), and for a caller carrying no fault when the
reply-receive may block in place
(`replyRecvBlocksFast`) and its reply leg transfers no capability
(`replyRecvReplyInertW`), the in-place delivery
(`performReplyRecvBlockDeliveredLong`); otherwise the transferring arm
(`replyRecvLongCapsR`), which runs the transfer in place or the
specification's path. -/
@[inline] def replyRecvLongResolvedR (ctx : LabelingContext) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (rf : SeLe4n.RegisterFile) (len label : Nat) (executingCore : Concurrency.CoreId) :
    RefusalCarrying Unit :=
  fun st =>
    if securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf c) then
      if threadHasPendingFault st c then
        replyRecvLongFaultArmR epId tid c rid badge grant rf len label executingCore st
      else if replyRecvBlocksFast st epId tid c rid && replyRecvReplyInertW st tid c grant then
        .ok ((), performReplyRecvBlockDeliveredLong st c tid rid epId (receiveQueueTailCode st epId)
          rf len badge executingCore)
      else replyRecvLongPopR epId tid c rid badge grant rf len label executingCore st
    else .error (.replyCapInvalid, st)

/-- The long reply-receive's general arm, its words read where it runs. -/
@[inline] def endpointReplyRecvLongGeneralR (ctx : LabelingContext) (rf : SeLe4n.RegisterFile)
    (len extraCaps label : Nat) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (cap : Capability) : RefusalCarrying Unit :=
  fun st => endpointReplyRecvCheckedArmGeneralR ctx
    { length := len, extraCaps := extraCaps, label := label } (longReplyRegs st tid rf len) tid
    executingCore cap st

/-- The checked reply-receive arm for a message of `len` words, more than four,
refusing in the state it was handed (`endpointReplyRecvLongCheckedArmR_eq`).
The reply capability at MR0 is resolved in continuation form; a reply-receive
that answers an unfaulted caller and then blocks writes in place, copying the
replier's overflow words into the caller's buffer
(`replyRecvOnCore_blocks_deliveredLong`), as seL4's `doReplyTransfer` does. -/
@[inline] def endpointReplyRecvLongCheckedArmR (ctx : LabelingContext) (rf : SeLe4n.RegisterFile)
    (len _extraCaps label : Nat) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (cap : Capability) : RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object epId =>
      if !endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) then
        .error (.flowDenied, st)
      else
        resolveReplyRecvK st tid len
          (SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf
            (SeLe4n.arm64DefaultLayout.msgRegs[0]'(Nat.lt_of_lt_of_eq (by decide : 0 < 4) rfl))))
          (fun e => .error (e, st))
          (fun rid c badge grant =>
            replyRecvLongResolvedR ctx epId tid c rid badge grant rf len label executingCore st)
    | _ => .error (.invalidCapability 0, st)

theorem endpointReplyRecvLongCheckedArmR_eq_general (ctx : LabelingContext)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability)
    (st : SystemState)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 =
      .replyRecvLong capAddr mi)
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w)
    (hRf : ∀ stcb, st.getTcb? tid = some stcb → stcb.registerContext = rf) :
    endpointReplyRecvLongCheckedArmR ctx rf mi.length mi.extraCaps mi.label tid executingCore cap
        st =
      endpointReplyRecvLongGeneralR ctx rf mi.length mi.extraCaps mi.label tid executingCore cap
        st := by
  obtain ⟨hGt, hMax, -⟩ :=
    Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReplyRecvLong st tid _ rf 32
      capAddr mi hR
  have hSz4 : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  rw [hSz4] at hGt
  have hExt : extractMessageRegisters (longReplyRegs st tid rf mi.length)
      { length := mi.length, extraCaps := mi.extraCaps, label := mi.label } =
      (longSendMessage SeLe4n.arm64DefaultLayout rf st tid mi.length none).registers :=
    congrArg IpcMessage.registers
      (longMessageDecode_message .replyRecv st tid rf capAddr mi none (by omega) hMax)
  have hM : ∀ badge : Option SeLe4n.Badge,
      ({ registers := (longSendMessage SeLe4n.arm64DefaultLayout rf st tid mi.length none).registers.extract
          1 (longSendMessage SeLe4n.arm64DefaultLayout rf st tid mi.length none).registers.size,
         badge := badge } : IpcMessage) =
      { registers := longReplyRecvRegs rf st tid mi.length, badge := badge } := fun _ => rfl
  unfold endpointReplyRecvLongCheckedArmR endpointReplyRecvLongGeneralR
    endpointReplyRecvCheckedArmGeneralR
  split
  · next epId hTgt =>
    split
    · rfl
    · rw [resolveReplyRecvK_eq st tid mi.length _ (longReplyRegs st tid rf mi.length) _ _
        (fun _ => by
          simp only [longReplyRegs]
          rw [Array.getElem?_append_left (by simp [Architecture.regMessageRegs, hSz4])]
          simp [Architecture.regMessageRegs, hSz4, SeLe4n.readReg_eq_word, SeLe4n.CPtr.ofWord])]
      cases resolveReplyRecvReplyR st tid mi.length (longReplyRegs st tid rf mi.length) with
      | error e => rfl
      | ok r =>
        obtain ⟨rid, c, badge, grant⟩ := r
        simp only [replyRecvLongResolvedR, hExt, hM]
        split
        · split
          · next hFlt =>
            rw [replyRecvLongFaultArmR_eq epId tid c rid badge grant rf mi.length mi.label
              executingCore st (by omega) hFlt]
            rfl
          · next hFlt =>
            have hNoFault : threadHasPendingFault st c = false := Bool.eq_false_iff.mpr hFlt
            split
            · next hG =>
              simp only [Bool.and_eq_true] at hG
              obtain ⟨hF, hI⟩ := hG
              obtain ⟨ct, ep0, rt, ep, rp, hT, hIpc, hRO, hW, hNe, hE, hS, hR, hA, hEnq, hRp,
                hFree, hStash, hRecR, hTail⟩ := replyRecvBlocksFast_spec hF
              have hInert := replyRecvReplyInertW_spec hI hT
              rw [replyRecvTransferOnCore_of_no_fault (h := hNoFault),
                replyRecvOnCore_blocks_inPlace st epId tid c rid _ _ _ ct ep0 rt ep rp ?_ hT hIpc
                  hRO hW hNe hE hS hR hA hEnq hRp hFree hStash hRecR hInert]
              · simp only [CapTransferSummary.capInfo_empty]
                rw [hTail, replyRecvOnCore_blocks_deliveredLong st epId tid c rid rf mi.length badge
                  executingCore ct ep0 rt ep rp (by omega) hT hIpc hW hNe hE hR hA hEnq hRp hFree
                  hStash hRecR]
              · show ¬ (longReplyRecvRegs rf st tid mi.length).size > maxMessageRegisters
                rw [longReplyRecvRegs_size rf st tid mi.length (by omega)]; omega
            · have hSzL : ¬ (longReplyRecvRegs rf st tid mi.length).size > maxMessageRegisters := by
                rw [longReplyRecvRegs_size rf st tid mi.length (by omega)]; omega
              rw [replyRecvLongPopR_eq epId tid c rid badge grant rf mi.length mi.label executingCore
                st (by omega) hSzL (fun stcb hS' => by
                  have hReq := replyCapRequest_of_routedReplyLong st tid stcb rf capAddr mi .replyRecv
                    true hS' (hRf stcb hS') (.inr ⟨hR, rfl⟩) hRead
                  simp only [↓reduceIte] at hReq
                  exact hReq)]
              rfl
        · rfl
  · rfl

/-- The long reply-receive arm is the specification's. -/
theorem endpointReplyRecvLongCheckedArmR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (st : SystemState)
    (hRR : decoded.syscallId = .replyRecv)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 =
      .replyRecvLong capAddr decoded.msgInfo)
    (hRegs : longReplyRegs st tid rf decoded.msgInfo.length = decoded.msgRegs)
    (hCaller : gate.callerId = tid)
    (hRoot : gate.cspaceRoot = callerCspaceRoot st tid)
    (hDepth : gate.capDepth = callerCspaceDepth st tid)
    (hRead : ∀ j, j < decoded.msgInfo.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w)
    (hRf : ∀ stcb, st.getTcb? tid = some stcb → stcb.registerContext = rf) :
    endpointReplyRecvLongCheckedArmR ctx rf decoded.msgInfo.length decoded.msgInfo.extraCaps
        decoded.msgInfo.label tid executingCore cap st =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap)
        st := by
  rw [endpointReplyRecvLongCheckedArmR_eq_general ctx rf capAddr decoded.msgInfo tid executingCore
    cap st hR hRead hRf]
  unfold endpointReplyRecvLongGeneralR
  rw [hRegs]
  exact endpointReplyRecvCheckedArmGeneralR_eq ctx decoded tid executingCore gate cap st hRR
    hCaller hRoot hDepth

/-- The long reply-receive's slot check, gate, arm and taint step on the
capability its operand resolved to (`endpointReplyRecvLongCheckedArmR`), its
taint the short reply-receive's (`replyRecvTaintStep`).  Every refusal carries
the state it was handed (`replyRecvLongOperandArmThenTaintR_eq`). -/
@[inline] def replyRecvLongOperandArmThenTaintR (ctx : LabelingContext)
    (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (requiredRight : AccessRight)
    (operand : Option Capability) : RefusalCarrying Unit :=
  fun st =>
    match operand with
    | none => .error (.invalidCapability 0, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedKernelObject cap then .error (.invalidCapability 0, st)
        else if !syscallTargetAccepted .replyRecv st cap then .error (.invalidCapability 0, st)
        else if cap.hasRight requiredRight then
          let sourceCode := receiveTaintSourceCode st cap
          let callerCode := replyRecvTaintCallerCodeOf st tid cap SeLe4n.arm64DefaultLayout rf len
          withTaintWordsAt st (threadObjOfCode sourceCode) fun a0 a1 a2 a3 a4 a5 a6 a7 ac as =>
          withTaintWordsAt st tid.toObjId fun b0 b1 b2 b3 b4 b5 b6 b7 bc bs =>
          match endpointReplyRecvLongCheckedArmR ctx rf len extraCaps label tid executingCore
              cap st with
          | .error refusal => .error refusal
          | .ok ((), stPost) =>
              .ok ((), replyRecvTaintStep sourceCode callerCode tid
                ⟨a0, a1, a2, a3, a4, a5, a6, a7, ac, as⟩ ⟨b0, b1, b2, b3, b4, b5, b6, b7, bc, bs⟩
                stPost)
        else .error (syscallMissingRightError .replyRecv, st)

theorem replyRecvLongOperandArmThenTaintR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId)
    (preEpoch : Nat) (preLength : Nat)
    (st : SystemState) (tcb : TCB) (rootCn : CNode) (ref : CSpaceAddr)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr)
    (hRR : decoded.syscallId = .replyRecv)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 =
      .replyRecvLong capAddr decoded.msgInfo)
    (hRegs : longReplyRegs st tid rf decoded.msgInfo.length = decoded.msgRegs)
    (hTcb : st.getObject? tid.toObjId = some (.tcb tcb))
    (hRoot : st.getObject? tcb.cspaceRoot = some (.cnode rootCn))
    (hRef : resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth st = .ok ref)
    (hRead : ∀ j, j < decoded.msgInfo.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w)
    (hRf : ∀ stcb, st.getTcb? tid = some stcb → stcb.registerContext = rf) :
    replyRecvLongOperandArmThenTaintR ctx rf decoded.msgInfo.length decoded.msgInfo.extraCaps
        decoded.msgInfo.label tid executingCore
        (syscallRequiredRight decoded.syscallId) (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore
        { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
          capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
        (syscallTaintPlan st tid decoded) preEpoch preLength st.declassificationTaint) st := by
  have hOperand := syscallOperandCap?_of_resolved st tid _ tcb rootCn ref hTcb hRoot hRef
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel,
    hRR, ↓reduceIte, syscallInvokeTyped, syscallResolveCap, hRef]
  simp only [replyRecvTaintStep_eq st tid decoded hRR SeLe4n.arm64DefaultLayout rf tcb rootCn hTcb
    hRoot _ (Or.inr (by decide)) hRegs
    (wS := fun cap => st.taintWordsAt (threadObjOfCode (receiveTaintSourceCode st cap)))
    (wT := st.taintWordsAt tid.toObjId) (hS := fun _ => decode_taintWordsAt st _)
    (hT := decode_taintWordsAt st _), hOperand]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [replyRecvLongOperandArmThenTaintR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hType : syscallTargetAccepted .replyRecv st cap = false
      · simp only [hIdle, hType, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      replace hType : syscallTargetAccepted .replyRecv st cap = true := by simpa using hType
      by_cases hRight : cap.hasRight (syscallRequiredRight .replyRecv) = true
      · simp only [hIdle, hType, Bool.not_true, Bool.false_eq_true, hRight, ↓reduceIte, Bool.false_eq_true, withTaintWordsAt_eq,
          TaintWords.mk_fields]
        rw [endpointReplyRecvLongCheckedArmR_eq ctx decoded tid executingCore
          { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
            capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
          cap rf capAddr st hRR hR hRegs rfl (by simp only [callerCspaceRoot, hTcb])
          (by simp only [callerCspaceDepth, hTcb, hRoot]) hRead hRf]
        simp only [RefusalCarrying.ofKernel, hRR]
        rcases dispatchWithCapChecked ctx decoded tid executingCore
          { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
            capDepth := rootCn.depth, requiredRight := syscallRequiredRight .replyRecv }
          cap st with _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hType, Bool.not_true, Bool.false_eq_true, hRight, ↓reduceIte, Bool.false_eq_true]

/-- The long reply-receive's operand dispatch (`dispatchReplyRecvLongCheckedR_eq`).
A specification: the compiled entry runs the arm out of line. -/
noncomputable def dispatchReplyRecvLongCheckedR (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore
    (replyRecvLongOperandArmThenTaintR ctx rf len extraCaps label tid executingCore
      (syscallRequiredRight .replyRecv))

theorem dispatchReplyRecvLongCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (st : SystemState)
    (hRR : decoded.syscallId = .replyRecv)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 =
      .replyRecvLong capAddr decoded.msgInfo)
    (hRegs : longReplyRegs st tid rf decoded.msgInfo.length = decoded.msgRegs)
    (hRead : ∀ j, j < decoded.msgInfo.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w)
    (hRf : ∀ stcb, st.getTcb? tid = some stcb → stcb.registerContext = rf) :
    dispatchReplyRecvLongCheckedR ctx decoded.capAddr rf decoded.msgInfo.length
        decoded.msgInfo.extraCaps decoded.msgInfo.label tid executingCore st =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) st := by
  apply dispatchOperandCheckedR_eq_at ctx decoded tid executingCore _ (by rw [hRR]; decide) st
  intro tcb rootCn ref hTcb hRoot hRef
  have hArm := replyRecvLongOperandArmThenTaintR_eq ctx decoded tid executingCore
    st.declassificationAuditEpoch st.declassificationAudit.length
    st tcb rootCn ref rf capAddr hRR hR hRegs hTcb hRoot hRef hRead hRf
  simp only [hRR] at hArm ⊢
  exact hArm

end SeLe4n.Kernel
