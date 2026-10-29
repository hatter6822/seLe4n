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
    Except KernelError (SeLe4n.ReplyId × SeLe4n.ThreadId × Option SeLe4n.Badge) :=
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
      match syscallLookupCap gate st with
      | .error e => .error e
      | .ok (rcap, _) =>
          match extractReplyId rcap with
          | .error e => .error e
          | .ok rid =>
              match replyAnsweredCaller? st rid with
              | some prevCaller => .ok (rid, prevCaller, rcap.badge)
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
        | .ok (rid, prevCaller, replyBadge) =>
            let full := extractMessageRegisters regs mi
            let msg : IpcMessage :=
              { registers := full.extract 1 full.size, badge := replyBadge }
            if securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf prevCaller) then
              match endpointReplyRecvOnCore epId tid rid prevCaller msg (callerCspaceRoot st tid)
                  (SeLe4n.Slot.ofNat 0) executingCore st with
              | .ok (summary, st') =>
                  .ok ((), Architecture.stageDeliveredMessage st' tid summary.installedCount)
              | .error e => .error (e, st)
            else .error (.replyCapInvalid, st)
    | _ => .error (.invalidCapability, st)

theorem endpointReplyRecvCheckedArmGeneralR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (st : SystemState)
    (hRR : decoded.syscallId = .replyRecv)
    (hCaller : gate.callerId = tid)
    (hRoot : gate.cspaceRoot = callerCspaceRoot st tid)
    (hDepth : gate.capDepth = callerCspaceDepth st tid)
    (hSlot : decoded.capRecvSlot = SeLe4n.Slot.ofNat 0) :
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
        obtain ⟨rid, prevCaller, replyBadge⟩ := r
        simp only [← hRoot, hSlot]
        split
        · rcases endpointReplyRecvOnCore epId tid rid prevCaller _ gate.cspaceRoot
            (SeLe4n.Slot.ofNat 0) executingCore st with _ | ⟨summary, st'⟩ <;> rfl
        · rfl
  | _ => rfl

/-- The reply capability a reply-receive names, checked as
`resolveReplyRecvReplyR` checks it once its slot is found: present, not the idle
thread's, carrying the write right, naming a reply object with an outstanding
caller.  The reply object, its caller and the capability's badge go to `onOk`,
a refusal to `onErr`, so no `Except` or tuple cell is built. -/
@[inline] def replyRecvCapK {α : Type} (st : SystemState) (cap? : Option Capability)
    (onErr : KernelError → α)
    (onOk : SeLe4n.ReplyId → SeLe4n.ThreadId → Option SeLe4n.Badge → α) : α :=
  match cap? with
  | none => onErr .invalidCapability
  | some cap =>
      if SeLe4n.Kernel.capTargetsReservedIdleObject cap then onErr .invalidCapability
      else if !cap.hasRight .write then onErr .illegalAuthority
      else
        match cap.target with
        | .replyCap rid =>
            match replyAnsweredCaller? st rid with
            | some c => onOk rid c cap.badge
            | none => onErr .replyCapInvalid
        | _ => onErr .invalidCapability

/-- `resolveReplyRecvReplyR` in continuation form (`resolveReplyRecvK_eq`), on
the message length and the first message register: the slot is resolved
through `resolveCapAddressKUnrolled`, as the operand is.  WS-ZA ZA4.7. -/
@[inline] def resolveReplyRecvK {α : Type} (st : SystemState) (tid : SeLe4n.ThreadId)
    (len : Nat) (replyAddr : SeLe4n.CPtr) (onErr : KernelError → α)
    (onOk : SeLe4n.ReplyId → SeLe4n.ThreadId → Option SeLe4n.Badge → α) : α :=
  if len = 0 then onErr .replyCapInvalid else
  resolveCapAddressKUnrolled (callerCspaceRoot st tid) replyAddr
    (callerCspaceDepth st tid) st onErr
    (fun cnode slot =>
      replyRecvCapK st (SystemState.lookupSlotCap st { cnode := cnode, slot := slot })
        onErr onOk)

theorem resolveReplyRecvK_eq {α : Type} (st : SystemState) (tid : SeLe4n.ThreadId)
    (len : Nat) (replyAddr : SeLe4n.CPtr) (regs : Array SeLe4n.RegValue)
    (onErr : KernelError → α)
    (onOk : SeLe4n.ReplyId → SeLe4n.ThreadId → Option SeLe4n.Badge → α)
    (hReplyAddr : len ≠ 0 → regs[0]? = some ⟨replyAddr.toNat⟩) :
    resolveReplyRecvK st tid len replyAddr onErr onOk =
      match resolveReplyRecvReplyR st tid len regs with
      | .error e => onErr e
      | .ok (rid, c, b) => onOk rid c b := by
  unfold resolveReplyRecvK resolveReplyRecvReplyR
  by_cases h0 : len = 0
  · simp [h0]
  · have hR : requireMsgReg regs 0 = .ok ⟨replyAddr.toNat⟩ := by
      have h := hReplyAddr h0
      rw [Array.getElem?_eq_some_iff] at h
      obtain ⟨hs, hv⟩ := h
      simp only [requireMsgReg, hs, ↓reduceDIte, hv]
    have hL : (len == 0) = false := by simp [h0]
    simp only [h0, ↓reduceIte, hL, Bool.false_eq_true, hR, syscallLookupCap, syscallResolveCap,
      SeLe4n.CPtr.ofNat_toNat]
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
        by_cases hIdle : SeLe4n.Kernel.capTargetsReservedIdleObject cap = true
        · simp only [hIdle, ↓reduceIte]
        · by_cases hRight : cap.hasRight .write = true
          · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true, Bool.not_true]
            unfold extractReplyId
            cases cap.target <;> try rfl
            rename_i rid
            simp only []
            cases replyAnsweredCaller? st rid <;> rfl
          · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true, Bool.not_false]

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

/-- The checked reply-receive once its reply capability is resolved, through the
specification's path.  Out of line, so the reply's message record is built only
here. -/
@[noinline] def replyRecvRendezvousR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    match endpointReplyRecvOnCore epId tid rid c
        { registers := Architecture.regReplyRecvBody layout rf len, badge := badge }
        (callerCspaceRoot st tid) (SeLe4n.Slot.ofNat 0) executingCore st with
    | .ok (summary, st') =>
        .ok ((), Architecture.stageDeliveredMessage st' tid summary.installedCount)
    | .error e => .error (e, st)

/-- The checked reply-receive once its reply capability resolved to reply object
`rid`, answering caller `c` with badge `badge`: the reply leg's flow gate, then
the in-place path when it may be taken (`replyRecvBlocksFast`, a reply of at
most four words), the specification's otherwise. -/
@[inline] def replyRecvResolvedR (ctx : LabelingContext) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    if securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf c) then
      if decide (Architecture.regMessageLength layout len - 1 ≤ 4) &&
          replyRecvBlocksFast st epId tid c rid then
        .ok ((), performReplyRecvBlockDelivered st c tid rid epId (receiveQueueTailCode st epId)
          layout rf len badge executingCore)
      else replyRecvRendezvousR epId tid c rid badge layout rf len executingCore st
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
        let resolved := fun rid c badge =>
          replyRecvResolvedR ctx epId tid c rid badge layout rf len executingCore st
        resolveReplyRecvK st tid len
          (SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf (layout.msgRegs[0]'h0)))
          (fun e => .error (e, st)) resolved
      else endpointReplyRecvCheckedArmRegsR ctx layout rf len extraCaps label tid executingCore
          cap st
    | _ => .error (.invalidCapability, st)

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
            simp [Architecture.regMessageRegs, h0, SeLe4n.CPtr.ofWord_toNat,
              ← SeLe4n.readReg_val_eq_word])]
        cases resolveReplyRecvReplyR st tid len (Architecture.regMessageRegs layout rf) with
        | error e => rfl
        | ok r =>
          obtain ⟨rid, c, badge⟩ := r
          simp only [replyRecvResolvedR]
          split
          · next hFlow =>
            split
            · next hG =>
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hG
              obtain ⟨hSz, hF⟩ := hG
              obtain ⟨ct, ep0, rt, ep, rp, hT, hIpc, hRO, hW, hNe, hE, hS, hR, hA, hEnq, hRp,
                hFree, hStash, hRecR, hTail⟩ := replyRecvBlocksFast_spec hF
              have hSz4 : (Architecture.regReplyRecvBody layout rf len).size ≤ 4 := by
                rw [Architecture.regReplyRecvBody_size]; exact hSz
              have h := replyRecvOnCore_blocks_delivered st epId tid c rid
                { registers := Architecture.regReplyRecvBody layout rf len,
                  badge := badge } (callerCspaceRoot st tid) (SeLe4n.Slot.ofNat 0) executingCore
                ct ep0 rt ep rp (by simp only; unfold maxMessageRegisters; omega) hSz4 hT hIpc
                hRO hW hNe hE hS hR hA hEnq hRp hFree hStash hRecR
              rw [Architecture.returnFrameOfMessage_regReplyRecvBody,
                replyRecvOnCore_blocks_inPlace st epId tid c rid _ _ _ _ ct ep0 rt ep rp
                  (by simp only; unfold maxMessageRegisters; omega) hT hIpc hRO hW hNe hE hS hR
                  hA hEnq hRp hFree hStash hRecR] at h
              simp only [CapTransferSummary.installedCount_empty] at h
              rw [hTail, replyRecvOnCore_blocks_inPlace st epId tid c rid _ _ _ _ ct ep0 rt ep rp
                  ?_ hT hIpc hRO hW hNe hE hS hR hA hEnq hRp hFree hStash hRecR]
              · simp only [CapTransferSummary.installedCount_empty]
                have h2 := congrArg Prod.snd (Except.ok.inj h)
                dsimp only at h2
                rw [h2]
                rfl
              · show ¬ (Architecture.regReplyRecvBody layout rf len).size > maxMessageRegisters
                unfold maxMessageRegisters; omega
            · simp only [replyRecvRendezvousR]
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
    (hDepth : gate.capDepth = callerCspaceDepth st tid)
    (hSlot : decoded.capRecvSlot = SeLe4n.Slot.ofNat 0) :
    endpointReplyRecvCheckedArmR ctx layout rf decoded.msgInfo.length decoded.msgInfo.extraCaps
        decoded.msgInfo.label tid executingCore cap st =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap)
        st := by
  rw [endpointReplyRecvCheckedArmR_eq_general]
  unfold endpointReplyRecvCheckedArmRegsR
  rw [hRegs]
  exact endpointReplyRecvCheckedArmGeneralR_eq ctx decoded tid executingCore gate cap st hRR
    hCaller hRoot hDepth hSlot

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
    (hRegs : Architecture.regMessageRegs layout rf = decoded.msgRegs) :
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
        have hs : 0 < decoded.msgRegs.size := by
          rw [← hRegs]; simp [Architecture.regMessageRegs, h0]
        simp only [Architecture.SyscallArgDecode.decodeReplyRecvArgs, requireMsgReg, hs,
          ↓reduceDIte, bind, Except.bind, pure, Except.pure]
        congr 2
        simp only [← hRegs, Architecture.regMessageRegs, Array.getElem_map,
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
          rw [← hRegs]; simpa [Architecture.regMessageRegs] using h0
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
    (hRegs : Architecture.regMessageRegs layout rf = decoded.msgRegs)
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
        replyRecvReplyLegEdges_eq st tid decoded layout rf tcb rootCn hTcb hRoot hRegs,
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

/-- WS-ZA ZA5.12: the reply-receive's arm and taint step over the source words captured
before it, handed over as scalars.  Out of line, so each branch of the capture
(`withTaintWordsAt`) is one call with the words as arguments, and the compiler
builds no closure over them to share the arm between branches. -/
@[noinline] def replyRecvArmThenTaintWordsR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability)
    (sourceCode callerCode : Nat) (a0 a1 a2 a3 a4 a5 a6 a7 : UInt64) (ac : Nat) (as : Bool)
    (b0 b1 b2 b3 b4 b5 b6 b7 : UInt64) (bc : Nat) (bs : Bool) : RefusalCarrying Unit :=
  fun st =>
    match endpointReplyRecvCheckedArmR ctx layout rf len extraCaps label tid executingCore cap st with
    | .error refusal => .error refusal
    | .ok ((), stPost) =>
        .ok ((), replyRecvTaintStep sourceCode callerCode tid ⟨a0, a1, a2, a3, a4, a5, a6, a7, ac, as⟩ ⟨b0, b1, b2, b3, b4, b5, b6, b7, bc, bs⟩ stPost)

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
    | none => .error (.invalidCapability, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedIdleObject cap then .error (.invalidCapability, st)
        else if cap.hasRight requiredRight then
          let sourceCode := receiveTaintSourceCode st cap
          let callerCode := replyRecvTaintCallerCodeOf st tid cap layout rf len
          withTaintWordsAt st (threadObjOfCode sourceCode) fun a0 a1 a2 a3 a4 a5 a6 a7 ac as =>
          withTaintWordsAt st tid.toObjId fun b0 b1 b2 b3 b4 b5 b6 b7 bc bs =>
          replyRecvArmThenTaintWordsR ctx layout rf len extraCaps label tid executingCore cap
            sourceCode callerCode a0 a1 a2 a3 a4 a5 a6 a7 ac as b0 b1 b2 b3 b4 b5 b6 b7 bc bs st
        else .error (.illegalAuthority, st)

theorem replyRecvOperandArmThenTaintR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId)
    (preEpoch : Nat) (preLength : Nat)
    (st : SystemState) (tcb : TCB) (rootCn : CNode) (ref : CSpaceAddr)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (hRR : decoded.syscallId = .replyRecv)
    (hRegs : Architecture.regMessageRegs layout rf = decoded.msgRegs)
    (hSlot : decoded.capRecvSlot = SeLe4n.Slot.ofNat 0)
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
    hRR, syscallChecksTargetFirst, Bool.false_eq_true, ↓reduceIte, syscallInvoke,
    syscallLookupCap, syscallResolveCap, hRef]
  simp only [replyRecvTaintStep_eq st tid decoded hRR layout rf tcb rootCn hTcb hRoot hRegs
    (wS := fun cap => st.taintWordsAt (threadObjOfCode (receiveTaintSourceCode st cap)))
    (wT := st.taintWordsAt tid.toObjId) (hS := fun _ => decode_taintWordsAt st _)
    (hT := decode_taintWordsAt st _), hOperand]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [replyRecvOperandArmThenTaintR, replyRecvArmThenTaintWordsR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedIdleObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hRight : cap.hasRight (syscallRequiredRight .replyRecv) = true
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true, withTaintWordsAt_eq,
          TaintWords.mk_fields]
        rw [endpointReplyRecvCheckedArmR_eq ctx decoded tid executingCore
          { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
            capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
          cap layout rf st hRR hRegs rfl (by simp only [callerCspaceRoot, hTcb])
          (by simp only [callerCspaceDepth, hTcb, hRoot]) hSlot]
        simp only [RefusalCarrying.ofKernel, hRR]
        rcases dispatchWithCapChecked ctx decoded tid executingCore
          { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
            capDepth := rootCn.depth, requiredRight := syscallRequiredRight .replyRecv }
          cap st with _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]

/-- WS-ZA ZA4.7: the reply-receive's dispatch: `dispatchOperandCheckedR` with
the reply-receive's arm (`dispatchReplyRecvCheckedR_eq`). -/
@[inline] def dispatchReplyRecvCheckedR (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
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
    (hRegs : Architecture.regMessageRegs layout rf = decoded.msgRegs)
    (hSlot : decoded.capRecvSlot = SeLe4n.Slot.ofNat 0) :
    dispatchReplyRecvCheckedR ctx decoded.capAddr layout rf decoded.msgInfo.length
        decoded.msgInfo.extraCaps decoded.msgInfo.label tid executingCore =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) := by
  apply dispatchOperandCheckedR_eq ctx decoded tid executingCore _ (by rw [hRR]; rfl)
    (by rw [hRR]; decide)
  intro st tcb rootCn ref hTcb hRoot hRef
  have hArm := replyRecvOperandArmThenTaintR_eq ctx decoded tid executingCore
    st.declassificationAuditEpoch st.declassificationAudit.length
    st tcb rootCn ref layout rf hRR hRegs hSlot hTcb hRoot hRef
  simp only [hRR] at hArm ⊢
  exact hArm

end SeLe4n.Kernel
