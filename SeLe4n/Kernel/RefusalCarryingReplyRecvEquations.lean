-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RefusalCarryingReplyRecv
import SeLe4n.Kernel.RefusalCarryingReplyRecvAfterReply

/-!
# Reply-receive's compiled arms, equal to their specification

The proofs over `RefusalCarryingReplyRecv`'s definitions, kept apart from them
as the Operations/Invariant split keeps a subsystem's proofs apart from its
transitions: each compiled reply-receive arm's equality to the specification's
path (`endpointReplyRecvCheckedArmR_eq`, `dispatchReplyRecvCheckedR_eq`, and
their long forms), and the codes and checks those arms read on the pre-state
(`replyRecvBlockArmCode_spec`, `replyRecvTakeArmCode_spec`, ...).  No
definition the kernel runs is here: the arms are all in
`RefusalCarryingReplyRecv`.

No proof here asks for a match's equations: a match's splitter is compiled
code, generated in the module whose proof first needs it, so a `split` on a
match, or a `simp` that meets a match it cannot reduce, would compile one into
this module.  The proofs case on each match's discriminant (`cases h : e`),
reduce the matches on constructors with `dsimp`, and rewrite with `rw` or a
`simp -iota` that never visits a match.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open Architecture.RegisterDecode
open Architecture.SyscallArgDecode

theorem resolveReplyRecvReplyR_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (decoded : SyscallDecodeResult)
    (hCaller : gate.callerId = tid)
    (hRoot : gate.cspaceRootCap = callerCspaceRoot st tid) :
    resolveReplyRecvReplyR st tid decoded.replyCPtr = resolveReplyRecvReply gate decoded st := by
  unfold resolveReplyRecvReplyR resolveReplyRecvReply
  rcases gate with ⟨c, r, a, rr⟩
  simp only at hCaller hRoot
  subst hCaller hRoot
  rfl

/-- A reply-receive whose reply answers no caller (`replyRecvRepliesToNoOne`)
resolves to no caller through its own CSpace root (`callerReplyGate`). -/
theorem resolveReplyRecvReply_of_repliesToNoOne {st : SystemState} {tid : SeLe4n.ThreadId}
    {decoded : SyscallDecodeResult}
    (h : replyRecvRepliesToNoOne st tid decoded.replyCPtr = true) :
    resolveReplyRecvReply (callerReplyGate st tid decoded) decoded st = .ok none := by
  rw [← resolveReplyRecvReplyR_eq st tid (callerReplyGate st tid decoded) decoded rfl rfl]
  unfold replyRecvRepliesToNoOne at h
  revert h
  cases resolveReplyRecvReplyR st tid decoded.replyCPtr with
  | error e => intro h; cases h
  | ok r =>
    cases r with
    | none => intro _; rfl
    | some _ => intro h; cases h

/-- **A reply-receive whose reply half is skipped** (WS-SX SX6.1, SX7.2; seL4-MCS
`SysReplyRecv`, whose `handleInvocation` on the reply capability runs with
`isBlocking = false` and whose `doReplyTransfer` returns when no caller waits on
the reply, after which `handleRecv` still runs) is the receive arm on the reply
register's capability (`endpointReceiveCheckedArmR`), which cancels its busy
reply and reports the cancelled state as `.receive` does. -/
theorem replyRecvSkipReply_eq (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (st : SystemState) (epId : SeLe4n.ObjId)
    (hRR : decoded.syscallId = .replyRecv)
    (hCaller : gate.callerId = tid)
    (hRoot : gate.cspaceRootCap = callerCspaceRoot st tid)
    (hTgt : cap.target = .object epId)
    (hFlow : endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) = true) :
    endpointReceiveCheckedArmR ctx tid true decoded.replyCPtr executingCore cap st =
      match receiveResolvedArm ctx decoded gate tid epId executingCore
          (cancelRecvBusyReply ctx tid gate decoded executingCore st) with
      | .ok r => .ok r
      | .error e => .error (e, cancelRecvBusyReply ctx tid gate decoded executingCore st) :=
  endpointReceiveCheckedArmR_eq_resolved ctx decoded tid executingCore gate cap st epId _ _
    hCaller hRoot (by rw [receiveReplyAddr?_of_replyRecv' hRR]; rfl) hTgt hFlow

theorem replyRecvSkipReport_eq (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (st : SystemState) (epId : SeLe4n.ObjId)
    (hRR : decoded.syscallId = .replyRecv)
    (hRoot : gate.cspaceRootCap = callerCspaceRoot st tid)
    (hTgt : cap.target = .object epId)
    (hFlow : endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) = true) :
    receiveArmReport ctx tid true decoded.replyCPtr executingCore cap st =
      cancelRecvBusyReply ctx tid gate decoded executingCore st := by
  unfold receiveArmReport cancelReceiveArmBusyReply cancelRecvBusyReply
  rw [hTgt]
  dsimp only
  rw [hFlow, Bool.not_true, if_neg Bool.false_ne_true,
    receiveArmHolderCode_eq ctx tid _ gate decoded _ _ st hRoot
      (by rw [receiveReplyAddr?_of_replyRecv' hRR]; rfl)]
  rfl

theorem endpointReplyRecvCheckedArmGeneralR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (st : SystemState)
    (hRR : decoded.syscallId = .replyRecv)
    (hCaller : gate.callerId = tid)
    (hRoot : gate.cspaceRootCap = callerCspaceRoot st tid) :
    endpointReplyRecvCheckedArmGeneralR ctx decoded.msgInfo decoded.msgRegs
        decoded.replyCPtr tid executingCore cap st =
      RefusalCarrying.ofKernelReporting
        (replyRecvArmReport ctx tid decoded.msgInfo decoded.msgRegs
          decoded.replyCPtr executingCore cap)
        (dispatchWithCapChecked ctx decoded tid executingCore gate cap) st := by
  unfold RefusalCarrying.ofKernelReporting dispatchWithCapChecked dispatchCapabilityOnly
    endpointReplyRecvCheckedArmGeneralR replyRecvArmReport
  rw [hRR]
  dsimp only
  cases hTgt : cap.target with
  | object epId =>
    dsimp only
    cases hFlow : endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid)
    case false =>
      have hRA : receiveArmReport ctx tid true decoded.replyCPtr executingCore cap st = st := by
        unfold receiveArmReport; rw [hTgt]; dsimp only; rw [hFlow]; rfl
      have hAR : replyRecvAnsweringReport ctx tid decoded.msgInfo decoded.msgRegs
          decoded.replyCPtr executingCore cap st = st := by
        unfold replyRecvAnsweringReport; rw [hTgt]; dsimp only; rw [hFlow]; rfl
      rw [hRA, hAR, ite_self]
      cases callerExtraCapsFault? st tid decoded.msgInfo.extraCaps <;> rfl
    rw [Bool.not_true, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
      callerExtraCapsFailK_eq]
    have hSkip := replyRecvSkipReply_eq ctx decoded tid executingCore gate cap st epId hRR hCaller
      hRoot hTgt hFlow
    have hRep := replyRecvSkipReport_eq ctx decoded tid executingCore gate cap st epId hRR hRoot hTgt
      hFlow
    cases hXc : callerExtraCapsFault? st tid decoded.msgInfo.extraCaps with
    | some xf =>
      dsimp only
      rw [hSkip, hRep]
      cases receiveResolvedArm ctx decoded gate tid epId executingCore
        (cancelRecvBusyReply ctx tid gate decoded executingCore st) <;> rfl
    | none =>
    dsimp only
    rw [hRep]
    unfold replyRecvRepliesToNoOne replyRecvReplyRefused replyRecvAnsweringReport
      replyRecvAnsweredReply?
    rw [hTgt]
    dsimp only
    rw [hFlow, ← resolveReplyRecvReplyR_eq st tid gate decoded hCaller hRoot]
    cases hS : resolveReplyRecvReplyR st tid decoded.replyCPtr with
    | error e => rfl
    | ok r =>
      cases r with
      | none =>
        dsimp only
        rw [hSkip]
        cases receiveResolvedArm ctx decoded gate tid epId executingCore
          (cancelRecvBusyReply ctx tid gate decoded executingCore st) <;> rfl
      | some r =>
        obtain ⟨rid, prevCaller, replyBadge, replyGrant⟩ := r
        dsimp only
        cases hAns : replyRecvReplyAnswers ctx st tid prevCaller <;>
          simp -iota only [↓reduceIte, Bool.not_true, Bool.not_false, Bool.false_or] <;>
          (try dsimp only)
        case true =>
          cases hSig : receiveCompletesSignal ctx st tid <;>
            (try simp -iota only [↓reduceIte]) <;> (try dsimp only)
          case true =>
            rcases replyRecvCompletesSignalArm ctx tid prevCaller decoded.msgInfo.label _
              replyGrant executingCore st with _ | ⟨⟨⟩, st'⟩ <;> rfl
          case false =>
            rw [replyRecvTransferOnCoreR_eq_match]
            rcases replyRecvTransferOnCore epId tid rid prevCaller decoded.msgInfo.label _
              replyGrant executingCore st with
              _ | ⟨summary, st'⟩ <;> rfl
        case false =>
          rw [hSkip]
          cases receiveResolvedArm ctx decoded gate tid epId executingCore
            (cancelRecvBusyReply ctx tid gate decoded executingCore st) <;> rfl
  | _ =>
    have hRA : receiveArmReport ctx tid true decoded.replyCPtr executingCore cap st = st := by
      unfold receiveArmReport; rw [hTgt]
    have hAR : replyRecvAnsweringReport ctx tid decoded.msgInfo decoded.msgRegs
        decoded.replyCPtr executingCore cap st = st := by
      unfold replyRecvAnsweringReport; rw [hTgt]
    rw [hRA, hAR, ite_self]
    cases callerExtraCapsFault? st tid decoded.msgInfo.extraCaps <;> rfl

/-- The continuation form is the resolution, for an `onOk` that reads the
capability it is handed only through the facts the resolution reports: it names
reply object `rid`, whose caller is `c`, and carries the badge and grant right
passed beside it (`onOk'`). -/
theorem resolveReplyRecvK_eq_of {α : Type} (st : SystemState) (tid : SeLe4n.ThreadId)
    (replyAddr : SeLe4n.CPtr) (answers : SeLe4n.ThreadId → Bool) (onErr : KernelError → α)
    (onNone : Unit → α)
    (onOk : Capability → SeLe4n.ReplyId → SeLe4n.ThreadId → Option SeLe4n.Badge → Bool → α)
    (onOk' : SeLe4n.ReplyId → SeLe4n.ThreadId → Option SeLe4n.Badge → Bool → α)
    (hOk : ∀ cap rid c, cap.target = .replyCap rid → replyAnsweredCaller? st rid = some c →
      answers c = true →
      onOk cap rid c cap.badge (cap.rights.mem .grant) =
        onOk' rid c cap.badge (cap.rights.mem .grant)) :
    resolveReplyRecvK st tid replyAddr answers onErr onNone onOk =
      match resolveReplyRecvReplyR st tid replyAddr with
      | .error e => onErr e
      | .ok none => onNone ()
      | .ok (some (rid, c, b, g)) => if answers c then onOk' rid c b g else onNone () := by
  unfold resolveReplyRecvK resolveReplyRecvReplyR lookupReplyCap syscallLookupCap syscallResolveCap
    SyscallGate.lookupSlot
  dsimp only
  cases callerCspaceRoot st tid with
  | none => rfl
  | some root =>
  dsimp only
  rw [lookupSlotFromK_eq]
  cases lookupSlotFrom root replyAddr st with
  | error e =>
    dsimp only
    unfold KernelError.capFaultLookup
    dsimp only
    rw [LookupFault.ofWords_word]
  | ok ref =>
    unfold replyRecvCapK
    dsimp only
    cases SystemState.lookupSlotCap st ref with
    | none => rfl
    | some cap =>
      dsimp only
      cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap
      case true => rfl
      simp -iota only [↓reduceIte, Bool.false_eq_true]
      dsimp only
      cases hRight : cap.hasRight .write
      all_goals simp -iota only [↓reduceIte, Bool.false_eq_true, Bool.not_false,
        Bool.not_true]
      case false => rfl
      dsimp only
      cases hT : cap.target
      all_goals try rfl
      rename_i rid
      unfold replyRecvAnsweredCaller?
      dsimp only
      cases hA : replyAnsweredCaller? st rid with
      | none => rfl
      | some c =>
        dsimp only
        cases hC : answers c
        case false => rfl
        exact hOk cap rid c hT hA hC

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
  simp -iota only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hNe, hC⟩, hE⟩, hRp⟩ := h
  have hNe' : tid ≠ c := fun e => by subst e; simp at hNe
  cases hTc : st.getTcb? c with
  | none => rw [hTc] at hC; cases hC
  | some ct =>
  rw [hTc] at hC
  dsimp only at hC
  simp -iota only [Bool.and_eq_true] at hC
  obtain ⟨⟨hIpc, hRO⟩, hW⟩ := hC
  obtain ⟨ep0, hIpc'⟩ : ∃ ep0, ct.ipcState = .blockedOnReply ep0 (some tid) := by
    revert hIpc
    cases hS : ct.ipcState with
    | blockedOnReply ep0 server =>
      cases server with
      | none => intro e; cases e
      | some server =>
        intro e
        have : server = tid := by
          cases server; cases tid; simp only [beq_iff_eq] at e; subst e; rfl
        subst this
        exact ⟨ep0, rfl⟩
    | _ => intro e; cases e
  cases hEp : st.getEndpoint? epId with
  | none => rw [hEp] at hE; cases hE
  | some ep =>
  rw [hEp] at hE
  dsimp only at hE
  simp -iota only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hE
  obtain ⟨hS, hT⟩ := hE
  cases hTt : st.getTcb? tid with
  | none => rw [hTt] at hT; cases hT
  | some rt =>
  rw [hTt] at hT
  dsimp only at hT
  simp -iota only [Bool.and_eq_true] at hT
  obtain ⟨hA, hEnq⟩ := hT
  cases hR : st.getReply? rid with
  | none => rw [hR] at hRp; cases hRp
  | some rp =>
  rw [hR] at hRp
  dsimp only at hRp
  simp -iota only [Bool.and_eq_true, Bool.not_eq_true'] at hRp
  obtain ⟨⟨hFree, hStash⟩, hRecR⟩ := hRp
  refine ⟨ct, ep0, rt, ep, rp, (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc, hIpc', ?_, hW,
    hNe', (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp, hS,
    (SystemState.getTcb?_eq_some_iff _ _ _).mp hTt, hA, ?_,
    (SystemState.getReply?_eq_some_iff _ _ _).mp hR, (Reply.consumedIsFree_eq rp).symm.trans hFree,
    hStash, hRecR, ?_⟩
  · simp only [TCB.replyObject, beq_iff_eq.mp hRO, SeLe4n.ReplyId.ofOptCode]
  · rw [enqueuesInPlaceCode_eq, Endpoint.ofOptCode_recvTailCode] at hEnq; exact hEnq
  · simp only [receiveQueueTailCode, hEp]

theorem replyRecvReplyInertW_spec {st : SystemState} {tid c : SeLe4n.ThreadId} {grant : Bool}
    {ct : TCB} (h : replyRecvReplyInertW st tid c grant = true)
    (hT : st.objects[c.toObjId]? = some (.tcb ct)) :
    replyTransferInert st tid ct grant = true := by
  unfold replyRecvReplyInertW at h
  rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hT] at h
  exact replyTransferInert_of_W h

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
  simp -iota only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hNe, hC⟩, hU⟩, hE⟩, hRp⟩ := h
  have hNe' : tid ≠ c := fun e => by subst e; simp at hNe
  cases hTc : st.getTcb? c with
  | none => rw [hTc] at hC; cases hC
  | some ct =>
  rw [hTc] at hC
  dsimp only at hC
  simp -iota only [Bool.and_eq_true] at hC
  obtain ⟨hIpc, hRO⟩ := hC
  obtain ⟨ep0, hIpc'⟩ : ∃ ep0, ct.ipcState = .blockedOnReply ep0 none := by
    revert hIpc
    cases hS : ct.ipcState with
    | blockedOnReply ep0 server =>
      cases server with
      | none => intro _; exact ⟨ep0, rfl⟩
      | some server => intro e; cases e
    | _ => intro e; cases e
  cases hEp : st.getEndpoint? epId with
  | none => rw [hEp] at hE; cases hE
  | some ep =>
  rw [hEp] at hE
  dsimp only at hE
  simp -iota only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hE
  obtain ⟨hS, hT⟩ := hE
  cases hTt : st.getTcb? tid with
  | none => rw [hTt] at hT; cases hT
  | some rt =>
  rw [hTt] at hT
  dsimp only at hT
  simp -iota only [Bool.and_eq_true] at hT
  obtain ⟨hA, hEnq⟩ := hT
  cases hR : st.getReply? rid with
  | none => rw [hR] at hRp; cases hRp
  | some rp =>
  rw [hR] at hRp
  dsimp only at hRp
  simp -iota only [Bool.and_eq_true, Bool.not_eq_true'] at hRp
  obtain ⟨hStash, hRecR⟩ := hRp
  refine ⟨ct, ep0, rt, ep, rp, (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc, hIpc', ?_, hU,
    hNe', (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp, hS,
    (SystemState.getTcb?_eq_some_iff _ _ _).mp hTt, hA, ?_,
    (SystemState.getReply?_eq_some_iff _ _ _).mp hR, hStash, hRecR, ?_⟩
  · simp only [TCB.replyObject, beq_iff_eq.mp hRO, SeLe4n.ReplyId.ofOptCode]
  · rw [enqueuesInPlaceCode_eq, Endpoint.ofOptCode_recvTailCode] at hEnq; exact hEnq
  · simp only [receiveQueueTailCode, hEp]

theorem replyRecvUnlinkedBlocks_spec {st : SystemState} {epId : SeLe4n.ObjId}
    {tid c : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    (h : replyRecvUnlinkedBlocks st epId tid c rid = true) :
    ∃ (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply),
      st.objects[c.toObjId]? = some (.tcb ct) ∧
      ct.ipcState = .blockedOnReply ep0 none ∧ ct.replyObject = some rid ∧
      replyUnlinkedInPlace st c rid = true ∧ tid ≠ c ∧
      st.objects[epId]? = some (.endpoint ep) ∧ ep.sendQ.head = none ∧
      st.objects[tid.toObjId]? = some (.tcb rt) ∧ receiveBlockAdmits rt = true ∧
      enqueuesInPlace st epId tid ep.receiveQ.tail = true ∧
      st.objects[rid.toObjId]? = some (.reply rp) ∧
      st.replyStashedAt rid rp = false ∧ replyRecordsInPlace st (rid.val + 1) = true ∧
      receiveQueueTailCode st epId = ep.recvTailCode := by
  unfold replyRecvUnlinkedBlocks at h
  simp -iota only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hNe, hC⟩, hU⟩, hE⟩, hRp⟩ := h
  have hNe' : tid ≠ c := fun e => by subst e; simp at hNe
  cases hTc : st.getTcb? c with
  | none => rw [hTc] at hC; cases hC
  | some ct =>
  rw [hTc] at hC
  dsimp only at hC
  simp -iota only [Bool.and_eq_true] at hC
  obtain ⟨hIpc, hRO⟩ := hC
  obtain ⟨ep0, hIpc'⟩ : ∃ ep0, ct.ipcState = .blockedOnReply ep0 none := by
    revert hIpc
    cases hS : ct.ipcState with
    | blockedOnReply ep0 server =>
      cases server with
      | none => intro _; exact ⟨ep0, rfl⟩
      | some server => intro e; cases e
    | _ => intro e; cases e
  cases hEp : st.getEndpoint? epId with
  | none => rw [hEp] at hE; cases hE
  | some ep =>
  rw [hEp] at hE
  dsimp only at hE
  simp -iota only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hE
  obtain ⟨hS, hT⟩ := hE
  cases hTt : st.getTcb? tid with
  | none => rw [hTt] at hT; cases hT
  | some rt =>
  rw [hTt] at hT
  dsimp only at hT
  simp -iota only [Bool.and_eq_true] at hT
  obtain ⟨hA, hEnq⟩ := hT
  cases hR : st.getReply? rid with
  | none => rw [hR] at hRp; cases hRp
  | some rp =>
  rw [hR] at hRp
  dsimp only at hRp
  simp -iota only [Bool.and_eq_true, Bool.not_eq_true'] at hRp
  obtain ⟨hStash, hRecR⟩ := hRp
  refine ⟨ct, ep0, rt, ep, rp, (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc, hIpc', ?_, hU,
    hNe', (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp, hS,
    (SystemState.getTcb?_eq_some_iff _ _ _).mp hTt, hA, ?_,
    (SystemState.getReply?_eq_some_iff _ _ _).mp hR, hStash, hRecR, ?_⟩
  · simp only [TCB.replyObject, beq_iff_eq.mp hRO, SeLe4n.ReplyId.ofOptCode]
  · rw [enqueuesInPlaceCode_eq, Endpoint.ofOptCode_recvTailCode] at hEnq; exact hEnq
  · simp only [receiveQueueTailCode, hEp]

/-- **A nonzero arm code admits its arm**, the context the pop returns or
keeps and the caller's home read on the pre-state, with the checks every arm
shares. -/
theorem replyRecvBlockArmCode_spec {st : SystemState} {epId : SeLe4n.ObjId}
    {tid c : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    (h : replyRecvBlockArmCode st epId tid c rid ≠ 0) :
    ∃ (ct rt : TCB) (ep : Endpoint) (rp : Reply),
      (ReplyRecvArm.ofCode (replyRecvBlockArmCode st epId tid c rid)).Admits
        ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st tid c rid ct rt rp ∧
      st.objects[c.toObjId]? = some (.tcb ct) ∧ ct.replyObject = some rid ∧
      st.objects[epId]? = some (.endpoint ep) ∧ ep.sendQ.head = none ∧
      st.objects[tid.toObjId]? = some (.tcb rt) ∧
      enqueuesInPlace st epId tid ep.receiveQ.tail = true ∧
      st.objects[rid.toObjId]? = some (.reply rp) ∧ st.replyStashedAt rid rp = false ∧
      replyRecordsInPlace st (rid.val + 1) = true ∧
      receiveQueueTailCode st epId = ep.recvTailCode := by
  have tailOf : ∀ {ep : Endpoint}, st.objects[epId]? = some (.endpoint ep) →
      receiveQueueTailCode st epId = ep.recvTailCode := fun hE => by
    simp only [receiveQueueTailCode, (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE]
  unfold replyRecvBlockArmCode at h ⊢
  by_cases h1 : replyRecvBlocksFast st epId tid c rid = true
  · obtain ⟨ct, ep0, rt, ep, rp, hT, hIpc, hRO, hW, hNe, hE, hS, hR, hA, hEnq, hRp, hFree,
      hStash, hRec, hTail⟩ := replyRecvBlocksFast_spec h1
    simp only [h1, ↓reduceIte]
    exact ⟨ct, rt, ep, rp, ⟨⟨ep0, hIpc⟩, hW, hNe, hA, (Reply.consumedIsFree_eq rp).trans hFree⟩,
      hT, hRO, hE, hS, hR, hEnq, hRp, hStash, hRec, hTail⟩
  simp only [h1, Bool.false_eq_true, ↓reduceIte] at h ⊢
  by_cases h2 : replyRecvDonatedBlocks st epId tid c rid = true
  · obtain ⟨ct, ep0, rt, ep, rp, hT, hIpc, hRO, hP, hSRes, hE, hS, hR, hA, hEnq, hRp, hStash,
      hRec⟩ := replyRecvDonatedBlocks_spec h2
    simp only [h2, ↓reduceIte]
    exact ⟨ct, rt, ep, rp, ⟨⟨ep0, hIpc⟩, hSRes, hP, hA, rfl, rfl⟩, hT, hRO, hE, hS, hR, hEnq, hRp,
      hStash, hRec, tailOf hE⟩
  simp only [h2, Bool.false_eq_true, ↓reduceIte] at h ⊢
  by_cases h3 : replyRecvHeldBlocks st epId tid c rid = true
  · obtain ⟨ct, ep0, rt, ep, rp, hT, hIpc, hRO, hP, hSRes, hE, hS, hR, hOwn, hA, hEnq, hRp,
      hStash, hRec⟩ := replyRecvHeldBlocks_spec h3
    simp only [h3, ↓reduceIte]
    exact ⟨ct, rt, ep, rp, ⟨⟨ep0, hIpc⟩, hSRes, hP, hOwn, hA, rfl⟩, hT, hRO, hE, hS, hR, hEnq,
      hRp, hStash, hRec, tailOf hE⟩
  simp only [h3, Bool.false_eq_true, ↓reduceIte] at h ⊢
  by_cases h4 : replyRecvUnheldBlocks st epId tid c rid = true
  · obtain ⟨ct, ep0, rt, ep, rp, hT, hIpc, hRO, hU, hNe, hE, hS, hR, hA, hEnq, hRp, hStash, hRec,
      hTail⟩ := replyRecvUnheldBlocks_spec h4
    simp only [h4, ↓reduceIte]
    exact ⟨ct, rt, ep, rp, ⟨⟨ep0, hIpc⟩, hU, hNe, hA, rfl, rfl⟩, hT, hRO, hE, hS, hR, hEnq, hRp,
      hStash, hRec, hTail⟩
  simp only [h4, Bool.false_eq_true, ↓reduceIte] at h ⊢
  by_cases h5 : replyRecvUnlinkedBlocks st epId tid c rid = true
  · obtain ⟨ct, ep0, rt, ep, rp, hT, hIpc, hRO, hU, hNe, hE, hS, hR, hA, hEnq, hRp, hStash, hRec,
      hTail⟩ := replyRecvUnlinkedBlocks_spec h5
    simp only [h5, ↓reduceIte]
    exact ⟨ct, rt, ep, rp, ⟨⟨ep0, hIpc⟩, hU, hNe, hA⟩, hT, hRO, hE, hS, hR, hEnq, hRp, hStash,
      hRec, hTail⟩
  simp only [h5, Bool.false_eq_true, ↓reduceIte] at h
  exact absurd rfl h

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
  cases hS : st.getTcb? tid with
  | none => rfl
  | some stcb =>
    dsimp only
    cases hR : Architecture.RegisterDecode.registerRoutedSyscallOf SyscallId.replyRecv.toNat
        SeLe4n.arm64DefaultLayout stcb.registerContext
    case replyRecv capAddr mi =>
      dsimp only
      cases hTc0 : st.getTcb? c with
      | none => rfl
      | some ct0 =>
        dsimp only
        have hTc0' := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc0
        split
        · next hG =>
          simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hG
          obtain ⟨⟨hGr, hSz⟩, hK⟩ := hG
          subst hGr
          have hReq := replyCapRequest_of_routedReplyRecv st tid stcb capAddr mi hS hR
          obtain ⟨ct, rt, ep, rp, hAd, hT, hRO, hE, hS', hR', hEnq, hRp, hStash, hRecR, hTail⟩ :=
            replyRecvBlockArmCode_spec hK
          obtain rfl : ct = ct0 := by rw [hT] at hTc0'; cases hTc0'; rfl
          unfold replyRecvRendezvousR
          rw [replyRecvTransferOnCoreR_eq_match]
          rw [replyRecvTransferOnCore_of_no_fault (h := hNoF) (hA := hAd.popAdmits hT hRO), hTail]
          have h := replyRecvOnCore_arm_capsDelivered _ st epId tid c rid layout rf len badge
            executingCore ct rt ep rp stcb _ hAd hSz hT hRO hE hS' hR' hEnq hRp hStash hRecR hReq
          generalize endpointReplyRecvOnCore epId tid rid c
            { registers := Architecture.regMessageBody layout rf len, badge := badge } true
            executingCore st = r at h ⊢
          rcases r with e | ⟨a, st'⟩
          · cases h
          · simp only [Except.ok.injEq] at h ⊢
            exact h.symm
        · rfl
    all_goals rfl

/-- **The installing reply-receive does not reach the general path when its
checks pass**: on a replier whose frame routes as a reply-receive under the
default layout, with the grant right, a reply of at most four words and a reply
arm whose receive blocks in place -- every check read on the pre-state, before
any write -- the arm's performer runs.  The general path
(`replyRecvRendezvousR`) is reached only when one of those checks fails, on the
state the arm was handed. -/
theorem replyRecvCapsArmR_inPlace (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) (st : SystemState) (stcb ct : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hS : st.getTcb? tid = some stcb)
    (hR : Architecture.RegisterDecode.registerRoutedSyscallOf SyscallId.replyRecv.toNat
      SeLe4n.arm64DefaultLayout stcb.registerContext = .replyRecv capAddr mi)
    (hC : st.getTcb? c = some ct)
    (hAdm : (grant && decide (Architecture.regMessageLength layout len ≤ 4) &&
      replyRecvBlockArmCode st epId tid c rid != 0) = true) :
    replyRecvCapsArmR epId tid c rid badge grant layout rf len label executingCore st =
      .ok ((), performReplyRecvArmCapsDelivered
        (ReplyRecvArm.ofCode (replyRecvBlockArmCode st epId tid c rid))
        ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId
        (receiveQueueTailCode st epId) layout rf len badge executingCore stcb.spaceCells[2]
        stcb.ipcBuffer stcb.spaceCells[0] (routedExtraCaps stcb.registerContext) ct.spaceCells[2]
        ct.ipcBuffer ct.spaceCells[0]) := by
  unfold replyRecvCapsArmR
  simp only [hS, hR, hC, hAdm, if_true]

/-- **A nonzero take code admits its arm's reply leg**, at the context the
reply heads and the caller's home, with the sender the take reads. -/
theorem replyRecvTakeArmCode_spec {st : SystemState} {epId : SeLe4n.ObjId}
    {tid c : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    (h : replyRecvTakeArmCode st epId tid c rid ≠ 0) :
    ∃ (ct : TCB) (rp : Reply) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB),
      (ReplyRecvArm.ofCode (replyRecvTakeArmCode st epId tid c rid)).LegAdmits
        ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st tid c rid ct ∧
      st.objects[c.toObjId]? = some (.tcb ct) ∧ ct.replyObject = some rid ∧
      st.objects[rid.toObjId]? = some (.reply rp) ∧
      st.getEndpoint? epId = some ep ∧ ep.sendQ.head = some s ∧ st.getTcb? s = some sTcb ∧
      s ≠ c ∧ sTcb.ipcFaultSend = false ∧ receiveTakesInPlace st epId tid s sTcb = true := by
  unfold replyRecvTakeArmCode at h ⊢
  cases hTc : st.getTcb? c with
  | none => rw [hTc] at h; exact absurd rfl h
  | some ct =>
  rw [hTc] at h
  simp only at h ⊢
  by_cases hG : (ct.replyObjectCode == rid.val + 1 && (st.getReply? rid).isSome &&
      replyRecvSenderTakes st epId tid c) = true
  · have hG' := hG
    simp only [Bool.and_eq_true] at hG'
    obtain ⟨⟨hRO, hRpS⟩, hSnd⟩ := hG'
    obtain ⟨rp, hRp⟩ := Option.isSome_iff_exists.mp hRpS
    obtain ⟨ep, s, sTcb, hEp, hH, hTs, hSC, hF, hTk⟩ := replyRecvSenderTakes_spec hSnd
    have hRO' : ct.replyObject = some rid := by
      simp only [TCB.replyObject, beq_iff_eq.mp hRO, SeLe4n.ReplyId.ofOptCode]
    have fin : ∀ arm : ReplyRecvArm, arm.legGuard st tid c rid ct = true →
        ∃ (ct' : TCB) (rp : Reply) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB),
          arm.LegAdmits ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st tid c
            rid ct' ∧
          st.objects[c.toObjId]? = some (.tcb ct') ∧ ct'.replyObject = some rid ∧
          st.objects[rid.toObjId]? = some (.reply rp) ∧
          st.getEndpoint? epId = some ep ∧ ep.sendQ.head = some s ∧ st.getTcb? s = some sTcb ∧
          s ≠ c ∧ sTcb.ipcFaultSend = false ∧ receiveTakesInPlace st epId tid s sTcb = true :=
      fun _ hA => ⟨ct, rp, ep, s, sTcb, ReplyRecvArm.legGuard_spec hA,
        (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc, hRO',
        (SystemState.getReply?_eq_some_iff _ _ _).mp hRp, hEp, hH, hTs, hSC, hF, hTk⟩
    simp only [hG, ↓reduceIte] at h ⊢
    by_cases h1 : ReplyRecvArm.rendezvous.legGuard st tid c rid ct = true
    · simp only [h1, ↓reduceIte]; exact fin _ h1
    simp only [h1, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases h2 : ReplyRecvArm.donated.legGuard st tid c rid ct = true
    · simp only [h2, ↓reduceIte]; exact fin _ h2
    simp only [h2, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases h3 : ReplyRecvArm.held.legGuard st tid c rid ct = true
    · simp only [h3, ↓reduceIte]; exact fin _ h3
    simp only [h3, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases h4 : ReplyRecvArm.unheld.legGuard st tid c rid ct = true
    · simp only [h4, ↓reduceIte]; exact fin _ h4
    simp only [h4, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases h5 : ReplyRecvArm.unlinked.legGuard st tid c rid ct = true
    · simp only [h5, ↓reduceIte]; exact fin _ h5
    simp only [h5, Bool.false_eq_true, ↓reduceIte] at h
    exact absurd rfl h
  · simp only [hG, Bool.false_eq_true, ↓reduceIte] at h
    exact absurd rfl h

/-- On an unfaulted caller the take arm is the specification's path. -/
theorem replyRecvArmTakeR_eq (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (hNoF : threadHasPendingFault st c = false) :
    replyRecvArmTakeR epId tid c rid badge grant layout rf len label executingCore st =
      replyRecvRendezvousR epId tid c rid badge grant layout rf len label executingCore st := by
  unfold replyRecvArmTakeR
  split
  · next hA =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hA
    obtain ⟨hSz4, hK⟩ := hA
    obtain ⟨ct, rp, ep, s, sTcb, hAd, hT, hRO, hRp, hEp, hH, hTs, hSC, hF, hG⟩ :=
      replyRecvTakeArmCode_spec hK
    have hE := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp
    have hS := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTs
    rw [hEp]
    dsimp only
    rw [hH]
    dsimp only
    rw [hTs]
    dsimp only
    cases hR : Architecture.RegisterDecode.registerRoutedSyscallOf
        (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
        SeLe4n.arm64DefaultLayout sTcb.registerContext
    case send capAddr mi =>
      dsimp only
      split
      · next hI =>
        have h := replyRecvOnCore_arm_takeDelivered _ st epId tid c rid layout rf len badge grant
          executingCore ct rp ep s sTcb capAddr mi hAd hSz4 hT hRO hRp
          (replyRecvReplyInertW_spec hI hT) hE hH hS hSC hG
          ((Architecture.RegisterDecode.registerRoutedSyscall_default _).trans hR) hF
        rw [Architecture.regMessageFrameW_eq, ← TCB.ipcBadgeView_eq_opt]
        unfold replyRecvRendezvousR
        rw [replyRecvTransferOnCoreR_eq_match]
        rw [replyRecvTransferOnCore_of_no_fault (h := hNoF) (hA := hAd.popAdmits hT hRO)]
        generalize endpointReplyRecvOnCore epId tid rid c
          { registers := Architecture.regMessageBody layout rf len, badge := badge } grant
          executingCore st = r at h ⊢
        rcases r with e | ⟨a, st'⟩
        · cases h
        · simp only [Except.ok.injEq] at h ⊢
          exact h.symm
      · cases hS' : st.getTcb? tid with
        | none => rfl
        | some stcb =>
          dsimp only
          cases hR' : Architecture.RegisterDecode.registerRoutedSyscallOf SyscallId.replyRecv.toNat
              SeLe4n.arm64DefaultLayout stcb.registerContext
          case replyRecv capAddr' mi' =>
            dsimp only
            cases hTc0 : st.getTcb? c with
            | none => rfl
            | some ct0 =>
              dsimp only
              have hTc0' := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc0
              obtain rfl : ct = ct0 := by rw [hT] at hTc0'; cases hTc0'; rfl
              split
              · next hGr =>
                subst hGr
                have hReq := replyCapRequest_of_routedReplyRecv st tid stcb capAddr' mi' hS' hR'
                have h := replyRecvOnCore_arm_takeCapsDelivered _ st epId tid c rid layout rf len
                  badge executingCore ct rp ep s sTcb capAddr mi stcb _ hAd hSz4 hT hRO hRp
                  hE hH hS hSC hG ((Architecture.RegisterDecode.registerRoutedSyscall_default _).trans hR)
                  hF hReq
                rw [Architecture.regMessageFrameW_eq, ← TCB.ipcBadgeView_eq_opt]
                unfold replyRecvRendezvousR
                rw [replyRecvTransferOnCoreR_eq_match]
                rw [replyRecvTransferOnCore_of_no_fault (h := hNoF) (hA := hAd.popAdmits hT hRO)]
                generalize endpointReplyRecvOnCore epId tid rid c
                  { registers := Architecture.regMessageBody layout rf len, badge := badge } true
                  executingCore st = r at h ⊢
                rcases r with e | ⟨a, st'⟩
                · cases h
                · simp only [Except.ok.injEq] at h ⊢
                  exact h.symm
              · rfl
          all_goals rfl
    all_goals rfl
  · exact replyRecvCapsArmR_eq epId tid c rid badge grant layout rf len label executingCore st
      hNoF

theorem replyRecvArmCallCode_spec {arm : ReplyRecvArm} {st : SystemState}
    {epId : SeLe4n.ObjId} {tid c : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId} {ct : TCB}
    {s : SeLe4n.ThreadId} {sTcb : TCB} {k kOwn : Nat}
    (h : replyRecvArmCallCode arm st epId tid c rid ct s sTcb k kOwn ≠ 0) :
    (replyRecvArmCallCode arm st epId tid c rid ct s sTcb k kOwn = k ∧
        (arm.legGuard st tid c rid ct && arm.callGuard st epId tid s sTcb rid) = true) ∨
      (replyRecvArmCallCode arm st epId tid c rid ct s sTcb k kOwn = kOwn ∧
        (arm.legGuard st tid c rid ct && arm.callOwnGuard st epId tid s sTcb) = true) := by
  unfold replyRecvArmCallCode at h ⊢
  by_cases hL : arm.legGuard st tid c rid ct = true
  · by_cases hC : arm.callGuard st epId tid s sTcb rid = true
    · left; simp [hL, hC]
    · by_cases hO : arm.callOwnGuard st epId tid s sTcb = true
      · right; simp [hL, hC, hO]
      · simp [hL, hC, hO] at h
  · simp [hL] at h

/-- **A nonzero Call-take code admits its arm's reply leg and Call take**, at
the context the reply heads and the caller's home, with the queued caller the
take reads and its routed call. -/
theorem replyRecvCallTakeArmCode_spec {st : SystemState} {epId : SeLe4n.ObjId}
    {tid c : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    (h : replyRecvCallTakeArmCode st epId tid c rid ≠ 0) :
    ∃ (ct : TCB) (rp : Reply) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
      (capAddr : SeLe4n.CPtr) (mi : MessageInfo),
      (ReplyRecvArm.ofCode (replyRecvCallTakeArmCode st epId tid c rid)).LegAdmits
        ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st tid c rid ct ∧
      (ReplyRecvArm.ofCode (replyRecvCallTakeArmCode st epId tid c rid)).CallAdmitsAt
        (replyRecvCallLendsOfCode (replyRecvCallTakeArmCode st epId tid c rid)) st epId tid
        s sTcb rid ∧
      st.objects[c.toObjId]? = some (.tcb ct) ∧ ct.replyObject = some rid ∧
      st.objects[rid.toObjId]? = some (.reply rp) ∧
      st.getEndpoint? epId = some ep ∧ ep.sendQ.head = some s ∧ st.getTcb? s = some sTcb ∧
      s ≠ c ∧ sTcb.ipcFaultSend = false ∧
      Architecture.RegisterDecode.registerRoutedSyscallOf
        (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
        SeLe4n.arm64DefaultLayout sTcb.registerContext = .call capAddr mi := by
  generalize hk : replyRecvCallTakeArmCode st epId tid c rid = k at h ⊢
  unfold replyRecvCallTakeArmCode at hk
  cases hTc : st.getTcb? c with
  | none => rw [hTc] at hk; subst hk; exact absurd rfl h
  | some ct =>
  rw [hTc] at hk
  dsimp only at hk
  by_cases hG : (ct.replyObjectCode == rid.val + 1 && (st.getReply? rid).isSome &&
      replyRecvCallerQueued st epId c) = true
  · have hG' := hG
    simp only [Bool.and_eq_true] at hG'
    obtain ⟨⟨hRO, hRpS⟩, hQ⟩ := hG'
    obtain ⟨rp, hRp⟩ := Option.isSome_iff_exists.mp hRpS
    obtain ⟨ep, s, sTcb, capAddr, mi, hEp, hH, hTs, hSC, hF, hRt⟩ := replyRecvCallerQueued_spec hQ
    have hRO' : ct.replyObject = some rid := by
      simp only [TCB.replyObject, beq_iff_eq.mp hRO, SeLe4n.ReplyId.ofOptCode]
    have fin : ∀ (arm : ReplyRecvArm) (lends : Bool), arm.legGuard st tid c rid ct = true →
        arm.CallAdmitsAt lends st epId tid s sTcb rid →
        ∃ (ct' : TCB) (rp : Reply) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
          (capAddr : SeLe4n.CPtr) (mi : MessageInfo),
          arm.LegAdmits ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st tid c
            rid ct' ∧
          arm.CallAdmitsAt lends st epId tid s sTcb rid ∧
          st.objects[c.toObjId]? = some (.tcb ct') ∧ ct'.replyObject = some rid ∧
          st.objects[rid.toObjId]? = some (.reply rp) ∧
          st.getEndpoint? epId = some ep ∧ ep.sendQ.head = some s ∧ st.getTcb? s = some sTcb ∧
          s ≠ c ∧ sTcb.ipcFaultSend = false ∧
          Architecture.RegisterDecode.registerRoutedSyscallOf
            (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
            SeLe4n.arm64DefaultLayout sTcb.registerContext = .call capAddr mi :=
      fun _ _ hA hC =>
        ⟨ct, rp, ep, s, sTcb, capAddr, mi, ReplyRecvArm.legGuard_spec hA, hC,
          (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc, hRO',
          (SystemState.getReply?_eq_some_iff _ _ _).mp hRp, hEp, hH, hTs, hSC, hF, hRt⟩
    have lend : ∀ arm : ReplyRecvArm, (arm.legGuard st tid c rid ct &&
        arm.callGuard st epId tid s sTcb rid) = true →
        arm.legGuard st tid c rid ct = true ∧ arm.CallAdmitsAt arm.callLends st epId tid s sTcb rid :=
      fun _ hA => by
        simp only [Bool.and_eq_true] at hA
        exact ⟨hA.1, by
          unfold ReplyRecvArm.CallAdmitsAt; rw [if_pos rfl]; exact ReplyRecvArm.callGuard_spec hA.2⟩
    have own : ∀ arm : ReplyRecvArm, arm.callLends = true → (arm.legGuard st tid c rid ct &&
        arm.callOwnGuard st epId tid s sTcb) = true →
        arm.legGuard st tid c rid ct = true ∧ arm.CallAdmitsAt false st epId tid s sTcb rid :=
      fun _ hL hA => by
        simp only [Bool.and_eq_true] at hA
        exact ⟨hA.1, by
          unfold ReplyRecvArm.CallAdmitsAt; rw [if_neg (by rw [hL]; decide)]
          exact ReplyRecvArm.callOwnGuard_spec hA.2⟩
    rw [if_pos hG, hEp] at hk
    dsimp only at hk
    rw [hH] at hk
    dsimp only at hk
    rw [hTs] at hk
    dsimp only at hk
    generalize hc : replyRecvArmCallCode .rendezvous st epId tid c rid ct s sTcb 1 6 = kA at hk
    by_cases hA0 : kA = 0
    case neg =>
      simp only [hA0, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte] at hk
      subst hk
      rcases replyRecvArmCallCode_spec (by rw [hc]; exact hA0) with ⟨e, hB⟩ | ⟨e, hB⟩ <;>
        rw [hc] at e <;> subst e
      · exact fin _ _ (lend _ hB).1 (lend _ hB).2
      · exact fin _ _ (own _ rfl hB).1 (own _ rfl hB).2
    rw [hA0] at hk
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hk
    clear hc
    generalize hc : replyRecvArmCallCode .donated st epId tid c rid ct s sTcb 2 0 = kA at hk
    by_cases hA0 : kA = 0
    case neg =>
      simp only [hA0, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte] at hk
      subst hk
      rcases replyRecvArmCallCode_spec (by rw [hc]; exact hA0) with ⟨e, hB⟩ | ⟨e, hB⟩ <;>
        rw [hc] at e <;> subst e
      · exact fin _ _ (lend _ hB).1 (lend _ hB).2
      · exact absurd rfl hA0
    rw [hA0] at hk
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hk
    clear hc
    generalize hc : replyRecvArmCallCode .held st epId tid c rid ct s sTcb 3 0 = kA at hk
    by_cases hA0 : kA = 0
    case neg =>
      simp only [hA0, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte] at hk
      subst hk
      rcases replyRecvArmCallCode_spec (by rw [hc]; exact hA0) with ⟨e, hB⟩ | ⟨e, hB⟩ <;>
        rw [hc] at e <;> subst e
      · exact fin _ _ (lend _ hB).1 (lend _ hB).2
      · exact absurd rfl hA0
    rw [hA0] at hk
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hk
    clear hc
    generalize hc : replyRecvArmCallCode .unheld st epId tid c rid ct s sTcb 4 7 = kA at hk
    by_cases hA0 : kA = 0
    case neg =>
      simp only [hA0, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte] at hk
      subst hk
      rcases replyRecvArmCallCode_spec (by rw [hc]; exact hA0) with ⟨e, hB⟩ | ⟨e, hB⟩ <;>
        rw [hc] at e <;> subst e
      · exact fin _ _ (lend _ hB).1 (lend _ hB).2
      · exact fin _ _ (own _ rfl hB).1 (own _ rfl hB).2
    rw [hA0] at hk
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hk
    clear hc
    generalize hc : replyRecvArmCallCode .unlinked st epId tid c rid ct s sTcb 5 8 = kA at hk
    by_cases hA0 : kA = 0
    case neg =>
      simp only [hA0, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte] at hk
      subst hk
      rcases replyRecvArmCallCode_spec (by rw [hc]; exact hA0) with ⟨e, hB⟩ | ⟨e, hB⟩ <;>
        rw [hc] at e <;> subst e
      · exact fin _ _ (lend _ hB).1 (lend _ hB).2
      · exact fin _ _ (own _ rfl hB).1 (own _ rfl hB).2
    rw [hA0] at hk
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hk
    clear hc
    subst hk; exact absurd rfl h
  · rw [if_neg hG] at hk
    subst hk; exact absurd rfl h
/-- On an unfaulted caller the Call-take arm is the specification's path. -/
theorem replyRecvArmCallTakeR_eq (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (hNoF : threadHasPendingFault st c = false) :
    replyRecvArmCallTakeR epId tid c rid badge grant layout rf len label executingCore st =
      replyRecvRendezvousR epId tid c rid badge grant layout rf len label executingCore st := by
  unfold replyRecvArmCallTakeR
  split
  · next hA =>
    simp only [replyRecvShortCallTakeAdmits, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, bne_iff_ne, ne_eq] at hA
    obtain ⟨⟨hSz4, hK⟩, hShape⟩ := hA
    obtain ⟨ct, rp, ep, s, sTcb, capAddr, mi, hAd, hCA, hT, hRO, hRp, hEp, hH, hTs, hSC, hF, hRt⟩ :=
      replyRecvCallTakeArmCode_spec hK
    have hE := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp
    have hS := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTs
    have hTc := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
    have hR' := (Architecture.RegisterDecode.registerRoutedSyscall_default _).trans hRt
    unfold replyRecvCallTakeAnswer
    rw [hEp]
    dsimp only
    rw [hH]
    dsimp only
    rw [hTs]
    dsimp only
    rw [hRt]
    dsimp only
    split
    · next hI =>
      have h := replyRecvOnCore_arm_callTakeDelivered _ _ st epId tid c rid layout rf len badge
        grant executingCore ct rp ep s sTcb capAddr mi hAd hCA hSz4 hT hRO hRp
        (replyRecvReplyInertW_spec hI hT) hE hH hS hSC hR' hF
      unfold replyRecvRendezvousR
      rw [replyRecvTransferOnCoreR_eq_match]
      rw [replyRecvTransferOnCore_of_no_fault (h := hNoF) (hA := hAd.popAdmits hT hRO)]
      generalize endpointReplyRecvOnCore epId tid rid c
        { registers := Architecture.regMessageBody layout rf len, badge := badge } grant
        executingCore st = r at h ⊢
      rcases r with e | ⟨a, st'⟩
      · cases h
      · simp only [Except.ok.injEq] at h ⊢
        exact h.symm
    · next hI =>
      obtain ⟨rfl, hRR⟩ : grant = true ∧ replyRecvFrameRoutesReplyRecv st tid = true := by
        rcases hShape with h | h
        · exact absurd h hI
        · simpa only [Bool.and_eq_true] using h
      unfold replyRecvFrameRoutesReplyRecv at hRR
      revert hRR
      cases hS' : st.getTcb? tid with
      | none => intro hRR; cases hRR
      | some stcb =>
        dsimp only
        cases hRr : Architecture.RegisterDecode.registerRoutedSyscallOf SyscallId.replyRecv.toNat
            SeLe4n.arm64DefaultLayout stcb.registerContext
        case replyRecv capAddr' mi' =>
          intro _
          rw [hTc]
          dsimp only
          have hReq := replyCapRequest_of_routedReplyRecv st tid stcb capAddr' mi' hS' hRr
          have h := replyRecvOnCore_arm_callTakeCapsDelivered _ _ st epId tid c rid layout rf
            len badge executingCore ct rp ep s sTcb capAddr mi stcb _ hAd hCA hSz4 hT hRO
            hRp hE hH hS hSC hR' hF hReq
          unfold replyRecvRendezvousR
          rw [replyRecvTransferOnCoreR_eq_match]
          rw [replyRecvTransferOnCore_of_no_fault (h := hNoF) (hA := hAd.popAdmits hT hRO)]
          generalize endpointReplyRecvOnCore epId tid rid c
            { registers := Architecture.regMessageBody layout rf len, badge := badge } true
            executingCore st = r at h ⊢
          rcases r with e | ⟨a, st'⟩
          · cases h
          · simp only [Except.ok.injEq] at h ⊢
            exact h.symm
        all_goals intro hRR; cases hRR
  · exact replyRecvArmTakeR_eq epId tid c rid badge grant layout rf len label executingCore
      st hNoF

/-- On a faulted caller the arm is the specification's path. -/
theorem replyRecvFaultArmR_eq (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (hF : threadHasPendingFault st c = true) :
    replyRecvFaultArmR epId tid c rid badge grant layout rf len label executingCore st =
      replyRecvRendezvousR epId tid c rid badge grant layout rf len label executingCore st := by
  unfold replyRecvFaultArmR
  cases hTc0 : st.getTcb? c with
  | none => rfl
  | some ct0 =>
    dsimp only
    have hTc0' := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc0
    obtain ⟨tf, hPF⟩ : ∃ tf, ct0.pendingFault = some tf := by
      unfold threadHasPendingFault at hF
      rw [hTc0] at hF
      exact Option.isSome_iff_exists.mp hF
    split
    · next hK =>
      obtain ⟨ct, rt, ep, rp, hAd, hT, hRO, hE, hS, hR, hEnq, hRp, hStash, hRecR, hTail⟩ :=
        replyRecvBlockArmCode_spec (by simpa using hK)
      obtain rfl : ct = ct0 := by
        rw [hT] at hTc0'; cases hTc0'; rfl
      obtain ⟨hEq, hStg⟩ := replyRecvTransferOnCore_arm_fault_inPlace _ st epId tid c rid label
        layout rf len badge grant executingCore ct rt ep rp tf hAd hPF hT hRO hE hS hR hEnq hRp
        hStash hRecR
      unfold replyRecvRendezvousR
      rw [replyRecvTransferOnCoreR_eq_match]
      rw [hEq]
      simp only [CapTransferSummary.capInfo_empty]
      rw [hTail, hStg]
    · split
      · next hTk =>
        obtain ⟨ct, rp, ep, s, sTcb, hAd, hT, hRO, hRp, hEp, hH, hTs, hSC, hFs, hG⟩ :=
          replyRecvTakeArmCode_spec (by simpa using hTk)
        obtain rfl : ct = ct0 := by
          rw [hT] at hTc0'; cases hTc0'; rfl
        have hE := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp
        have hS := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTs
        rw [hEp]
        dsimp only
        rw [hH]
        dsimp only
        rw [hTs]
        dsimp only
        cases hR : Architecture.RegisterDecode.registerRoutedSyscallOf
            (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
            SeLe4n.arm64DefaultLayout sTcb.registerContext
        case send capAddr mi =>
          dsimp only
          have h := replyRecvTransferOnCore_arm_faultTake _ st epId tid c rid label layout
            rf len badge grant executingCore ct rp ep tf s sTcb capAddr mi hAd hPF hT hRO
            hRp hE hH hS hSC hG
            ((Architecture.RegisterDecode.registerRoutedSyscall_default _).trans hR) hFs
          rw [Architecture.regMessageFrameW_eq, ← TCB.ipcBadgeView_eq_opt]
          unfold replyRecvRendezvousR
          rw [replyRecvTransferOnCoreR_eq_match]
          generalize replyRecvTransferOnCore epId tid rid c label
            { registers := Architecture.regMessageBody layout rf len, badge := badge } grant
            executingCore st = r at h ⊢
          rcases r with e | ⟨a, st'⟩
          · cases h
          · simp only [Except.ok.injEq] at h ⊢
            exact h.symm
        all_goals rfl
      · rfl

/-- On a faulted caller the Call-take fault arm is the specification's path. -/
theorem replyRecvCallFaultArmR_eq (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (hF : threadHasPendingFault st c = true) :
    replyRecvCallFaultArmR epId tid c rid badge grant layout rf len label executingCore st =
      replyRecvRendezvousR epId tid c rid badge grant layout rf len label executingCore st := by
  unfold replyRecvCallFaultArmR
  split
  · next hK =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hK
    obtain ⟨hK, hSz4⟩ := hK
    obtain ⟨ct, rp, ep, s, sTcb, capAddr, mi, hAd, hCA, hT, hRO, hRp, hEp, hH, hTs, hSC, hFs,
      hRt⟩ := replyRecvCallTakeArmCode_spec (by simpa using hK)
    have hTc := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
    obtain ⟨tf, hPF⟩ : ∃ tf, ct.pendingFault = some tf := by
      unfold threadHasPendingFault at hF
      rw [hTc] at hF
      exact Option.isSome_iff_exists.mp hF
    have hE := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp
    have hS := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTs
    unfold replyRecvCallFaultTakeAnswer
    simp only [hTc, hEp, hH, hTs, hRt]
    have h := replyRecvTransferOnCore_arm_callFaultTake _ _ st epId tid c rid label layout rf len
      badge grant executingCore ct rp ep tf s sTcb capAddr mi hAd hCA hSz4 hPF hT hRO hRp hE hH hS
      hSC ((Architecture.RegisterDecode.registerRoutedSyscall_default _).trans hRt) hFs
    unfold replyRecvRendezvousR
    rw [replyRecvTransferOnCoreR_eq_match]
    generalize replyRecvTransferOnCore epId tid rid c label
      { registers := Architecture.regMessageBody layout rf len, badge := badge } grant
      executingCore st = r at h ⊢
    rcases r with e | ⟨a, st'⟩
    · cases h
    · simp only [Except.ok.injEq] at h ⊢
      exact h.symm
  · exact replyRecvFaultArmR_eq epId tid c rid badge grant layout rf len label executingCore st hF

/-- **The reply leg's words, read as the `.reply` arm reads them**: the layout's
message registers under the declared length, or the body the reply-receive cut
from them (`replyRecvReplyMessageInfo`), agree on every word a fault decode
reads. -/
theorem replyWordOr_regMessageRegs_body (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat) (i : Nat) (fb : UInt64)
    (hi : i ≤ 10) :
    Architecture.replyWordOr { length := len, extraCaps := extraCaps, label := label }
        (Architecture.regMessageRegs layout rf) i fb =
      Architecture.replyWordOr
        (replyRecvReplyMessageInfo label
          { registers := Architecture.regMessageBody layout rf len, badge := none })
        (Architecture.regMessageBody layout rf len) i fb := by
  have hS : (Architecture.regMessageRegs layout rf).size = layout.msgRegs.size := by
    simp only [Architecture.regMessageRegs, Array.size_map]
  have hB := Architecture.regMessageBody_size layout rf len
  unfold Architecture.replyWordOr
  simp only [hS, hB, Nat.min_self]
  have hMax : (10 : Nat) < maxMessageRegisters := by unfold maxMessageRegisters; omega
  by_cases hLt : i < min len layout.msgRegs.size
  · have hLt' : i < Architecture.regMessageLength layout len := by
      unfold Architecture.regMessageLength; omega
    rw [if_pos hLt, if_pos hLt', wordAt_regMessageRegs, wordAt_regMessageBody layout rf len i hLt']
  · have hLt' : ¬ i < Architecture.regMessageLength layout len := by
      unfold Architecture.regMessageLength; omega
    rw [if_neg hLt, if_neg hLt']

/-- The signal arm's second leg, in place, is the specification's: the gated
wait on the state the reply left, its refusal reported in the state the arm was
handed. -/
theorem replyRecvSignalLeg_eq (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (st st1 : SystemState) :
    (if receiveCompletesSignal ctx st1 tid && receiverIpcReady st1 tid then
        match notificationWaitGatedR ctx tid (receiverBoundNotification st1 tid) executingCore
            st1 with
        | .ok r => .ok r
        | .error (e, _) => .error (e, st)
      else .ok ((), st1) : Except (KernelError × SystemState) (Unit × SystemState)) =
      match (if receiveCompletesSignal ctx st1 tid && receiverIpcReady st1 tid then
          completeSignalArm ctx tid (receiverBoundNotification st1 tid) executingCore st1
        else .ok ((), st1) : Except KernelError (Unit × SystemState)) with
      | .ok r => .ok r
      | .error e => .error (e, st) := by
  split
  · rw [notificationWaitGatedR_eq]
    unfold RefusalCarrying.ofKernel
    rcases completeSignalArm ctx tid (receiverBoundNotification st1 tid) executingCore st1 with
      _ | _ <;> rfl
  · rfl

theorem replyRecvSignalArmR_eq (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (rcap : Capability)
    (rid : SeLe4n.ReplyId) (c : SeLe4n.ThreadId) (st : SystemState)
    (hTgt : rcap.target = .replyCap rid) (hAns : replyAnsweredCaller? st rid = some c)
    (hFlow : securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf c) = true) :
    replyRecvSignalArmR ctx layout rf len extraCaps label tid executingCore rcap st =
      match replyRecvCompletesSignalArm ctx tid c label
          { registers := Architecture.regMessageBody layout rf len, badge := rcap.badge }
          (rcap.rights.mem .grant) executingCore st with
      | .ok r => .ok r
      | .error e => .error (e, st) := by
  unfold replyRecvSignalArmR replyRecvCompletesSignalArm
  rw [endpointReplyCheckedArmR_eq_general (keep := true)]
  unfold endpointReplyCheckedArmGeneralR
  rw [hTgt]
  dsimp only
  rw [hAns]
  dsimp only
  rw [if_pos hFlow]
  rw [replyTransferOnCoreChecked_congr_words ctx tid c
    { length := len, extraCaps := extraCaps, label := label }
    (replyRecvReplyMessageInfo label
      { registers := Architecture.regMessageBody layout rf len, badge := rcap.badge })
    (Architecture.regMessageRegs layout rf) (Architecture.regMessageBody layout rf len) _ _ _ st
    rfl (fun i fb hi => replyWordOr_regMessageRegs_body layout rf len extraCaps label i fb hi) true]
  have hMsg : ({ registers := extractMessageRegisters (Architecture.regMessageRegs layout rf) { length := len, extraCaps := extraCaps, label := label }, badge := rcap.badge } : IpcMessage) =
      { registers := Architecture.regMessageBody layout rf len, badge := rcap.badge } := rfl
  rw [hMsg]
  rcases replyTransferOnCoreChecked ctx tid c _ _
      { registers := Architecture.regMessageBody layout rf len, badge := rcap.badge }
      (rcap.rights.mem .grant) executingCore st true with e | ⟨⟨⟩, st1⟩
  · rfl
  · exact replyRecvSignalLeg_eq ctx tid executingCore st st1

theorem endpointReplyRecvCheckedArmR_eq_general (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability) :
    endpointReplyRecvCheckedArmR ctx layout rf len extraCaps label tid executingCore cap =
      endpointReplyRecvCheckedArmRegsR ctx layout rf len extraCaps label tid executingCore cap := by
  funext st
  unfold endpointReplyRecvCheckedArmR endpointReplyRecvCheckedArmRegsR
    endpointReplyRecvCheckedArmGeneralR
  cases hTgt : cap.target with
  | object epId =>
    dsimp only
    have hExt : extractMessageRegisters (Architecture.regMessageRegs layout rf)
        { length := len, extraCaps := extraCaps, label := label } =
        Architecture.regMessageBody layout rf len := rfl
    rw [hExt]
    split
    · rfl
    · rw [callerExtraCapsFailK_eq, callerExtraCapsFailK_eq]
      cases callerExtraCapsFault? st tid extraCaps with
      | some _ => rfl
      | none =>
      dsimp only
      rw [resolveReplyRecvK_eq_of st tid _ _ _ _ _ (fun rid c badge grant =>
        replyRecvResolvedR ctx epId tid c rid badge grant layout rf len label executingCore
          (fun st' => match replyRecvCompletesSignalArm ctx tid c label
              { registers := Architecture.regMessageBody layout rf len, badge := badge } grant
              executingCore st' with
            | .ok r => .ok r
            | .error e => .error (e, st')) st)
        (fun rcap rid c hT hA hAns => by
          have hAns' : replyRecvReplyAnswers ctx st tid c = true := hAns
          have hFlow := (Bool.and_eq_true _ _).mp hAns' |>.1
          unfold replyRecvResolvedR
          rw [replyRecvSignalArmR_eq ctx layout rf len extraCaps label tid executingCore rcap rid
            c st hT hA hFlow]
          all_goals rfl)]
      cases resolveReplyRecvReplyR st tid (SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf layout.replyReg)) with
      | error e => rfl
      | ok r =>
        cases r with
        | none => rfl
        | some r =>
        obtain ⟨rid, c, badge, grant⟩ := r
        unfold replyRecvResolvedR replyRecvAnsweredReply?
        dsimp only
        split
        · next hFlow =>
          try dsimp only
          by_cases hSig : receiveCompletesSignal ctx st tid = true
          · simp -iota only [hSig, ↓reduceIte]; rfl
          simp -iota only [hSig, Bool.false_eq_true, ↓reduceIte]
          split
          · next hFault =>
            rw [replyRecvCallFaultArmR_eq epId tid c rid badge grant layout rf len label
              executingCore st hFault]
            unfold replyRecvRendezvousR
            all_goals rfl
          rename_i hNoFault
          split
          · next hG =>
            simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hG
            obtain ⟨⟨hSz, hK⟩, hI⟩ := hG
            obtain ⟨ct, rt, ep, rp, hAd, hT, hRO, hE, hS, hR, hEnq, hRp, hStash, hRecR, hTail⟩ :=
              replyRecvBlockArmCode_spec hK
            have hInert := replyRecvReplyInertW_spec hI hT
            have h := replyRecvOnCore_arm_deliveredRegs _ st epId tid c rid layout rf len badge grant
              executingCore ct rt ep rp hAd hSz hT hRO hE hS hR hEnq hRp hStash hRecR hInert
            rw [replyRecvTransferOnCoreR_eq_match]
            rw [replyRecvTransferOnCore_of_no_fault (h := by simpa using hNoFault)
              (hA := hAd.popAdmits hT hRO), hTail]
            generalize endpointReplyRecvOnCore epId tid rid c
              { registers := Architecture.regMessageBody layout rf len, badge := badge } grant
              executingCore st = r at h ⊢
            rcases r with e | ⟨a, st'⟩
            · cases h
            · simp only [Except.ok.injEq] at h ⊢
              exact h.symm
          rw [replyRecvArmCallTakeR_eq epId tid c rid badge grant layout rf len label executingCore
            st (by simpa using hNoFault)]
          unfold replyRecvRendezvousR
          all_goals rfl
        · rfl
  | _ => rfl

theorem endpointReplyRecvCheckedArmR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (st : SystemState)
    (hRR : decoded.syscallId = .replyRecv)
    (hRegs : Architecture.regMessageRegs layout rf = decoded.msgRegs)
    (hReply : decoded.replyCPtr = SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf layout.replyReg))
    (hCaller : gate.callerId = tid)
    (hRoot : gate.cspaceRootCap = callerCspaceRoot st tid) :
    endpointReplyRecvCheckedArmR ctx layout rf decoded.msgInfo.length decoded.msgInfo.extraCaps
        decoded.msgInfo.label tid executingCore cap st =
      RefusalCarrying.ofKernelReporting
        (replyRecvArmReport ctx tid decoded.msgInfo decoded.msgRegs
          decoded.replyCPtr executingCore cap)
        (dispatchWithCapChecked ctx decoded tid executingCore gate cap) st := by
  rw [endpointReplyRecvCheckedArmR_eq_general]
  unfold endpointReplyRecvCheckedArmRegsR
  rw [hRegs, ← hReply]
  exact endpointReplyRecvCheckedArmGeneralR_eq ctx decoded tid executingCore gate cap st hRR
    hCaller hRoot

theorem replyRecvReplyLegEdges_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (tcb : TCB)
    (hTcb : st.getObject? tid.toObjId = some (.tcb tcb))
    (hReply : decoded.replyCPtr = SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf layout.replyReg)) :
    replyRecvReplyLegEdges st tid decoded =
      match replyRecvTaintCallerCode st tid layout rf decoded.msgInfo.extraCaps with
      | 0 => []
      | k + 1 => [{ sink := (⟨k⟩ : SeLe4n.ThreadId).toObjId, source := tid.toObjId }] := by
  have hCR : callerCspaceRoot st tid = tcb.spaceCells[0] := by
    unfold callerCspaceRoot; rw [hTcb]
  have hTcb' : st.getTcb? tid = some tcb :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr
      (by rw [← SystemState.getObject?_eq_getElem]; exact hTcb)
  have hOp : ∀ p, syscallOperandCap? st tid p =
      match lookupSlot tcb p st with
      | .error _ => none
      | .ok ref => SystemState.lookupSlotCap st ref := by
    intro p
    unfold syscallOperandCap?
    rw [hTcb']
    rfl
  unfold replyRecvReplyLegEdges replyRecvTaintCallerCode
  rw [callerExtraCapsFailK_eq]
  cases callerExtraCapsFault? st tid decoded.msgInfo.extraCaps with
  | some _ => rfl
  | none =>
  dsimp only [Option.isSome_none]
  rw [if_neg Bool.false_ne_true, hReply, hOp, hCR]
  unfold lookupSlot
  cases tcb.spaceCells[0] with
  | none => rfl
  | some root =>
  dsimp only
  rw [lookupSlotFromK_eq]
  cases lookupSlotFrom root _ st with
  | error e => rfl
  | ok ref =>
    dsimp only
    cases SystemState.lookupSlotCap st ref with
    | none => rfl
    | some rc =>
      dsimp only
      cases rc.target <;> try rfl
      rename_i rid
      unfold replyTaintEdges
      dsimp only
      cases st.getReply? rid with
      | none => rfl
      | some r =>
        dsimp only [Option.bind_some]
        unfold Reply.caller
        cases r.callerCode <;> rfl

theorem replyRecvTaintStep_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (hRR : decoded.syscallId = .replyRecv)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (tcb : TCB)
    (hTcb : st.getObject? tid.toObjId = some (.tcb tcb))
    (hReply : decoded.replyCPtr = SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf layout.replyReg))
    (preEpoch : Nat) (preLength : Nat) (wN wS : Capability → TaintWords) (wT : TaintWords)
    (hN : ∀ cap, (wN cap).decode =
      st.declassificationTaint (notifObjOfCode (receiveTaintSignalCode st tid cap)))
    (hS : ∀ cap, (wS cap).decode =
      st.declassificationTaint (threadObjOfCode (receiveTaintSourceCode st cap)))
    (hT : wT.decode = st.declassificationTaint tid.toObjId)
    (post : SystemState) :
    applySyscallTaintAfter (syscallTaintPlan st tid decoded) preEpoch preLength
        st.declassificationTaint post =
      (match syscallOperandCap? st tid decoded.capAddr with
        | some cap => replyRecvTaintStep (receiveTaintSignalCode st tid cap)
            (receiveTaintSourceCode st cap)
            (replyRecvTaintCallerCode st tid layout rf decoded.msgInfo.extraCaps) tid
              (wN cap) (wS cap)
            wT post
        | none => sendTaintStep (replyRecvTaintCallerCode st tid layout rf decoded.msgInfo.extraCaps)
            tid wT post) := by
  simp -iota only [syscallTaintPlan, contentFlowClass, hRR, contentFlowEdges, contentFlowClears,
    contentFlowBypassed, replyRecvOperandFreeEdges, ↓reduceIte]
  dsimp only
  rcases syscallOperandCap? st tid decoded.capAddr with _ | cap
  · simp -iota only [replyRecvReplyLegEdges_eq st tid decoded layout rf tcb hTcb hReply]
    dsimp only
    generalize replyRecvTaintCallerCode st tid layout rf decoded.msgInfo.extraCaps = k
    cases k <;>
      simp [sendTaintStep, applySyscallTaintAfter, syscallRecordsDeclassification,
        applyOrigination, applyTaintClears, applyTaintFlow, applyTaintStep,
        joinTaintAt_toWords_of_decode _ _ hT]
  · have h := hS cap
    have hN := hN cap
    rcases cap with ⟨target, _, _⟩
    cases target with
    | object epId =>
      simp -iota only [receiveTaintSourceCode, receiveTaintSignalCode, receiverTaintEdges,
        boundSignalTaintEdges,
        replyRecvReplyLegEdges_eq st tid decoded layout rf tcb hTcb hReply,
        replyRecvTaintStep] at h hN ⊢
      dsimp only at h hN ⊢
      generalize replyRecvTaintCallerCode st tid layout rf decoded.msgInfo.extraCaps = k
      revert h hN
      generalize boundSignalTaintCode st tid = sc
      cases st.getEndpoint? epId with
      | none =>
        cases sc <;> cases k <;> intro _ hn <;> (try dsimp only at hn ⊢) <;>
          simp only [notifObjOfCode, Nat.add_sub_cancel] at hn <;>
          simp [receiveTaintStep, sendTaintStep, applySyscallTaintAfter,
            syscallRecordsDeclassification, applyOrigination, applyTaintClears, applyTaintFlow,
            applyTaintStep, joinTaintAt_toWords_of_decode _ _ hT,
            joinTaintAt_toWords_of_decode _ _ hn]
      | some ep =>
        simp -iota only [Option.bind_some, ← Endpoint.ofOptCode_sendHeadCode]
        dsimp only
        cases sc <;> cases ep.sendHeadCode <;> cases k <;> intro h hn <;>
          (try dsimp only at h hn ⊢) <;>
          simp only [threadObjOfCode, notifObjOfCode, Nat.add_sub_cancel] at h hn <;>
          simp [receiveTaintStep, sendTaintStep, SeLe4n.ThreadId.ofOptCode,
            applySyscallTaintAfter, syscallRecordsDeclassification, applyOrigination,
            applyTaintClears, applyTaintFlow, applyTaintStep,
            joinTaintAt_toWords_of_decode _ _ hT, joinTaintAt_toWords_of_decode _ _ h,
            joinTaintAt_toWords_of_decode _ _ hn]
    | _ =>
      simp -iota only [receiveTaintSourceCode, receiveTaintSignalCode, replyRecvTaintStep,
        replyRecvReplyLegEdges_eq st tid decoded layout rf tcb hTcb hReply]
      dsimp only
      generalize replyRecvTaintCallerCode st tid layout rf decoded.msgInfo.extraCaps = k
      cases k <;>
        simp [receiveTaintStep, sendTaintStep, applySyscallTaintAfter,
          syscallRecordsDeclassification, applyOrigination, applyTaintClears, applyTaintFlow,
          applyTaintStep, joinTaintAt_toWords_of_decode _ _ hT]

theorem replyRecvOperandArmThenTaintR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId)
    (preEpoch : Nat) (preLength : Nat)
    (st : SystemState) (tcb : TCB) (ref : CSpaceAddr)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (hRR : decoded.syscallId = .replyRecv)
    (hRegs : Architecture.regMessageRegs layout rf = decoded.msgRegs)
    (hReply : decoded.replyCPtr = SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf layout.replyReg))
    (hTcb : st.getObject? tid.toObjId = some (.tcb tcb))
    (hRef : lookupSlot tcb decoded.capAddr st = .ok ref)
    (hOrd : replyRecvAnsweringReply? ctx (replyRecvCallerGate decoded tid tcb) decoded tid st = none ∨
      ∃ epId, replyRecvReceiveEndpoint ctx (replyRecvCallerGate decoded tid tcb) tid st = .ok epId) :
    replyRecvOperandArmThenTaintR ctx layout rf decoded.msgInfo.length decoded.msgInfo.extraCaps
        decoded.msgInfo.label tid executingCore
        (syscallRequiredRight decoded.syscallId) (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernelReporting
        (replyRecvOperandReport ctx tid decoded.msgInfo decoded.msgRegs
          decoded.replyCPtr executingCore (syscallRequiredRight decoded.syscallId)
          (SystemState.lookupSlotCap st ref))
        (dispatchCheckedArmThenTaint ctx decoded tid executingCore
        { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr, requiredRight := syscallRequiredRight decoded.syscallId } none
        (syscallTaintPlan st tid decoded) preEpoch preLength st.declassificationTaint) st := by
  have hOperand := syscallOperandCap?_of_resolved st tid _ tcb ref hTcb hRef
  simp -iota only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernelReporting]
  rw [dispatchSyscallArmChecked_of_entryOrder
    (gate := { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr, requiredRight := syscallRequiredRight decoded.syscallId })
    (Or.inr hOrd) (fun _ => rfl)]
  simp -iota only [hRR, syscallInvokeTyped, syscallResolveCap, SyscallGate.lookupSlot_mk, hRef]
  dsimp only
  simp -iota only [replyRecvTaintStep_eq st tid decoded hRR layout rf tcb hTcb hReply
    (wN := fun cap => st.taintWordsAt (notifObjOfCode (receiveTaintSignalCode st tid cap)))
    (wS := fun cap => st.taintWordsAt (threadObjOfCode (receiveTaintSourceCode st cap)))
    (wT := st.taintWordsAt tid.toObjId) (hN := fun _ => decode_taintWordsAt st _)
    (hS := fun _ => decode_taintWordsAt st _)
    (hT := decode_taintWordsAt st _), hOperand]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · unfold replyRecvOperandArmThenTaintR replyRecvOperandReport
    dsimp only
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
    · simp -iota only [hIdle, ↓reduceIte]
      rfl
    · simp -iota only [hIdle, Bool.false_eq_true, ↓reduceIte]
      dsimp only
      by_cases hType : syscallTargetAccepted .replyRecv st cap = false
      · simp -iota only [hType, Bool.not_false, ↓reduceIte]
        rfl
      replace hType : syscallTargetAccepted .replyRecv st cap = true := by simpa using hType
      by_cases hRight : cap.hasRight (syscallRequiredRight .replyRecv) = true
      · simp -iota only [hType, Bool.not_true, Bool.false_eq_true, hRight, ↓reduceIte,
          withTaintWordsAt_eq, TaintWords.mk_fields]
        rw [endpointReplyRecvCheckedArmR_eq ctx decoded tid executingCore
          { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr, requiredRight := syscallRequiredRight decoded.syscallId }
          cap layout rf st hRR hRegs hReply rfl (by unfold callerCspaceRoot; rw [hTcb])]
        unfold RefusalCarrying.ofKernelReporting
        simp -iota only [hRR]
        rcases dispatchWithCapChecked ctx decoded tid executingCore
          { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr, requiredRight := syscallRequiredRight .replyRecv }
          cap st with _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp -iota only [hType, Bool.not_true, Bool.false_eq_true, hRight, ↓reduceIte]
        rfl

/-- WS-ZA ZA4.7: the reply-receive's dispatch: `dispatchOperandCheckedR` with
the reply-receive's arm (`dispatchReplyRecvCheckedR_eq`).

A specification: the compiled entry runs the arm out of line
(`syscallEntryRoutedK`), so no code is generated for it. -/
noncomputable def dispatchReplyRecvCheckedR (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (xc : Nat) : RefusalCarrying Unit :=
  replyRecvRoutedR ctx
    (replyRecvRoutedDecode capAddr (Architecture.regMessageRegs layout rf)
      (SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf layout.replyReg)) len extraCaps label)
    tid executingCore
    (dispatchOperandCheckedR capAddr tid executingCore xc
      (replyRecvOperandArmThenTaintR ctx layout rf len extraCaps label tid executingCore
        (syscallRequiredRight .replyRecv)))

theorem dispatchReplyRecvCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (hRR : decoded.syscallId = .replyRecv)
    (hRegs : Architecture.regMessageRegs layout rf = decoded.msgRegs)
    (hReply : decoded.replyCPtr = SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf layout.replyReg)) :
    dispatchReplyRecvCheckedR ctx decoded.capAddr layout rf decoded.msgInfo.length
        decoded.msgInfo.extraCaps decoded.msgInfo.label tid executingCore (syscallExtraCapCount decoded.syscallId decoded.msgInfo.extraCaps) =
      RefusalCarrying.ofKernelReporting
        (replyRecvRoutedReport ctx decoded tid executingCore
          (operandReport decoded.capAddr tid executingCore
            (syscallExtraCapCount decoded.syscallId decoded.msgInfo.extraCaps)
            (replyRecvOperandReport ctx tid decoded.msgInfo decoded.msgRegs
              decoded.replyCPtr executingCore (syscallRequiredRight .replyRecv))))
        (dispatchSyscallChecked ctx decoded tid executingCore) := by
  funext st
  unfold dispatchReplyRecvCheckedR
  rw [hRegs, ← hReply, replyRecvRoutedDecode_eq_norm hRR, replyRecvRoutedR_norm]
  apply replyRecvRoutedR_eq hRR
  intro hOrd
  apply dispatchOperandCheckedR_eq_reporting_at ctx decoded tid executingCore _ _
    (by rw [hRR]; decide) st
  · intro tcb ref hTcb hRef
    have hArm := replyRecvOperandArmThenTaintR_eq ctx decoded tid executingCore
      st.declassificationAuditEpoch st.declassificationAudit.length
      st tcb ref layout rf hRR hRegs hReply hTcb hRef (hOrd tcb hTcb)
    simp only [hRR] at hArm ⊢
    exact hArm
  · exact fun tcb hTcb => Or.inr (hOrd tcb hTcb)

/-- **The reply-receive's arm refuses a receive capability the entry refuses,
on the state it was handed** (WS-SX SX36.1): its reserved-object, type and
right checks and its flow gate (`endpointReplyRecvCheckedArmR`) all run before
any write, so a capability one of them refuses comes back with the state
unchanged.  Unconditional. -/
theorem replyRecvOperandArmThenTaintR_refuses_unchanged (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability)
    (st : SystemState)
    (hRef : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true ∨
      syscallTargetAccepted .replyRecv st cap = false ∨
      cap.hasRight (syscallRequiredRight .replyRecv) = false ∨
      ∀ epId, cap.target = .object epId →
        endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) = false) :
    ∃ e, replyRecvOperandArmThenTaintR ctx layout rf len extraCaps label tid executingCore
      (syscallRequiredRight .replyRecv) (some cap) st = .error (e, st) := by
  unfold replyRecvOperandArmThenTaintR
  dsimp only
  by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
  · exact ⟨_, by rw [if_pos hIdle]⟩
  rw [if_neg hIdle]
  cases hA : syscallTargetAccepted .replyRecv st cap
  · exact ⟨_, rfl⟩
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hRt : cap.hasRight (syscallRequiredRight .replyRecv)
  · exact ⟨_, rfl⟩
  have hFl : ∀ epId, cap.target = .object epId →
      endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) = false := by
    rcases hRef with h | h | h | h
    · exact absurd h hIdle
    · rw [hA] at h; cases h
    · rw [hRt] at h; cases h
    · exact h
  simp only [↓reduceIte, withTaintWordsAt_eq]
  unfold endpointReplyRecvCheckedArmR
  cases hT : cap.target with
  | object epId =>
    dsimp only
    rw [hFl epId hT]
    exact ⟨_, rfl⟩
  | _ => exact ⟨_, rfl⟩

/-- **Today's reply-receive route refuses wherever the after-reply route runs,
on the state it was handed** (WS-SX SX36.1): where the reply answers and the
entry refuses the receive capability (`replyRecvRefusedOnEntry?`), the operand
route on the entry state (`dispatchOperandCheckedR` over the reply-receive's
arm) refuses with nothing written: the operand's lookup, its empty slot, or
the arm's reserved-object, type, right or flow refusal
(`replyRecvOperandArmThenTaintR_refuses_unchanged`).  Unconditional: no
invariant of the state is read. -/
theorem dispatchOperandCheckedR_replyRecv_refuses_of_refusedOnEntry (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (xc : Nat) (st : SystemState)
    (hSid : decoded.syscallId = .replyRecv) {q}
    (h : replyRecvRefusedOnEntry? ctx decoded tid st = some q) :
    ∃ e, dispatchOperandCheckedR decoded.capAddr tid executingCore xc
      (replyRecvOperandArmThenTaintR ctx layout rf len extraCaps label tid executingCore
        (syscallRequiredRight .replyRecv)) st = .error (e, st) := by
  unfold dispatchOperandCheckedR
  dsimp only
  by_cases hC : (!(st.scheduler.currentOnCore executingCore).isEqSome tid) = true
  · exact ⟨_, by rw [if_pos hC]⟩
  rw [if_neg hC]
  cases hT : st.getObject? tid.toObjId with
  | none => exact ⟨_, rfl⟩
  | some o =>
    cases o with
    | tcb tcb =>
      dsimp only
      have hE : ∃ e, replyRecvReceiveEndpoint ctx (replyRecvCallerGate decoded tid tcb) tid st =
          .error e := by
        unfold replyRecvRefusedOnEntry? at h
        rw [hT] at h
        dsimp only at h
        cases hA : replyRecvAnsweringReply? ctx (replyRecvCallerGate decoded tid tcb) decoded tid st with
        | none => rw [hA] at h; cases h
        | some a =>
          rw [hA] at h
          obtain ⟨rid, pc, b, g⟩ := a
          dsimp only at h
          cases hR : replyRecvReceiveEndpoint ctx (replyRecvCallerGate decoded tid tcb) tid st with
          | error e => exact ⟨e, rfl⟩
          | ok _ => rw [hR] at h; cases h
      obtain ⟨e, hE⟩ := hE
      rw [lookupSlotK_eq]
      unfold replyRecvReceiveEndpoint syscallResolveCap at hE
      simp only [replyRecvCallerGate, SyscallGate.lookupSlot_mk] at hE
      cases hL : lookupSlot tcb decoded.capAddr st with
      | error f => exact ⟨_, rfl⟩
      | ok ref =>
        dsimp only
        rw [hL] at hE
        dsimp only at hE
        cases hX : extraCapsLookupFault? st tcb xc with
        | some p => exact ⟨_, rfl⟩
        | none =>
          dsimp only
          cases hS : SystemState.lookupSlotCap st ref with
          | none => exact ⟨_, rfl⟩
          | some cap =>
            simp only [capHeldNone]
            rw [hS] at hE
            dsimp only at hE
            by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
            · exact ⟨_, by rw [if_pos hIdle]⟩
            rw [if_neg hIdle]
            rw [if_neg hIdle] at hE
            dsimp only at hE
            apply replyRecvOperandArmThenTaintR_refuses_unchanged
            cases hA : syscallTargetAccepted .replyRecv st cap
            · exact .inr (.inl rfl)
            rw [hA] at hE
            cases hRt : cap.hasRight (syscallRequiredRight .replyRecv)
            · exact .inr (.inr (.inl rfl))
            refine .inr (.inr (.inr fun epId hTg => ?_))
            simp only [hSid, hRt, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hTg] at hE
            cases hF : endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid)
            · rfl
            · rw [hF] at hE; cases hE
    | _ => exact ⟨_, rfl⟩

/-! ### The long reply-receive -/

/-- The long take arm is the specification's path, the replier's frame asking
for its routed capabilities under the grant right (`hReqOf`). -/
theorem replyRecvLongTakeArmR_eq (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (rf : SeLe4n.RegisterFile) (len label : Nat) (executingCore : Concurrency.CoreId)
    (st : SystemState) (hLen : 5 ≤ len)
    (hSzL : ¬ (longReplyRecvRegs rf st tid len).size > maxMessageRegisters)
    (hReqOf : ∀ stcb, st.getTcb? tid = some stcb →
      replyCapRequest st tid true = frameCapRequestOf st stcb (routedExtraCaps rf)) :
    replyRecvLongTakeArmR epId tid c rid badge grant rf len label executingCore st =
      replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st := by
  unfold replyRecvLongTakeArmR
  split
  · next hA =>
    unfold replyRecvLongTakeAdmits at hA
    simp -iota only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hA
    obtain ⟨hNoF, hK⟩ := hA
    obtain ⟨ct, rp, ep, s, sTcb, hAd, hT, hRO, hRp, hEp, hH, hTs, hSC, hF, hG⟩ :=
      replyRecvTakeArmCode_spec hK
    have hE := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp
    have hS := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTs
    rw [hEp]
    dsimp only
    rw [hH]
    dsimp only
    rw [hTs]
    dsimp only
    cases hR : Architecture.RegisterDecode.registerRoutedSyscallOf
        (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
        SeLe4n.arm64DefaultLayout sTcb.registerContext
    case send capAddr mi =>
      dsimp only
      have hR' := (Architecture.RegisterDecode.registerRoutedSyscall_default _).trans hR
      split
      · next hI =>
        have h := replyRecvOnCore_arm_takeDeliveredLong _ st epId tid c rid rf len badge grant
          executingCore ct rp ep s sTcb capAddr mi hAd hLen hSzL hT hRO hRp
          (replyRecvReplyInertW_spec hI hT) hE hH hS hSC hG hR' hF
        rw [Architecture.regMessageFrameW_eq, ← TCB.ipcBadgeView_eq_opt]
        unfold replyRecvLongRendezvousR
        rw [replyRecvTransferOnCoreR_eq_match]
        rw [replyRecvTransferOnCore_of_no_fault (h := hNoF) (hA := hAd.popAdmits hT hRO)]
        generalize endpointReplyRecvOnCore epId tid rid c
          { registers := longReplyRecvRegs rf st tid len, badge := badge } grant
          executingCore st = r at h ⊢
        rcases r with e | ⟨a, st'⟩
        · cases h
        · simp only [Except.ok.injEq] at h ⊢
          exact h.symm
      · split
        · next hGr =>
          subst hGr
          cases hS' : st.getTcb? tid with
          | none => rfl
          | some stcb =>
            dsimp only
            cases hTc0 : st.getTcb? c with
            | none => rfl
            | some ct0 =>
              dsimp only
              have hTc0' := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc0
              obtain rfl : ct = ct0 := by rw [hT] at hTc0'; cases hTc0'; rfl
              have h := replyRecvOnCore_arm_takeCapsDeliveredLong _ st epId tid c rid rf len badge
                executingCore ct rp ep s sTcb capAddr mi stcb _ hAd hLen hSzL hT hRO
                hRp hE hH hS hSC hG hR' hF (hReqOf stcb hS')
              rw [Architecture.regMessageFrameW_eq, ← TCB.ipcBadgeView_eq_opt]
              unfold replyRecvLongRendezvousR
              rw [replyRecvTransferOnCoreR_eq_match]
              rw [replyRecvTransferOnCore_of_no_fault (h := hNoF) (hA := hAd.popAdmits hT hRO)]
              generalize endpointReplyRecvOnCore epId tid rid c
                { registers := longReplyRecvRegs rf st tid len, badge := badge } true
                executingCore st = r at h ⊢
              rcases r with e | ⟨a, st'⟩
              · cases h
              · simp only [Except.ok.injEq] at h ⊢
                exact h.symm
        · rfl
    all_goals rfl
  · rfl

/-- The long Call-take arm is the specification's path, the replier's frame
asking for its routed capabilities under the grant right (`hReqOf`). -/
theorem replyRecvLongCallTakeArmR_eq (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (rf : SeLe4n.RegisterFile) (len label : Nat) (executingCore : Concurrency.CoreId)
    (st : SystemState) (hLen : 5 ≤ len)
    (hSzL : ¬ (longReplyRecvRegs rf st tid len).size > maxMessageRegisters)
    (hReqOf : ∀ stcb, st.getTcb? tid = some stcb →
      replyCapRequest st tid true = frameCapRequestOf st stcb (routedExtraCaps rf)) :
    replyRecvLongCallTakeArmR epId tid c rid badge grant rf len label executingCore st =
      replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st := by
  unfold replyRecvLongCallTakeArmR
  split
  · next hA =>
    simp -iota only [replyRecvLongCallTakeAdmits, Bool.and_eq_true, Bool.or_eq_true,
      Bool.not_eq_true', bne_iff_ne, ne_eq] at hA
    obtain ⟨⟨hNoF, hK⟩, hShape⟩ := hA
    obtain ⟨ct, rp, ep, s, sTcb, capAddr, mi, hAd, hCA, hT, hRO, hRp, hEp, hH, hTs, hSC, hF, hRt⟩ :=
      replyRecvCallTakeArmCode_spec hK
    have hE := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp
    have hS := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTs
    have hTc := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
    have hR' := (Architecture.RegisterDecode.registerRoutedSyscall_default _).trans hRt
    unfold replyRecvLongCallTakeAnswer
    rw [hEp]
    dsimp only
    rw [hH]
    dsimp only
    rw [hTs]
    dsimp only
    rw [hRt]
    dsimp only
    split
    · next hI =>
      have h := replyRecvOnCore_arm_callTakeDeliveredLong _ _ st epId tid c rid rf len badge grant
        executingCore ct rp ep s sTcb capAddr mi hAd hCA hLen hSzL hT hRO hRp
        (replyRecvReplyInertW_spec hI hT) hE hH hS hSC hR' hF
      unfold replyRecvLongRendezvousR
      rw [replyRecvTransferOnCoreR_eq_match]
      rw [replyRecvTransferOnCore_of_no_fault (h := hNoF) (hA := hAd.popAdmits hT hRO)]
      generalize endpointReplyRecvOnCore epId tid rid c
        { registers := longReplyRecvRegs rf st tid len, badge := badge } grant
        executingCore st = r at h ⊢
      rcases r with e | ⟨a, st'⟩
      · cases h
      · simp only [Except.ok.injEq] at h ⊢
        exact h.symm
    · next hI =>
      obtain ⟨rfl, hTid⟩ : grant = true ∧ (st.getTcb? tid).isSome = true := by
        rcases hShape with h | h
        · exact absurd h hI
        · simpa only [Bool.and_eq_true] using h
      obtain ⟨stcb, hS'⟩ := Option.isSome_iff_exists.mp hTid
      rw [hS']
      dsimp only
      rw [hTc]
      dsimp only
      have h := replyRecvOnCore_arm_callTakeCapsDeliveredLong _ _ st epId tid c rid rf len
        badge executingCore ct rp ep s sTcb capAddr mi stcb _ hAd hCA hLen hSzL hT hRO
        hRp hE hH hS hSC hR' hF (hReqOf stcb hS')
      unfold replyRecvLongRendezvousR
      rw [replyRecvTransferOnCoreR_eq_match]
      rw [replyRecvTransferOnCore_of_no_fault (h := hNoF) (hA := hAd.popAdmits hT hRO)]
      generalize endpointReplyRecvOnCore epId tid rid c
        { registers := longReplyRecvRegs rf st tid len, badge := badge } true
        executingCore st = r at h ⊢
      rcases r with e | ⟨a, st'⟩
      · cases h
      · simp only [Except.ok.injEq] at h ⊢
        exact h.symm
  · exact replyRecvLongTakeArmR_eq epId tid c rid badge grant rf len label executingCore st hLen
      hSzL hReqOf

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
    simp -iota only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hG
    obtain ⟨⟨hGr, hNoFault⟩, hK⟩ := hG
    subst hGr
    obtain ⟨ct, rt, ep, rp, hAd, hT, hRO, hE, hS, hR', hEnq, hRp, hStash, hRecR, hTail⟩ :=
      replyRecvBlockArmCode_spec hK
    cases hS' : st.getTcb? tid with
    | none => rfl
    | some stcb =>
      dsimp only
      cases hTc0 : st.getTcb? c with
      | none => rfl
      | some ct0 =>
        dsimp only
        obtain rfl : ct = ct0 := by
          rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp hTc0] at hT; cases hT; rfl
        unfold replyRecvLongRendezvousR
        rw [replyRecvTransferOnCoreR_eq_match]
        rw [replyRecvTransferOnCore_of_no_fault (h := hNoFault) (hA := hAd.popAdmits hT hRO)]
        have h := replyRecvOnCore_arm_capsDeliveredLong _ st epId tid c rid rf len badge
          executingCore ct rt ep rp stcb _ hAd hLen hSzL hT hRO hE hS hR' hEnq hRp hStash hRecR
          (hReqOf stcb hS')
        rw [hTail]
        generalize endpointReplyRecvOnCore epId tid rid c
          { registers := longReplyRecvRegs rf st tid len, badge := badge } true
          executingCore st = r at h ⊢
        rcases r with e | ⟨a, st'⟩
        · cases h
        · simp only [Except.ok.injEq] at h ⊢
          exact h.symm
  · exact replyRecvLongCallTakeArmR_eq epId tid c rid badge grant rf len label executingCore st
      hLen hSzL hReqOf

/-- On a faulted caller the long arm is the specification's path. -/
theorem replyRecvLongFaultArmR_eq (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (rf : SeLe4n.RegisterFile) (len label : Nat) (executingCore : Concurrency.CoreId)
    (st : SystemState) (hLen : 4 ≤ len) (hF : threadHasPendingFault st c = true) :
    replyRecvLongFaultArmR epId tid c rid badge grant rf len label executingCore st =
      replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st := by
  unfold replyRecvLongFaultArmR
  cases hTc0 : st.getTcb? c with
  | none => rfl
  | some ct0 =>
    dsimp only
    have hTc0' := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc0
    obtain ⟨tf, hPF⟩ : ∃ tf, ct0.pendingFault = some tf := by
      unfold threadHasPendingFault at hF
      rw [hTc0] at hF
      exact Option.isSome_iff_exists.mp hF
    split
    · next hK =>
      obtain ⟨ct, rt, ep, rp, hAd, hT, hRO, hE, hS, hR, hEnq, hRp, hStash, hRecR, hTail⟩ :=
        replyRecvBlockArmCode_spec (by simpa using hK)
      obtain rfl : ct = ct0 := by
        rw [hT] at hTc0'; cases hTc0'; rfl
      obtain ⟨hEq, hStg⟩ := replyRecvTransferOnCore_arm_fault_inPlaceLong _ st epId tid c rid
        label rf len badge grant executingCore ct rt ep rp tf hAd hLen hPF hT hRO hE hS hR hEnq hRp
        hStash hRecR
      unfold replyRecvLongRendezvousR
      rw [replyRecvTransferOnCoreR_eq_match]
      rw [hEq]
      simp only [CapTransferSummary.capInfo_empty]
      rw [hTail, hStg]
    · split
      · next hTk =>
        obtain ⟨ct, rp, ep, s, sTcb, hAd, hT, hRO, hRp, hEp, hH, hTs, hSC, hFs, hG⟩ :=
          replyRecvTakeArmCode_spec (by simpa using hTk)
        obtain rfl : ct = ct0 := by
          rw [hT] at hTc0'; cases hTc0'; rfl
        have hE := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp
        have hS := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTs
        rw [hEp]
        dsimp only
        rw [hH]
        dsimp only
        rw [hTs]
        dsimp only
        cases hR : Architecture.RegisterDecode.registerRoutedSyscallOf
            (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
            SeLe4n.arm64DefaultLayout sTcb.registerContext
        case send capAddr mi =>
          dsimp only
          have h := replyRecvTransferOnCore_arm_faultTakeLong _ st epId tid c rid label
            rf len badge grant executingCore ct rp ep tf s sTcb capAddr mi hAd hLen hPF hT hRO
            hRp hE hH hS hSC hG
            ((Architecture.RegisterDecode.registerRoutedSyscall_default _).trans hR) hFs
          rw [Architecture.regMessageFrameW_eq, ← TCB.ipcBadgeView_eq_opt]
          unfold replyRecvLongRendezvousR
          rw [replyRecvTransferOnCoreR_eq_match]
          generalize replyRecvTransferOnCore epId tid rid c label
            { registers := longReplyRecvRegs rf st tid len, badge := badge } grant
            executingCore st = r at h ⊢
          rcases r with e | ⟨a, st'⟩
          · cases h
          · simp only [Except.ok.injEq] at h ⊢
            exact h.symm
        all_goals rfl
      · rfl

/-- On a faulted caller the Call-take fault arm is the specification's path. -/
theorem replyRecvLongCallFaultArmR_eq (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (rf : SeLe4n.RegisterFile) (len label : Nat) (executingCore : Concurrency.CoreId) (st : SystemState) (hLen : 4 ≤ len) (hF : threadHasPendingFault st c = true) :
    replyRecvLongCallFaultArmR epId tid c rid badge grant rf len label executingCore st =
      replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st := by
  unfold replyRecvLongCallFaultArmR
  split
  · next hK =>
    obtain ⟨ct, rp, ep, s, sTcb, capAddr, mi, hAd, hCA, hT, hRO, hRp, hEp, hH, hTs, hSC, hFs,
      hRt⟩ := replyRecvCallTakeArmCode_spec (by simpa using hK)
    have hTc := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
    obtain ⟨tf, hPF⟩ : ∃ tf, ct.pendingFault = some tf := by
      unfold threadHasPendingFault at hF
      rw [hTc] at hF
      exact Option.isSome_iff_exists.mp hF
    have hE := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp
    have hS := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTs
    unfold replyRecvLongCallFaultTakeAnswer
    simp only [hTc, hEp, hH, hTs, hRt]
    have h := replyRecvTransferOnCore_arm_callFaultTakeLong _ _ st epId tid c rid label rf len
      badge grant executingCore ct rp ep tf s sTcb capAddr mi hAd hCA hLen hPF hT hRO hRp hE hH hS
      hSC ((Architecture.RegisterDecode.registerRoutedSyscall_default _).trans hRt) hFs
    unfold replyRecvLongRendezvousR
    rw [replyRecvTransferOnCoreR_eq_match]
    generalize replyRecvTransferOnCore epId tid rid c label
      { registers := longReplyRecvRegs rf st tid len, badge := badge } grant
      executingCore st = r at h ⊢
    rcases r with e | ⟨a, st'⟩
    · cases h
    · simp only [Except.ok.injEq] at h ⊢
      exact h.symm
  · exact replyRecvLongFaultArmR_eq epId tid c rid badge grant rf len label executingCore st hLen hF

/-- **A cut of the reply's words decodes as the words it was cut from**, on
every word a fault decode reads (`Architecture.decodeFaultReply_congr`): the
words below the cut are the same words, and the declared length covers them on
both readings. -/
theorem replyWordOr_extractMessageRegisters (mi mi' : MessageInfo)
    (regs : Array SeLe4n.RegValue) (i : Nat) (fb : UInt64) (hi : i < maxMessageRegisters)
    (hmi : mi'.length = (extractMessageRegisters regs mi).size) :
    Architecture.replyWordOr mi regs i fb =
      Architecture.replyWordOr mi' (extractMessageRegisters regs mi) i fb := by
  unfold Architecture.replyWordOr
  rw [hmi, Nat.min_self]
  unfold extractMessageRegisters Architecture.wordAt
  simp only [Array.size_extract]
  by_cases h : i < min mi.length regs.size
  · have h' : i < min (min mi.length (min maxMessageRegisters regs.size)) regs.size - 0 := by
      omega
    rw [if_pos h, if_pos h', Array.getElem?_extract]
    simp only [Nat.zero_add]
    rw [if_pos h']
  · have h' : ¬ i < min (min mi.length (min maxMessageRegisters regs.size)) regs.size - 0 := by
      omega
    rw [if_neg h, if_neg h']

theorem replyRecvLongSignalArmR_eq (ctx : LabelingContext) (rf : SeLe4n.RegisterFile)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (rcap : Capability) (rid : SeLe4n.ReplyId)
    (c : SeLe4n.ThreadId) (st : SystemState)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall opCode SeLe4n.arm64DefaultLayout rf 32 =
      .replyRecvLong capAddr mi)
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w)
    (hRf : ∀ stcb, st.getTcb? tid = some stcb → stcb.registerContext = rf)
    (hTgt : rcap.target = .replyCap rid) (hAns : replyAnsweredCaller? st rid = some c)
    (hFlow : securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf c) = true) :
    replyRecvLongSignalArmR ctx rf mi.length mi.extraCaps mi.label tid executingCore rcap st =
      match replyRecvCompletesSignalArm ctx tid c mi.label
          { registers := longReplyRecvRegs rf st tid mi.length, badge := rcap.badge }
          (rcap.rights.mem .grant) executingCore st with
      | .ok r => .ok r
      | .error e => .error (e, st) := by
  obtain ⟨hGt, hMax, -⟩ :=
    Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedReplyRecvLong st tid _ rf 32
      capAddr mi hR
  have hSz4 : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  rw [hSz4] at hGt
  have hExt : extractMessageRegisters (longReplyRegs st tid rf mi.length)
      { length := mi.length, extraCaps := mi.extraCaps, label := mi.label } =
      longReplyRecvRegs rf st tid mi.length :=
    congrArg IpcMessage.registers
      (longMessageDecode_message .replyRecv st tid rf capAddr mi none (by omega) hMax)
  unfold replyRecvLongSignalArmR replyRecvCompletesSignalArm
  rw [endpointReplyLongCheckedArmR_eq_general ctx rf capAddr mi tid executingCore rcap st
    .replyRecv (.inr ⟨hR, rfl⟩) hRead hRf true]
  unfold endpointReplyLongGeneralR
  unfold endpointReplyCheckedArmGeneralR
  rw [hTgt]
  dsimp only
  rw [hAns]
  dsimp only
  rw [if_pos hFlow]
  rw [replyTransferOnCoreChecked_congr_words ctx tid c
    { length := mi.length, extraCaps := mi.extraCaps, label := mi.label }
    (replyRecvReplyMessageInfo mi.label
      { registers := longReplyRecvRegs rf st tid mi.length, badge := rcap.badge })
    (longReplyRegs st tid rf mi.length) (longReplyRecvRegs rf st tid mi.length) _ _ _ st rfl
    (fun i fb hi => by
      rw [← hExt]
      exact replyWordOr_extractMessageRegisters _ _ _ i fb
        (by unfold maxMessageRegisters; omega) rfl) true]
  have hMsg : ({ registers := extractMessageRegisters (longReplyRegs st tid rf mi.length) { length := mi.length, extraCaps := mi.extraCaps, label := mi.label }, badge := rcap.badge } : IpcMessage) =
      { registers := longReplyRecvRegs rf st tid mi.length, badge := rcap.badge } := by
    rw [hExt]
  rw [hMsg]
  rcases replyTransferOnCoreChecked ctx tid c _ _
      { registers := longReplyRecvRegs rf st tid mi.length, badge := rcap.badge }
      (rcap.rights.mem .grant) executingCore st true with e | ⟨⟨⟩, st1⟩
  · rfl
  · exact replyRecvSignalLeg_eq ctx tid executingCore st st1

theorem endpointReplyRecvLongCheckedArmR_eq_general (ctx : LabelingContext)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability)
    (st : SystemState)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall opCode SeLe4n.arm64DefaultLayout rf 32 =
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
      ({ registers := (longSendMessage SeLe4n.arm64DefaultLayout rf st tid mi.length none).registers,
         badge := badge } : IpcMessage) =
      { registers := longReplyRecvRegs rf st tid mi.length, badge := badge } := fun _ => rfl
  unfold endpointReplyRecvLongCheckedArmR endpointReplyRecvLongGeneralR
    endpointReplyRecvCheckedArmGeneralR
  cases hTgt : cap.target with
  | object epId =>
    dsimp only
    split
    · rfl
    · rw [callerExtraCapsFailK_eq, callerExtraCapsFailK_eq]
      cases callerExtraCapsFault? st tid mi.extraCaps with
      | some _ => rfl
      | none =>
      dsimp only
      rw [resolveReplyRecvK_eq_of st tid _ _ _ _ _ (fun rid c badge grant =>
        replyRecvLongResolvedR ctx epId tid c rid badge grant rf mi.length mi.label executingCore
          (fun st' => match replyRecvCompletesSignalArm ctx tid c mi.label
              { registers := longReplyRecvRegs rf st' tid mi.length, badge := badge } grant
              executingCore st' with
            | .ok r => .ok r
            | .error e => .error (e, st')) st)
        (fun rcap rid c hT hA hAns => by
          have hAns' : replyRecvReplyAnswers ctx st tid c = true := hAns
          have hFlow := (Bool.and_eq_true _ _).mp hAns' |>.1
          unfold replyRecvLongResolvedR
          rw [replyRecvLongSignalArmR_eq ctx rf capAddr mi tid executingCore rcap rid c st hR
            hRead hRf hT hA hFlow]
          all_goals rfl)]
      cases resolveReplyRecvReplyR st tid
          (SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf SeLe4n.arm64DefaultLayout.replyReg)) with
      | error e => rfl
      | ok r =>
        cases r with
        | none => rfl
        | some r =>
        obtain ⟨rid, c, badge, grant⟩ := r
        unfold replyRecvLongResolvedR replyRecvAnsweredReply?
        dsimp only
        simp -iota only [hExt, hM]
        split
        · next hFlow =>
          try dsimp only
          by_cases hSig : receiveCompletesSignal ctx st tid = true
          · simp -iota only [hSig, ↓reduceIte]; rfl
          simp -iota only [hSig, Bool.false_eq_true, ↓reduceIte]
          split
          · next hFlt =>
            rw [replyRecvLongCallFaultArmR_eq epId tid c rid badge grant rf mi.length mi.label
              executingCore st (by omega) hFlt]
            rfl
          · next hFlt =>
            have hNoFault : threadHasPendingFault st c = false := Bool.eq_false_iff.mpr hFlt
            split
            · next hG =>
              simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hG
              obtain ⟨hK, hI⟩ := hG
              obtain ⟨ct, rt, ep, rp, hAd, hT, hRO, hE, hS, hR, hEnq, hRp, hStash, hRecR, hTail⟩ :=
                replyRecvBlockArmCode_spec hK
              have hInert := replyRecvReplyInertW_spec hI hT
              have hSzL : ¬ (longReplyRecvRegs rf st tid mi.length).size > maxMessageRegisters := by
                rw [longReplyRecvRegs_size rf st tid mi.length (by omega)]; omega
              have h := replyRecvOnCore_arm_deliveredLong _ st epId tid c rid rf mi.length badge
                grant executingCore ct rt ep rp hAd (by omega) hSzL hT hRO hE hS hR hEnq hRp hStash
                hRecR hInert
              rw [replyRecvTransferOnCoreR_eq_match]
              rw [replyRecvTransferOnCore_of_no_fault (h := hNoFault) (hA := hAd.popAdmits hT hRO), hTail]
              generalize endpointReplyRecvOnCore epId tid rid c
                { registers := longReplyRecvRegs rf st tid mi.length, badge := badge } grant
                executingCore st = r at h ⊢
              rcases r with e | ⟨a, st'⟩
              · cases h
              · simp only [Except.ok.injEq] at h ⊢
                exact h.symm
            · have hSzL : ¬ (longReplyRecvRegs rf st tid mi.length).size > maxMessageRegisters := by
                rw [longReplyRecvRegs_size rf st tid mi.length (by omega)]; omega
              rw [replyRecvLongCapsR_eq epId tid c rid badge grant rf mi.length mi.label executingCore
                st (by omega) hSzL (fun stcb hS' => by
                  have hReq := replyCapRequest_of_routedReplyLong st tid stcb rf capAddr mi .replyRecv
                    true hS' (hRf stcb hS') (.inr ⟨hR, rfl⟩) hRead
                  simp only [↓reduceIte] at hReq
                  exact hReq)]
              rfl
        · rfl
  | _ => rfl

/-- The long reply-receive arm is the specification's. -/
theorem endpointReplyRecvLongCheckedArmR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (st : SystemState)
    (hRR : decoded.syscallId = .replyRecv)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall opCode SeLe4n.arm64DefaultLayout rf 32 =
      .replyRecvLong capAddr decoded.msgInfo)
    (hRegs : longReplyRegs st tid rf decoded.msgInfo.length = decoded.msgRegs)
    (hReply : decoded.replyCPtr =
      SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf SeLe4n.arm64DefaultLayout.replyReg))
    (hCaller : gate.callerId = tid)
    (hRoot : gate.cspaceRootCap = callerCspaceRoot st tid)
    (hRead : ∀ j, j < decoded.msgInfo.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w)
    (hRf : ∀ stcb, st.getTcb? tid = some stcb → stcb.registerContext = rf) :
    endpointReplyRecvLongCheckedArmR ctx rf decoded.msgInfo.length decoded.msgInfo.extraCaps
        decoded.msgInfo.label tid executingCore cap st =
      RefusalCarrying.ofKernelReporting
        (replyRecvArmReport ctx tid decoded.msgInfo decoded.msgRegs
          decoded.replyCPtr executingCore cap)
        (dispatchWithCapChecked ctx decoded tid executingCore gate cap) st := by
  rw [endpointReplyRecvLongCheckedArmR_eq_general ctx rf capAddr decoded.msgInfo tid executingCore
    cap st hR hRead hRf]
  unfold endpointReplyRecvLongGeneralR
  rw [hRegs, ← hReply]
  exact endpointReplyRecvCheckedArmGeneralR_eq ctx decoded tid executingCore gate cap st hRR
    hCaller hRoot

theorem replyRecvLongOperandArmThenTaintR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId)
    (preEpoch : Nat) (preLength : Nat)
    (st : SystemState) (tcb : TCB) (ref : CSpaceAddr)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr)
    (hRR : decoded.syscallId = .replyRecv)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall opCode SeLe4n.arm64DefaultLayout rf 32 =
      .replyRecvLong capAddr decoded.msgInfo)
    (hRegs : longReplyRegs st tid rf decoded.msgInfo.length = decoded.msgRegs)
    (hReply : decoded.replyCPtr =
      SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf SeLe4n.arm64DefaultLayout.replyReg))
    (hTcb : st.getObject? tid.toObjId = some (.tcb tcb))
    (hRef : lookupSlot tcb decoded.capAddr st = .ok ref)
    (hRead : ∀ j, j < decoded.msgInfo.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w)
    (hRf : ∀ stcb, st.getTcb? tid = some stcb → stcb.registerContext = rf)
    (hOrd : replyRecvAnsweringReply? ctx (replyRecvCallerGate decoded tid tcb) decoded tid st = none ∨
      ∃ epId, replyRecvReceiveEndpoint ctx (replyRecvCallerGate decoded tid tcb) tid st = .ok epId) :
    replyRecvLongOperandArmThenTaintR ctx rf decoded.msgInfo.length decoded.msgInfo.extraCaps
        decoded.msgInfo.label tid executingCore
        (syscallRequiredRight decoded.syscallId) (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernelReporting
        (replyRecvOperandReport ctx tid decoded.msgInfo decoded.msgRegs
          decoded.replyCPtr executingCore (syscallRequiredRight decoded.syscallId)
          (SystemState.lookupSlotCap st ref))
        (dispatchCheckedArmThenTaint ctx decoded tid executingCore
        { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr, requiredRight := syscallRequiredRight decoded.syscallId } none
        (syscallTaintPlan st tid decoded) preEpoch preLength st.declassificationTaint) st := by
  have hOperand := syscallOperandCap?_of_resolved st tid _ tcb ref hTcb hRef
  simp -iota only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernelReporting]
  rw [dispatchSyscallArmChecked_of_entryOrder
    (gate := { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr, requiredRight := syscallRequiredRight decoded.syscallId })
    (Or.inr hOrd) (fun _ => rfl)]
  simp -iota only [hRR, syscallInvokeTyped, syscallResolveCap, SyscallGate.lookupSlot_mk, hRef]
  dsimp only
  simp -iota only [replyRecvTaintStep_eq st tid decoded hRR SeLe4n.arm64DefaultLayout rf tcb hTcb hReply
    (wN := fun cap => st.taintWordsAt (notifObjOfCode (receiveTaintSignalCode st tid cap)))
    (wS := fun cap => st.taintWordsAt (threadObjOfCode (receiveTaintSourceCode st cap)))
    (wT := st.taintWordsAt tid.toObjId) (hN := fun _ => decode_taintWordsAt st _)
    (hS := fun _ => decode_taintWordsAt st _)
    (hT := decode_taintWordsAt st _), hOperand]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · unfold replyRecvLongOperandArmThenTaintR replyRecvOperandReport
    dsimp only
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
    · simp -iota only [hIdle, ↓reduceIte]
      rfl
    · simp -iota only [hIdle, Bool.false_eq_true, ↓reduceIte]
      dsimp only
      by_cases hType : syscallTargetAccepted .replyRecv st cap = false
      · simp -iota only [hType, Bool.not_false, ↓reduceIte]
        rfl
      replace hType : syscallTargetAccepted .replyRecv st cap = true := by simpa using hType
      by_cases hRight : cap.hasRight (syscallRequiredRight .replyRecv) = true
      · simp -iota only [hType, Bool.not_true, Bool.false_eq_true, hRight, ↓reduceIte,
          withTaintWordsAt_eq, TaintWords.mk_fields]
        rw [endpointReplyRecvLongCheckedArmR_eq ctx decoded tid executingCore
          { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr, requiredRight := syscallRequiredRight decoded.syscallId }
          cap rf capAddr st hRR hR hRegs hReply rfl (by unfold callerCspaceRoot; rw [hTcb])
          hRead hRf]
        unfold RefusalCarrying.ofKernelReporting
        simp -iota only [hRR]
        rcases dispatchWithCapChecked ctx decoded tid executingCore
          { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr, requiredRight := syscallRequiredRight .replyRecv }
          cap st with _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp -iota only [hType, Bool.not_true, Bool.false_eq_true, hRight, ↓reduceIte]
        rfl

/-- The long reply-receive's operand dispatch (`dispatchReplyRecvLongCheckedR_eq`).
A specification: the compiled entry runs the arm out of line. -/
noncomputable def dispatchReplyRecvLongCheckedR (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (xc : Nat) : RefusalCarrying Unit := fun st =>
  replyRecvRoutedR ctx
    (replyRecvRoutedDecode capAddr (longReplyRegs st tid rf len)
      (SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf SeLe4n.arm64DefaultLayout.replyReg))
      len extraCaps label)
    tid executingCore
    (dispatchOperandCheckedR capAddr tid executingCore xc
      (replyRecvLongOperandArmThenTaintR ctx rf len extraCaps label tid executingCore
        (syscallRequiredRight .replyRecv))) st

theorem dispatchReplyRecvLongCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (st : SystemState)
    (hRR : decoded.syscallId = .replyRecv)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall opCode SeLe4n.arm64DefaultLayout rf 32 =
      .replyRecvLong capAddr decoded.msgInfo)
    (hRegs : longReplyRegs st tid rf decoded.msgInfo.length = decoded.msgRegs)
    (hReply : decoded.replyCPtr =
      SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf SeLe4n.arm64DefaultLayout.replyReg))
    (hRead : ∀ j, j < decoded.msgInfo.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w)
    (hRf : ∀ stcb, st.getTcb? tid = some stcb → stcb.registerContext = rf) :
    dispatchReplyRecvLongCheckedR ctx decoded.capAddr rf decoded.msgInfo.length
        decoded.msgInfo.extraCaps decoded.msgInfo.label tid executingCore (syscallExtraCapCount decoded.syscallId decoded.msgInfo.extraCaps) st =
      RefusalCarrying.ofKernelReporting
        (replyRecvRoutedReport ctx decoded tid executingCore
          (operandReport decoded.capAddr tid executingCore
            (syscallExtraCapCount decoded.syscallId decoded.msgInfo.extraCaps)
            (replyRecvOperandReport ctx tid decoded.msgInfo decoded.msgRegs
              decoded.replyCPtr executingCore (syscallRequiredRight .replyRecv))))
        (dispatchSyscallChecked ctx decoded tid executingCore) st := by
  unfold dispatchReplyRecvLongCheckedR
  rw [hRegs, ← hReply, replyRecvRoutedDecode_eq_norm hRR, replyRecvRoutedR_norm]
  apply replyRecvRoutedR_eq hRR
  intro hOrd
  apply dispatchOperandCheckedR_eq_reporting_at ctx decoded tid executingCore _ _
    (by rw [hRR]; decide) st
  · intro tcb ref hTcb hRef
    have hArm := replyRecvLongOperandArmThenTaintR_eq ctx decoded tid executingCore
      st.declassificationAuditEpoch st.declassificationAudit.length
      st tcb ref rf capAddr hRR hR hRegs hReply hTcb hRef hRead hRf (hOrd tcb hTcb)
    simp only [hRR] at hArm ⊢
    exact hArm
  · exact fun tcb hTcb => Or.inr (hOrd tcb hTcb)

end SeLe4n.Kernel
