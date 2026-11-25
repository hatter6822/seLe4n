-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RefusalCarryingEndpoint
import SeLe4n.Kernel.IPC.CrossCore.ReplyLegFrame
import SeLe4n.Kernel.IPC.CrossCore.ReplyPopFrame
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyHeldInPlace
import SeLe4n.Kernel.IPC.CrossCore.ReplyUnheldPopFrame
import SeLe4n.Kernel.IPC.CrossCore.FaultAnswerInPlace
import SeLe4n.Kernel.IPC.CrossCore.LongReplyRecvFrame
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvCapsDelivered
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvTakeFrame
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvLegGuards
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvBlockComposed
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvTakeComposed
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvCallTakeComposed

/-!
# Reply-receive, refusing in the state it was refused in

WS-ZA ZA4.7.  The checked reply-receive arm on a message read in registers,
proven equal to `RefusalCarrying.ofKernel` of the specification's dispatch
(`dispatchReplyRecvCheckedR_eq`).  The reply capability at the reply register
(x6, WS-SX SX7.3) is resolved in continuation form, so no gate, slot reference or result cell is built for it;
a reply-receive whose receive then blocks on an endpoint no sender waits on
writes in place on every reply arm (`replyRecvBlockArmCode`,
`replyRecvOnCore_arm_deliveredRegs`); any other takes the specification's
path.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open Architecture.RegisterDecode
open Architecture.SyscallArgDecode

/-- `resolveReplyRecvReply` on the reply register's address alone, with the
gate the caller's own CSpace gives (`resolveReplyRecvReplyR_eq`). -/
def resolveReplyRecvReplyR (st : SystemState) (tid : SeLe4n.ThreadId) (replyAddr : SeLe4n.CPtr) :
    Except KernelError (Option (SeLe4n.ReplyId × SeLe4n.ThreadId × Option SeLe4n.Badge × Bool)) :=
  let gate : SyscallGate :=
    { callerId := tid
      cspaceRootCap := callerCspaceRoot st tid
      capAddr := replyAddr
      requiredRight := .write }
  match lookupReplyCap gate st with
  | .error lf => .error (.failedLookup false lf)
  | .ok (rcap, rid) =>
      match replyAnsweredCaller? st rid with
      | some prevCaller => .ok (some (rid, prevCaller, rcap.badge, rcap.rights.mem .grant))
      | none => .ok none

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

/-- **Whether a reply-receive's reply half replies to no one** (WS-SX SX7.2):
its reply capability resolves (`resolveReplyRecvReplyR`) to a reply object
with no caller blocked on it, so seL4-MCS's `doReplyTransfer` returns and the
receive half runs alone. -/
def replyRecvRepliesToNoOne (st : SystemState) (tid : SeLe4n.ThreadId)
    (replyAddr : SeLe4n.CPtr) : Bool :=
  match resolveReplyRecvReplyR st tid replyAddr with
  | .ok none => true
  | _ => false

/-- A reply-receive whose reply answers no caller (`replyRecvRepliesToNoOne`)
resolves to no caller through its own CSpace root (`callerReplyGate`). -/
theorem resolveReplyRecvReply_of_repliesToNoOne {st : SystemState} {tid : SeLe4n.ThreadId}
    {decoded : SyscallDecodeResult}
    (h : replyRecvRepliesToNoOne st tid decoded.replyCPtr = true) :
    resolveReplyRecvReply (callerReplyGate st tid decoded) decoded st = .ok none := by
  rw [← resolveReplyRecvReplyR_eq st tid (callerReplyGate st tid decoded) decoded rfl rfl]
  unfold replyRecvRepliesToNoOne at h
  split at h
  · assumption
  · cases h

/-- **The state a reply-receive arm's refusal reports**: the receive arm's
(`receiveArmReport`) when the reply half is skipped, by an extra capability
that does not look up (WS-SX SX6.1) or a reply with no caller to answer (WS-SX
SX7.2), since the receive half then runs alone; the state it was handed
otherwise, since the reply-receive refuses before its first write. -/
def replyRecvArmReport (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (extraCaps : Nat) (replyAddr : SeLe4n.CPtr) (executingCore : Concurrency.CoreId)
    (cap : Capability) (st : SystemState) : SystemState :=
  match callerExtraCapsFault? st tid extraCaps with
  | some _ => receiveArmReport ctx tid true replyAddr executingCore cap st
  | none =>
    if replyRecvRepliesToNoOne st tid replyAddr then
      receiveArmReport ctx tid true replyAddr executingCore cap st
    else st

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
  simp only [receiveArmReport, hTgt, hFlow, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    cancelReceiveArmBusyReply, cancelRecvBusyReply]
  rw [receiveArmHolderCode_eq ctx tid _ gate decoded _ _ st hRoot
    (by rw [receiveReplyAddr?_of_replyRecv' hRR]; rfl)]
  rfl

/-- The checked reply-receive arm (`dispatchWithCapChecked`'s `.replyRecv`
case) through the specification's path, refusing in the state it was handed
(`endpointReplyRecvCheckedArmGeneralR_eq`). -/
def endpointReplyRecvCheckedArmGeneralR (ctx : LabelingContext) (mi : MessageInfo)
    (regs : Array SeLe4n.RegValue) (replyAddr : SeLe4n.CPtr)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability) :
    RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object epId =>
      if !endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) then
        .error (.flowDenied, st)
      else
        callerExtraCapsFailK st tid mi.extraCaps
          (fun _ => endpointReceiveCheckedArmR ctx tid true replyAddr executingCore cap st)
          (fun _ =>
        match resolveReplyRecvReplyR st tid replyAddr with
        | .error e => .error (e, st)
        | .ok none => endpointReceiveCheckedArmR ctx tid true replyAddr executingCore cap st
        | .ok (some (rid, prevCaller, replyBadge, replyGrant)) =>
            let msg : IpcMessage :=
              { registers := extractMessageRegisters regs mi, badge := replyBadge }
            if securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf prevCaller) then
              if receiveCompletesSignal ctx st tid then
                match replyRecvCompletesSignalArm ctx tid prevCaller mi.label msg replyGrant
                    executingCore st with
                | .ok r => .ok r
                | .error e => .error (e, st)
              else
              match replyRecvTransferOnCore epId tid rid prevCaller mi.label msg
                  replyGrant executingCore st with
              | .ok (summary, st') =>
                  .ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo)
              | .error e => .error (e, st)
            else .error (.replyCapInvalid, st))
    | _ => .error (.invalidCapability 0, st)

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
        (replyRecvArmReport ctx tid decoded.msgInfo.extraCaps
          decoded.replyCPtr executingCore cap)
        (dispatchWithCapChecked ctx decoded tid executingCore gate cap) st := by
  cases hTgt : cap.target with
  | object epId =>
    by_cases hFlow : endpointFlowGate ctx epId (ctx.endpointLabelOf epId)
        (ctx.threadLabelOf tid) = true
    case neg =>
      simp only [endpointReplyRecvCheckedArmGeneralR, RefusalCarrying.ofKernelReporting,
        dispatchWithCapChecked, dispatchCapabilityOnly, hRR, hTgt, hFlow, Bool.not_false,
        ↓reduceIte, replyRecvArmReport, receiveArmReport]
      split <;> (try split) <;> rfl
    simp only [endpointReplyRecvCheckedArmGeneralR, hTgt, hFlow, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, callerExtraCapsFailK_eq]
    have hSkip := replyRecvSkipReply_eq ctx decoded tid executingCore gate cap st epId hRR hCaller
      hRoot hTgt hFlow
    have hRep := replyRecvSkipReport_eq ctx decoded tid executingCore gate cap st epId hRR hRoot hTgt
      hFlow
    cases hXc : callerExtraCapsFault? st tid decoded.msgInfo.extraCaps with
    | some xf =>
      simp only []
      rw [hSkip]
      simp only [RefusalCarrying.ofKernelReporting, dispatchWithCapChecked,
        dispatchCapabilityOnly, hRR, hTgt, hFlow, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        hXc, replyRecvArmReport, hRep]
      cases receiveResolvedArm ctx decoded gate tid epId executingCore
        (cancelRecvBusyReply ctx tid gate decoded executingCore st) <;> rfl
    | none =>
    simp only [RefusalCarrying.ofKernelReporting, dispatchWithCapChecked,
      dispatchCapabilityOnly, hRR, hTgt, hFlow, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      hXc, replyRecvArmReport, replyRecvRepliesToNoOne]
    have hEq := resolveReplyRecvReplyR_eq st tid gate decoded hCaller hRoot
    cases hS : resolveReplyRecvReply gate decoded st with
    | error e => simp only [hEq, hS, Bool.false_eq_true, ↓reduceIte]
    | ok r =>
      cases r with
      | none =>
        simp only [hEq, hS, ↓reduceIte, hRep]
        rw [hSkip]
        cases receiveResolvedArm ctx decoded gate tid epId executingCore
          (cancelRecvBusyReply ctx tid gate decoded executingCore st) <;> rfl
      | some r =>
        obtain ⟨rid, prevCaller, replyBadge, replyGrant⟩ := r
        simp only [hEq, hS, Bool.false_eq_true, ↓reduceIte]
        split
        · split
          · rcases replyRecvCompletesSignalArm ctx tid prevCaller decoded.msgInfo.label _
              replyGrant executingCore st with _ | ⟨⟨⟩, st'⟩ <;> rfl
          · rcases replyRecvTransferOnCore epId tid rid prevCaller decoded.msgInfo.label _
              replyGrant executingCore st with
              _ | ⟨summary, st'⟩ <;> rfl
        · rfl
  | _ =>
    simp only [endpointReplyRecvCheckedArmGeneralR, RefusalCarrying.ofKernelReporting,
      dispatchWithCapChecked, dispatchCapabilityOnly, hRR, hTgt, replyRecvArmReport,
      receiveArmReport]
    split <;> (try split) <;> rfl

/-- The reply capability a reply-receive names, checked as
`resolveReplyRecvReplyR` checks it once its slot is found: present, not the idle
thread's, carrying the write right, naming a reply object.  A reply object with
an outstanding caller goes to `onOk` with the caller and the capability's
badge, one with none to `onNone` (WS-SX SX7.2), a refusal to `onErr`, so no
`Except`, `Option` or tuple cell is built.  `onOk` is also handed the capability
itself, as the slot holds it, so an arm that answers the caller through the
`.reply` arm's in-place forms runs them on it. -/
@[inline] def replyRecvCapK {α : Type} (st : SystemState) (cap? : Option Capability)
    (onErr : KernelError → α) (onNone : Unit → α)
    (onOk : Capability → SeLe4n.ReplyId → SeLe4n.ThreadId → Option SeLe4n.Badge → Bool → α) :
    α :=
  match cap? with
  | none => onErr (.failedLookup false (.missingCapability 0))
  | some cap =>
      if SeLe4n.Kernel.capTargetsReservedKernelObject cap then
        onErr (.failedLookup false (.missingCapability 0))
      else if !cap.hasRight .write then onErr (.failedLookup false (.missingCapability 0))
      else
        match cap.target with
        | .replyCap rid =>
            match replyAnsweredCaller? st rid with
            | some c => onOk cap rid c cap.badge (cap.rights.mem .grant)
            | none => onNone ()
        | _ => onErr (.failedLookup false (.missingCapability 0))

/-- `resolveReplyRecvReplyR` in continuation form (`resolveReplyRecvK_eq_of`), on
the reply register's address: the slot is resolved through `lookupSlotFromK`,
as the operand is.  WS-ZA ZA4.7. -/
@[inline] def resolveReplyRecvK {α : Type} (st : SystemState) (tid : SeLe4n.ThreadId)
    (replyAddr : SeLe4n.CPtr) (onErr : KernelError → α) (onNone : Unit → α)
    (onOk : Capability → SeLe4n.ReplyId → SeLe4n.ThreadId → Option SeLe4n.Badge → Bool → α) :
    α :=
  match callerCspaceRoot st tid with
  | none => onErr (.failedLookup false .invalidRoot)
  | some root =>
    lookupSlotFromK root replyAddr st
      (fun t a b c => onErr (.failedLookup false (LookupFault.ofWords t a b c)))
      (fun cnode slot =>
        replyRecvCapK st (SystemState.lookupSlotCap st { cnode := cnode, slot := slot })
          onErr onNone onOk)

/-- The continuation form is the resolution, for an `onOk` that reads the
capability it is handed only through the facts the resolution reports: it names
reply object `rid`, whose caller is `c`, and carries the badge and grant right
passed beside it (`onOk'`). -/
theorem resolveReplyRecvK_eq_of {α : Type} (st : SystemState) (tid : SeLe4n.ThreadId)
    (replyAddr : SeLe4n.CPtr) (onErr : KernelError → α) (onNone : Unit → α)
    (onOk : Capability → SeLe4n.ReplyId → SeLe4n.ThreadId → Option SeLe4n.Badge → Bool → α)
    (onOk' : SeLe4n.ReplyId → SeLe4n.ThreadId → Option SeLe4n.Badge → Bool → α)
    (hOk : ∀ cap rid c, cap.target = .replyCap rid → replyAnsweredCaller? st rid = some c →
      onOk cap rid c cap.badge (cap.rights.mem .grant) =
        onOk' rid c cap.badge (cap.rights.mem .grant)) :
    resolveReplyRecvK st tid replyAddr onErr onNone onOk =
      match resolveReplyRecvReplyR st tid replyAddr with
      | .error e => onErr e
      | .ok none => onNone ()
      | .ok (some (rid, c, b, g)) => onOk' rid c b g := by
  unfold resolveReplyRecvK resolveReplyRecvReplyR
  simp only [lookupReplyCap, syscallLookupCap, syscallResolveCap]
  simp only [SyscallGate.lookupSlot]
  cases callerCspaceRoot st tid with
  | none => rfl
  | some root =>
  simp only [lookupSlotFromK_eq]
  cases lookupSlotFrom root replyAddr st with
  | error e => simp only [LookupFault.ofWords_word, KernelError.capFaultLookup]
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
          cases hT : cap.target <;> try rfl
          rename_i rid
          simp only []
          cases hA : replyAnsweredCaller? st rid with
          | none => rfl
          | some c => exact hOk cap rid c hT hA
        · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true, Bool.not_false] <;> rfl

/-- WS-ZA ZA4.7: a reply-receive answers a caller blocked on this server and
then blocks, every write in its slot: the caller's reply leg may write in place
(`replyWakesInPlace`), no sender waits on the endpoint, the server may block
there in place and its reply object, consumed by the reply leg, is free, not
stashed and in its slot for the stasher record (`replyRecordsInPlace`).  Each
check reads the pre-state; `replyRecvBlocksFast_spec` carries
them to the rendezvous arm's guard (`replyRecvBlockArmCode_spec`). -/
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
        { registers := Architecture.regMessageBody layout rf len, badge := badge }
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

/-- WS-SX SX8.3: **a reply-receive answering a caller recording no server whose
reply object is linked to nothing, that may block in place**, read on the
pre-state: the caller `c` blocked on reply object `rid` with no server recorded,
the reply object neither heading a stack nor on one (`replyUnlinkedInPlace`: the
state SchedContext_Unbind of a lent context leaves once the server is
finalised), no sender waiting on the endpoint, the replier a thread that may
block there in place and the reply object not stashed and in its slot for the
stasher record.  Every read is a code. -/
@[inline] def replyRecvUnlinkedBlocks (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) : Bool :=
  tid.val != c.val &&
  (match st.getTcb? c with
   | some ct =>
       (match ct.ipcState with
        | .blockedOnReply _ none => true
        | _ => false) &&
       ct.replyObjectCode == rid.val + 1
   | none => false) &&
  replyUnlinkedInPlace st c rid &&
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

/-- **The reply arm whose blocking reply-receive writes in place**, as a code
read on the pre-state: 1 to 5 for the arm whose checks pass first (the
rendezvous, `replyRecvBlocksFast`; the donated, `replyRecvDonatedBlocks`; the
held, `replyRecvHeldBlocks`; the unheld, `replyRecvUnheldBlocks`; the unlinked,
`replyRecvUnlinkedBlocks`), 0 when none does.  A code, so choosing the arm
allocates nothing (`ReplyRecvArm.ofCode`, `replyRecvBlockArmCode_spec`); out of
line, so the five guards are compiled once for every answer that reads them. -/
@[noinline] def replyRecvBlockArmCode (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) : Nat :=
  if replyRecvBlocksFast st epId tid c rid then 1
  else if replyRecvDonatedBlocks st epId tid c rid then 2
  else if replyRecvHeldBlocks st epId tid c rid then 3
  else if replyRecvUnheldBlocks st epId tid c rid then 4
  else if replyRecvUnlinkedBlocks st epId tid c rid then 5
  else 0

/-- The arm a nonzero `replyRecvBlockArmCode` names. -/
@[inline] def ReplyRecvArm.ofCode : Nat → ReplyRecvArm
  | 1 => .rendezvous
  | 2 => .donated
  | 3 => .held
  | 4 => .unheld
  | _ => .unlinked

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

/-- **The checked reply-receive whose reply leg transfers capabilities**, its
caller unfaulted: from a replier whose frame routes as a reply-receive, under
the grant right, a reply of at most four words, on every reply arm whose
receive blocks in place (`replyRecvBlockArmCode`): the arm's reply leg and pop,
the transfer in place (seL4's `doReplyTransfer`; every CNode it writes keeps
its kind), then the receive leg (seL4's `receiveIPC`) and the caller's frame
(`performReplyRecvArmCapsDelivered`).  The replier and the caller enter as the
words the transfer reads of them, read before any write.  Any other takes the
specification's path (`replyRecvCapsArmR_eq`). -/
@[inline] def replyRecvCapsArmR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    match st.getTcb? tid with
    | some stcb =>
        match Architecture.RegisterDecode.registerRoutedSyscallOf SyscallId.replyRecv.toNat
            SeLe4n.arm64DefaultLayout stcb.registerContext with
        | .replyRecv _ _ =>
            match st.getTcb? c with
            | some ct =>
                if grant && decide (Architecture.regMessageLength layout len ≤ 4) &&
                    replyRecvBlockArmCode st epId tid c rid != 0 then
                  .ok ((), performReplyRecvArmCapsDelivered
                    (ReplyRecvArm.ofCode (replyRecvBlockArmCode st epId tid c rid))
                    ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId
                    (receiveQueueTailCode st epId) layout rf len badge executingCore
                    stcb.spaceCells[2] stcb.ipcBuffer stcb.spaceCells[0]
                    (routedExtraCaps stcb.registerContext) ct.spaceCells[2] ct.ipcBuffer
                    ct.spaceCells[0])
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
          simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hG
          obtain ⟨⟨hGr, hSz⟩, hK⟩ := hG
          subst hGr
          have hReq := replyCapRequest_of_routedReplyRecv st tid stcb capAddr mi hS hR
          obtain ⟨ct, rt, ep, rp, hAd, hT, hRO, hE, hS', hR', hEnq, hRp, hStash, hRecR, hTail⟩ :=
            replyRecvBlockArmCode_spec hK
          obtain rfl : ct = ct0 := by rw [hT] at hTc0'; cases hTc0'; rfl
          unfold replyRecvRendezvousR
          rw [replyRecvTransferOnCore_of_no_fault (h := hNoF), hTail]
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
      · rfl
    · rfl
  · rfl

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

/-- **The reply arm whose reply-receive takes a waiting sender in place**, as a
code read on the pre-state: 1 to 5 for the arm whose reply-leg guard passes
first (`ReplyRecvArm.legGuard`: the rendezvous, the donated, the held, the
unheld, the unlinked), the caller's reply object the one named and present and
the endpoint's send queue offering a sender the take writes in place
(`replyRecvSenderTakes`); 0 otherwise.  A code, so choosing the arm allocates
nothing (`ReplyRecvArm.ofCode`, `replyRecvTakeArmCode_spec`); out of line, so the
guards are compiled once for every answer that reads them. -/
@[noinline] def replyRecvTakeArmCode (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) : Nat :=
  match st.getTcb? c with
  | some ct =>
      if ct.replyObjectCode == rid.val + 1 && (st.getReply? rid).isSome &&
          replyRecvSenderTakes st epId tid c then
        if ReplyRecvArm.rendezvous.legGuard st tid c rid ct then 1
        else if ReplyRecvArm.donated.legGuard st tid c rid ct then 2
        else if ReplyRecvArm.held.legGuard st tid c rid ct then 3
        else if ReplyRecvArm.unheld.legGuard st tid c rid ct then 4
        else if ReplyRecvArm.unlinked.legGuard st tid c rid ct then 5
        else 0
      else 0
  | none => 0

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

/-- **The checked reply-receive whose receive leg takes a waiting sender, over
every reply arm** (seL4-MCS's `handleReplyRecv`: `doReplyTransfer`, the
reply arm's `reply_pop`, then `receiveIPC` meeting a sender already queued --
the ordinary server loop under load): when a reply of at most four words takes
the sender in place on some reply arm (`replyRecvTakeArmCode`) and the sender's
saved frame routes as a capability-free send, the arm's reply leg and pop, the
reply leg's transfer, the take, the arm's deschedule and the frames, the
sender's six words read from its saved registers before any write.  A reply
leg transferring no capability (`replyRecvReplyInertW`) runs
`performReplyRecvArmTakeDelivered`; a granting one whose frame routes as a
reply-receive, its transfer's stores in place, runs
`performReplyRecvArmTakeCapsDelivered`.  A caller queued by a `Call` is taken
ahead of this arm (`replyRecvArmCallTakeR`); otherwise the capability arm
(`replyRecvCapsArmR`).  Any other takes the specification's path
(`replyRecvArmTakeR_eq`). -/
@[inline] def replyRecvArmTakeR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    if decide (Architecture.regMessageLength layout len ≤ 4) &&
        replyRecvTakeArmCode st epId tid c rid != 0 then
      match st.getEndpoint? epId with
      | some ep =>
        match ep.sendQ.head with
        | some s =>
          match st.getTcb? s with
          | some sTcb =>
            match Architecture.RegisterDecode.registerRoutedSyscallOf
                (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
                SeLe4n.arm64DefaultLayout sTcb.registerContext with
            | .send _ mi =>
              if replyRecvReplyInertW st tid c grant then
                let f := Architecture.regMessageFrameW SeLe4n.arm64DefaultLayout
                  sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged
                .ok ((), performReplyRecvArmTakeDelivered
                  (ReplyRecvArm.ofCode (replyRecvTakeArmCode st epId tid c rid))
                  ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId s
                  sTcb.queueNextCode executingCore layout rf len badge f.x0 f.x1 f.x2 f.x3 f.x4 f.x5)
              else
                match st.getTcb? tid with
                | some stcb =>
                  match Architecture.RegisterDecode.registerRoutedSyscallOf SyscallId.replyRecv.toNat
                      SeLe4n.arm64DefaultLayout stcb.registerContext with
                  | .replyRecv _ _ =>
                    match st.getTcb? c with
                    | some ct =>
                      if grant then
                        let f := Architecture.regMessageFrameW SeLe4n.arm64DefaultLayout
                          sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge)
                          sTcb.ipcBadged
                        .ok ((), performReplyRecvArmTakeCapsDelivered
                          (ReplyRecvArm.ofCode (replyRecvTakeArmCode st epId tid c rid))
                          ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid
                          epId s sTcb.queueNextCode executingCore layout rf len badge
                          f.x0 f.x1 f.x2 f.x3 f.x4 f.x5 stcb.spaceCells[2] stcb.ipcBuffer
                          stcb.spaceCells[0] (routedExtraCaps stcb.registerContext) ct.spaceCells[2]
                          ct.ipcBuffer ct.spaceCells[0])
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
    else replyRecvCapsArmR epId tid c rid badge grant layout rf len label executingCore st

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
    simp only [hEp, hH, hTs]
    split
    · next capAddr mi hR =>
      split
      · next hI =>
        have h := replyRecvOnCore_arm_takeDelivered _ st epId tid c rid layout rf len badge grant
          executingCore ct rp ep s sTcb capAddr mi hAd hSz4 hT hRO hRp
          (replyRecvReplyInertW_spec hI hT) hE hH hS hSC hG
          ((Architecture.RegisterDecode.registerRoutedSyscall_default _).trans hR) hF
        rw [Architecture.regMessageFrameW_eq, ← TCB.ipcBadgeView_eq_opt]
        unfold replyRecvRendezvousR
        rw [replyRecvTransferOnCore_of_no_fault (h := hNoF)]
        generalize endpointReplyRecvOnCore epId tid rid c
          { registers := Architecture.regMessageBody layout rf len, badge := badge } grant
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
                have h := replyRecvOnCore_arm_takeCapsDelivered _ st epId tid c rid layout rf len
                  badge executingCore ct rp ep s sTcb capAddr mi stcb _ hAd hSz4 hT hRO hRp
                  hE hH hS hSC hG ((Architecture.RegisterDecode.registerRoutedSyscall_default _).trans hR)
                  hF hReq
                rw [Architecture.regMessageFrameW_eq, ← TCB.ipcBadgeView_eq_opt]
                unfold replyRecvRendezvousR
                rw [replyRecvTransferOnCore_of_no_fault (h := hNoF)]
                generalize endpointReplyRecvOnCore epId tid rid c
                  { registers := Architecture.regMessageBody layout rf len, badge := badge } true
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
  · exact replyRecvCapsArmR_eq epId tid c rid badge grant layout rf len label executingCore st
      hNoF

/-- **The reply arm whose reply-receive takes a queued caller in place**, as a
code read on the pre-state: 1 to 5 for the first arm (the rendezvous, the
donated, the held, the unheld, the unlinked) whose reply-leg guard
(`ReplyRecvArm.legGuard`) and Call-take guard (`ReplyRecvArm.callGuard`) pass,
the caller's reply object the one named and present and the head of the
endpoint's send queue a caller blocked by a routed capability-free call
(`replyRecvCallerQueued`); 0 otherwise.  A code, so choosing the arm allocates
nothing (`replyRecvCallTakeArmCode_spec`); out of line, so the guards are
compiled once for every answer and length that reads them. -/
@[noinline] def replyRecvCallTakeArmCode (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) : Nat :=
  match st.getTcb? c with
  | some ct =>
      if ct.replyObjectCode == rid.val + 1 && (st.getReply? rid).isSome &&
          replyRecvCallerQueued st epId c then
        match st.getEndpoint? epId with
        | some ep =>
          match ep.sendQ.head with
          | some s =>
            match st.getTcb? s with
            | some sTcb =>
              if ReplyRecvArm.rendezvous.legGuard st tid c rid ct &&
                  ReplyRecvArm.rendezvous.callGuard st epId tid s sTcb rid then 1
              else if ReplyRecvArm.donated.legGuard st tid c rid ct &&
                  ReplyRecvArm.donated.callGuard st epId tid s sTcb rid then 2
              else if ReplyRecvArm.held.legGuard st tid c rid ct &&
                  ReplyRecvArm.held.callGuard st epId tid s sTcb rid then 3
              else if ReplyRecvArm.unheld.legGuard st tid c rid ct &&
                  ReplyRecvArm.unheld.callGuard st epId tid s sTcb rid then 4
              else if ReplyRecvArm.unlinked.legGuard st tid c rid ct &&
                  ReplyRecvArm.unlinked.callGuard st epId tid s sTcb rid then 5
              else 0
            | none => 0
          | none => 0
        | none => 0
      else 0
  | none => 0

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
      (ReplyRecvArm.ofCode (replyRecvCallTakeArmCode st epId tid c rid)).CallAdmits st epId tid
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
  simp only at hk
  by_cases hG : (ct.replyObjectCode == rid.val + 1 && (st.getReply? rid).isSome &&
      replyRecvCallerQueued st epId c) = true
  · have hG' := hG
    simp only [Bool.and_eq_true] at hG'
    obtain ⟨⟨hRO, hRpS⟩, hQ⟩ := hG'
    obtain ⟨rp, hRp⟩ := Option.isSome_iff_exists.mp hRpS
    obtain ⟨ep, s, sTcb, capAddr, mi, hEp, hH, hTs, hSC, hF, hRt⟩ := replyRecvCallerQueued_spec hQ
    have hRO' : ct.replyObject = some rid := by
      simp only [TCB.replyObject, beq_iff_eq.mp hRO, SeLe4n.ReplyId.ofOptCode]
    have fin : ∀ arm : ReplyRecvArm, (arm.legGuard st tid c rid ct &&
        arm.callGuard st epId tid s sTcb rid) = true →
        ∃ (ct' : TCB) (rp : Reply) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
          (capAddr : SeLe4n.CPtr) (mi : MessageInfo),
          arm.LegAdmits ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st tid c
            rid ct' ∧
          arm.CallAdmits st epId tid s sTcb rid ∧
          st.objects[c.toObjId]? = some (.tcb ct') ∧ ct'.replyObject = some rid ∧
          st.objects[rid.toObjId]? = some (.reply rp) ∧
          st.getEndpoint? epId = some ep ∧ ep.sendQ.head = some s ∧ st.getTcb? s = some sTcb ∧
          s ≠ c ∧ sTcb.ipcFaultSend = false ∧
          Architecture.RegisterDecode.registerRoutedSyscallOf
            (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
            SeLe4n.arm64DefaultLayout sTcb.registerContext = .call capAddr mi :=
      fun _ hA => by
        simp only [Bool.and_eq_true] at hA
        exact ⟨ct, rp, ep, s, sTcb, capAddr, mi, ReplyRecvArm.legGuard_spec hA.1,
          ReplyRecvArm.callGuard_spec hA.2, (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc, hRO',
          (SystemState.getReply?_eq_some_iff _ _ _).mp hRp, hEp, hH, hTs, hSC, hF, hRt⟩
    simp only [hG, ↓reduceIte, hEp, hH, hTs] at hk
    by_cases h1 : (ReplyRecvArm.rendezvous.legGuard st tid c rid ct &&
        ReplyRecvArm.rendezvous.callGuard st epId tid s sTcb rid) = true
    · simp only [h1, ↓reduceIte] at hk; subst hk; exact fin _ h1
    simp only [h1, Bool.false_eq_true, ↓reduceIte] at hk
    by_cases h2 : (ReplyRecvArm.donated.legGuard st tid c rid ct &&
        ReplyRecvArm.donated.callGuard st epId tid s sTcb rid) = true
    · simp only [h2, ↓reduceIte] at hk; subst hk; exact fin _ h2
    simp only [h2, Bool.false_eq_true, ↓reduceIte] at hk
    by_cases h3 : (ReplyRecvArm.held.legGuard st tid c rid ct &&
        ReplyRecvArm.held.callGuard st epId tid s sTcb rid) = true
    · simp only [h3, ↓reduceIte] at hk; subst hk; exact fin _ h3
    simp only [h3, Bool.false_eq_true, ↓reduceIte] at hk
    by_cases h4 : (ReplyRecvArm.unheld.legGuard st tid c rid ct &&
        ReplyRecvArm.unheld.callGuard st epId tid s sTcb rid) = true
    · simp only [h4, ↓reduceIte] at hk; subst hk; exact fin _ h4
    simp only [h4, Bool.false_eq_true, ↓reduceIte] at hk
    by_cases h5 : (ReplyRecvArm.unlinked.legGuard st tid c rid ct &&
        ReplyRecvArm.unlinked.callGuard st epId tid s sTcb rid) = true
    · simp only [h5, ↓reduceIte] at hk; subst hk; exact fin _ h5
    simp only [h5, Bool.false_eq_true, ↓reduceIte] at hk
    subst hk; exact absurd rfl h
  · simp only [hG, Bool.false_eq_true, ↓reduceIte] at hk
    subst hk; exact absurd rfl h
/-- Whether the replier's saved frame routes as a reply-receive, the frame a
granting reply leg reads its capabilities from. -/
@[inline] def replyRecvFrameRoutesReplyRecv (st : SystemState) (tid : SeLe4n.ThreadId) : Bool :=
  match st.getTcb? tid with
  | some stcb =>
    match Architecture.RegisterDecode.registerRoutedSyscallOf SyscallId.replyRecv.toNat
        SeLe4n.arm64DefaultLayout stcb.registerContext with
    | .replyRecv _ _ => true
    | _ => false
  | none => false

/-- Whether the reply leg of a Call take transfers no capability
(`replyRecvReplyInertW`), out of line, so the admission tests and the answers
that read it share one copy. -/
@[noinline] def replyRecvCallTakeReplyInert (st : SystemState) (tid c : SeLe4n.ThreadId)
    (grant : Bool) : Bool :=
  replyRecvReplyInertW st tid c grant

/-- Whether a reply-receive with a reply of at most four words takes the queued
caller in place on some reply arm (`replyRecvCallTakeArmCode`): its reply leg
transferring no capability (`replyRecvReplyInertW`), or granting with the
replier's frame routing as a reply-receive.  Out of line and a `Bool`, so the
checks are one call and allocate nothing. -/
@[noinline] def replyRecvShortCallTakeAdmits (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (len : Nat) : Bool :=
  decide (Architecture.regMessageLength layout len ≤ 4) &&
    replyRecvCallTakeArmCode st epId tid c rid != 0 &&
    (replyRecvCallTakeReplyInert st tid c grant || grant && replyRecvFrameRoutesReplyRecv st tid)

/-- **The reply-receive taking a queued caller, its reply of at most four
words**: the arm's reply leg and pop, the reply leg's transfer, the take, the
arm's lend and the frames, every context, core and word it takes read on the
pre-state.  A reply leg transferring no capability runs
`performReplyRecvArmCallTakeDelivered`; a granting one
`performReplyRecvArmCallTakeCapsDelivered`.  Out of line, it returns the state,
so nothing is built around it; read only where `replyRecvShortCallTakeAdmits`
passes, and the state unchanged on a shape it does not admit. The reply enters as the four inline words the arm reads of the replier's
message registers on the pre-state (`Architecture.regLayoutWord`), not as its
register file, so nothing outside the server's TCB holds the register file
when the server's frame is written. -/
@[noinline] def replyRecvCallTakeAnswer (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (m0 m1 m2 m3 : UInt64) (len : Nat)
    (executingCore : Concurrency.CoreId) (st : SystemState) : SystemState :=
  match st.getEndpoint? epId with
  | some ep =>
    match ep.sendQ.head with
    | some s =>
      match st.getTcb? s with
      | some sTcb =>
        match Architecture.RegisterDecode.registerRoutedSyscallOf
            (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
            SeLe4n.arm64DefaultLayout sTcb.registerContext with
        | .call _ mi =>
          if replyRecvCallTakeReplyInert st tid c grant then
            performReplyRecvArmCallTakeDelivered
              (ReplyRecvArm.ofCode (replyRecvCallTakeArmCode st epId tid c rid))
              ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId s
              sTcb.queueNextCode ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s)
              (determineTargetCore st tid) executingCore layout len badge m0 m1 m2 m3
              sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge)
              sTcb.ipcBadged
          else
            match st.getTcb? tid with
            | some stcb =>
              match st.getTcb? c with
              | some ct =>
                performReplyRecvArmCallTakeCapsDelivered
                  (ReplyRecvArm.ofCode (replyRecvCallTakeArmCode st epId tid c rid))
                  ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid
                  epId s sTcb.queueNextCode ⟨sTcb.scBindingScCode - 1⟩
                  (determineTargetCore st s) (determineTargetCore st tid) executingCore
                  layout len badge m0 m1 m2 m3 sTcb.registerContext mi.length
                  (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged
                  stcb.spaceCells[2] stcb.ipcBuffer stcb.spaceCells[0]
                  (routedExtraCaps stcb.registerContext) ct.spaceCells[2] ct.ipcBuffer
                  ct.spaceCells[0]
              | none => st
            | none => st
        | _ => st
      | none => st
    | none => st
  | none => st

/-- **The checked reply-receive whose receive leg takes a queued caller, over
every reply arm** (seL4-MCS's `handleReplyRecv`: `doReplyTransfer`, the reply
arm's `reply_pop`, then `receiveIPC` taking a caller queued by a `Call`, and
`reply_push (canDonate)` lending that caller's context to a server holding
none): when a reply of at most four words takes the caller in place on some
reply arm (`replyRecvShortCallTakeAdmits`), the take out of line
(`replyRecvCallTakeAnswer`).  Otherwise the take arm (`replyRecvArmTakeR`); the
specification's path (`replyRecvArmCallTakeR_eq`). -/
@[inline] def replyRecvArmCallTakeR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    if replyRecvShortCallTakeAdmits st epId tid c rid grant layout len then
      .ok ((), replyRecvCallTakeAnswer epId tid c rid badge grant layout
        (Architecture.regLayoutWord layout rf 0)
        (Architecture.regLayoutWord layout rf 1) (Architecture.regLayoutWord layout rf 2)
        (Architecture.regLayoutWord layout rf 3) len executingCore st)
    else replyRecvArmTakeR epId tid c rid badge grant layout rf len label executingCore st

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
    simp only [hEp, hH, hTs, hRt]
    split
    · next hI =>
      have h := replyRecvOnCore_arm_callTakeDelivered _ st epId tid c rid layout rf len badge
        grant executingCore ct rp ep s sTcb capAddr mi hAd hCA hSz4 hT hRO hRp
        (replyRecvReplyInertW_spec hI hT) hE hH hS hSC hR' hF
      unfold replyRecvRendezvousR
      rw [replyRecvTransferOnCore_of_no_fault (h := hNoF)]
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
      split at hRR
      · next stcb hS' =>
        split at hRR
        · next capAddr' mi' hRr =>
          simp only [hTc]
          have hReq := replyCapRequest_of_routedReplyRecv st tid stcb capAddr' mi' hS' hRr
          have h := replyRecvOnCore_arm_callTakeCapsDelivered _ st epId tid c rid layout rf
            len badge executingCore ct rp ep s sTcb capAddr mi stcb _ hAd hCA hSz4 hT hRO
            hRp hE hH hS hSC hR' hF hReq
          unfold replyRecvRendezvousR
          rw [replyRecvTransferOnCore_of_no_fault (h := hNoF)]
          generalize endpointReplyRecvOnCore epId tid rid c
            { registers := Architecture.regMessageBody layout rf len, badge := badge } true
            executingCore st = r at h ⊢
          rcases r with e | ⟨a, st'⟩
          · cases h
          · simp only [Except.ok.injEq] at h ⊢
            exact h.symm
        · cases hRR
      · cases hRR
  · exact replyRecvArmTakeR_eq epId tid c rid badge grant layout rf len label executingCore
      st hNoF

/-- **The checked reply-receive answering a faulted caller**: in place on every
shape whose writes stay in their slots, the caller's fault words read off the
pre-state and the fault answered from them and the reply's registers past MR0,
the answer the `.reply` arm applies (`performFaultAnswer`): on every reply arm
whose receive blocks in place (`replyRecvBlockArmCode`,
`performReplyRecvArmFaultAnswer`), and on every reply arm whose receive takes a
waiting sender (`replyRecvTakeArmCode`, `performReplyRecvArmFaultTakeDelivered`); the specification's otherwise
(`replyRecvFaultArmR_eq`).  The caller's words are read before the writes and
its TCB is not held across them. -/
@[inline] def replyRecvFaultArmR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    match st.getTcb? c with
    | some ct =>
        if replyRecvBlockArmCode st epId tid c rid != 0 then
          .ok ((), performReplyRecvArmFaultAnswer
            (ReplyRecvArm.ofCode (replyRecvBlockArmCode st epId tid c rid))
            ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId
            (receiveQueueTailCode st epId) executingCore ct.faultKind label ct.faultIp ct.faultSp
            ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5
            ct.faultX6 ct.faultX7 layout rf len)
        else if replyRecvTakeArmCode st epId tid c rid != 0 then
          match st.getEndpoint? epId with
          | some ep =>
            match ep.sendQ.head with
            | some s =>
              match st.getTcb? s with
              | some sTcb =>
                match Architecture.RegisterDecode.registerRoutedSyscallOf
                    (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
                    SeLe4n.arm64DefaultLayout sTcb.registerContext with
                | .send _ mi =>
                  let f := Architecture.regMessageFrameW SeLe4n.arm64DefaultLayout
                    sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge)
                    sTcb.ipcBadged
                  .ok ((), performReplyRecvArmFaultTakeDelivered
                    (ReplyRecvArm.ofCode (replyRecvTakeArmCode st epId tid c rid))
                    ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId s
                    sTcb.queueNextCode executingCore ct.faultKind label ct.faultIp ct.faultSp
                    ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5
                    ct.faultX6 ct.faultX7 layout rf len f.x0 f.x1 f.x2 f.x3 f.x4 f.x5)
                | _ => replyRecvRendezvousR epId tid c rid badge grant layout rf len label
                    executingCore st
              | none => replyRecvRendezvousR epId tid c rid badge grant layout rf len label
                  executingCore st
            | none => replyRecvRendezvousR epId tid c rid badge grant layout rf len label
                executingCore st
          | none => replyRecvRendezvousR epId tid c rid badge grant layout rf len label
              executingCore st
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
    · next hK =>
      obtain ⟨ct, rt, ep, rp, hAd, hT, hRO, hE, hS, hR, hEnq, hRp, hStash, hRecR, hTail⟩ :=
        replyRecvBlockArmCode_spec (by simpa using hK)
      obtain rfl : ct = ct0 := by
        rw [hT] at hTc0'; cases hTc0'; rfl
      obtain ⟨hEq, hStg⟩ := replyRecvTransferOnCore_arm_fault_inPlace _ st epId tid c rid label
        layout rf len badge grant executingCore ct rt ep rp tf hAd hPF hT hRO hE hS hR hEnq hRp
        hStash hRecR
      unfold replyRecvRendezvousR
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
        simp only [hEp, hH, hTs]
        split
        · next capAddr mi hR =>
          have h := replyRecvTransferOnCore_arm_faultTake _ st epId tid c rid label layout
            rf len badge grant executingCore ct rp ep tf s sTcb capAddr mi hAd hPF hT hRO
            hRp hE hH hS hSC hG
            ((Architecture.RegisterDecode.registerRoutedSyscall_default _).trans hR) hFs
          rw [Architecture.regMessageFrameW_eq, ← TCB.ipcBadgeView_eq_opt]
          unfold replyRecvRendezvousR
          generalize replyRecvTransferOnCore epId tid rid c label
            { registers := Architecture.regMessageBody layout rf len, badge := badge } grant
            executingCore st = r at h ⊢
          rcases r with e | ⟨a, st'⟩
          · cases h
          · simp only [Except.ok.injEq] at h ⊢
            exact h.symm
        · rfl
      · rfl
  · rfl

/-- **The fault answered and a queued caller taken, its reply of at most four
words**: the arm's reply leg with no message and pop, the take, the arm's lend,
the fault answered from the caller's words and the reply's registers past MR0
(`performReplyRecvArmCallFaultTakeDelivered`), every word read on the
pre-state.  Out of line, it returns the state, so nothing is built around it;
read only where `replyRecvCallTakeArmCode` admits and the reply is at most four
words, and the state unchanged on a shape it does not. The reply enters as the four inline words the arm reads of the replier's
message registers on the pre-state (`Architecture.regLayoutWord`), not as its
register file, so nothing outside the server's TCB holds the register file
when the server's frame is written. -/
@[noinline] def replyRecvCallFaultTakeAnswer (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (layout : SeLe4n.SyscallRegisterLayout) (m0 m1 m2 m3 : UInt64)
    (len label : Nat) (executingCore : Concurrency.CoreId) (st : SystemState) : SystemState :=
  match st.getTcb? c with
  | some ct =>
    match st.getEndpoint? epId with
    | some ep =>
      match ep.sendQ.head with
      | some s =>
        match st.getTcb? s with
        | some sTcb =>
          match Architecture.RegisterDecode.registerRoutedSyscallOf
              (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
              SeLe4n.arm64DefaultLayout sTcb.registerContext with
          | .call _ mi =>
            performReplyRecvArmCallFaultTakeDelivered
              (ReplyRecvArm.ofCode (replyRecvCallTakeArmCode st epId tid c rid))
              ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId s
              sTcb.queueNextCode ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s)
              (determineTargetCore st tid) executingCore ct.faultKind label ct.faultIp
              ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4
              ct.faultX5 ct.faultX6 ct.faultX7 layout len m0 m1 m2 m3 sTcb.registerContext
              mi.length
              (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged
          | _ => st
        | none => st
      | none => st
    | none => st
  | none => st

/-- **The checked reply-receive answering a faulted caller and taking a queued
caller, over every reply arm**: when the receive leg takes a caller queued by a
routed capability-free call in place on some reply arm
(`replyRecvCallTakeArmCode`) and the reply is at most four words, the take
out of line (`replyRecvCallFaultTakeAnswer`); the fault arm (`replyRecvFaultArmR`)
otherwise (`replyRecvCallFaultArmR_eq`). -/
@[inline] def replyRecvCallFaultArmR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    if replyRecvCallTakeArmCode st epId tid c rid != 0 &&
        decide (Architecture.regMessageLength layout len ≤ 4) then
      .ok ((), replyRecvCallFaultTakeAnswer epId tid c rid layout
        (Architecture.regLayoutWord layout rf 0)
        (Architecture.regLayoutWord layout rf 1) (Architecture.regLayoutWord layout rf 2)
        (Architecture.regLayoutWord layout rf 3) len label executingCore st)
    else replyRecvFaultArmR epId tid c rid badge grant layout rf len label executingCore st

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
    have h := replyRecvTransferOnCore_arm_callFaultTake _ st epId tid c rid label layout rf len
      badge grant executingCore ct rp ep tf s sTcb capAddr mi hAd hCA hSz4 hPF hT hRO hRp hE hH hS
      hSC ((Architecture.RegisterDecode.registerRoutedSyscall_default _).trans hRt) hFs
    unfold replyRecvRendezvousR
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

/-- **The reply-receive whose receive completes the bound notification, in
place** (`replyRecvCompletesSignalArm`, `replyRecvSignalArmR_eq`): seL4's
`doReplyTransfer` alone, run as the `.reply` arm runs it on the reply
capability `rcap` the reply register names (`endpointReplyCheckedArmR`, whose
in-place forms answer every caller shape a reply may write in its slots), then,
when the receive's test holds on the state the reply left, `receiveIPC`'s
`completeSignal` (`notificationWaitGatedR`, the wait's in-place consumption).
No result is built between the legs: the reply arm is inlined and its result
matched where it is made. -/
@[inline] def replyRecvSignalArmR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (rcap : Capability) :
    RefusalCarrying Unit :=
  fun st =>
    match endpointReplyCheckedArmR ctx layout rf len extraCaps label tid executingCore rcap st with
    | .error r => .error r
    | .ok ((), st1) =>
        if receiveCompletesSignal ctx st1 tid && receiverIpcReady st1 tid then
          match notificationWaitGatedR ctx tid (receiverBoundNotification st1 tid) executingCore
              st1 with
          | .ok r => .ok r
          | .error (e, _) => .error (e, st)
        else .ok ((), st1)

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
    simp only [RefusalCarrying.ofKernel]
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
  rw [endpointReplyCheckedArmR_eq_general]
  simp only [endpointReplyCheckedArmGeneralR, hTgt, hAns, hFlow, ↓reduceIte]
  rw [replyTransferOnCoreChecked_congr_words ctx tid c
    { length := len, extraCaps := extraCaps, label := label }
    (replyRecvReplyMessageInfo label
      { registers := Architecture.regMessageBody layout rf len, badge := rcap.badge })
    (Architecture.regMessageRegs layout rf) (Architecture.regMessageBody layout rf len) _ _ _ st
    rfl (fun i fb hi => replyWordOr_regMessageRegs_body layout rf len extraCaps label i fb hi)]
  have hMsg : ({ registers := extractMessageRegisters (Architecture.regMessageRegs layout rf) { length := len, extraCaps := extraCaps, label := label }, badge := rcap.badge } : IpcMessage) =
      { registers := Architecture.regMessageBody layout rf len, badge := rcap.badge } := rfl
  rw [hMsg]
  rcases replyTransferOnCoreChecked ctx tid c _ _
      { registers := Architecture.regMessageBody layout rf len, badge := rcap.badge }
      (rcap.rights.mem .grant) executingCore st with e | ⟨⟨⟩, st1⟩
  · rfl
  · exact replyRecvSignalLeg_eq ctx tid executingCore st st1

/-- The checked reply-receive once its reply capability resolved to reply object
`rid`, answering caller `c` with badge `badge`: the reply leg's flow gate, then a
caller carrying a fault answered through the specification's path (its fault
reply: `replyRecvCallFaultArmR`, in place when the receive blocks or takes a
queued caller, `replyRecvFaultArmR` when it takes a queued sender), and for any
other caller the in-place path when
it may be taken (a reply of at most four words whose reply leg transfers no
capability, `replyRecvReplyInertW`, on every reply arm whose receive blocks in
place, `replyRecvBlockArmCode` and `performReplyRecvArmDelivered`; the take arms
from `replyRecvArmCallTakeR`, the Call take first; `replyRecvCapsArmR` when the reply leg
installs under the grant right, its transfer run in place between the reply's
writes and the receive),
the specification's otherwise.  Every
in-place path delivers the reply as a message, which is the answer only for a
caller carrying no fault, so the fault test runs first.  A receive that
completes the replier's bound notification (`receiveCompletesSignal`) runs
`signalArm` instead, the reply alone and then the completion: the in-place
`replyRecvSignalArmR` on the reply capability the caller resolved. -/
@[inline] def replyRecvResolvedR (ctx : LabelingContext) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) (signalArm : RefusalCarrying Unit) :
    RefusalCarrying Unit :=
  fun st =>
    if securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf c) then
      if receiveCompletesSignal ctx st tid then signalArm st
      else if threadHasPendingFault st c then
        replyRecvCallFaultArmR epId tid c rid badge grant layout rf len label executingCore st
      else if decide (Architecture.regMessageLength layout len ≤ 4) &&
          replyRecvBlockArmCode st epId tid c rid != 0 && replyRecvReplyInertW st tid c grant then
        .ok ((), performReplyRecvArmDelivered
          (ReplyRecvArm.ofCode (replyRecvBlockArmCode st epId tid c rid))
          ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId
          (receiveQueueTailCode st epId) layout rf len badge executingCore)
      else replyRecvArmCallTakeR epId tid c rid badge grant layout rf len label executingCore st
    else .error (.replyCapInvalid, st)

/-- The general reply-receive arm on a message read in registers: the reply
capability at the reply register (`layout.replyReg`, x6), its receive half
`handleRecv` with `canReply` true, as `SysReplyRecv` runs it (WS-SX SX7.3). -/
@[inline] def endpointReplyRecvCheckedArmRegsR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability) :
    RefusalCarrying Unit :=
  endpointReplyRecvCheckedArmGeneralR ctx
    { length := len, extraCaps := extraCaps, label := label }
    (Architecture.regMessageRegs layout rf)
    (SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf layout.replyReg)) tid executingCore cap

/-- WS-ZA ZA4.7: the checked reply-receive arm (`dispatchWithCapChecked`'s
`.replyRecv` case) on a message read in registers, refusing in the state it was
handed (`endpointReplyRecvCheckedArmR_eq`).  The reply capability at the reply
register (x6, WS-SX SX7.3) is resolved in continuation form; a reply-receive
that may block in place on any reply arm (`replyRecvBlockArmCode`) writes in
place (`performReplyRecvArmDelivered`); one whose reply has no caller to answer
receives alone (WS-SX SX7.2). -/
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
        let replyAddr := SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf layout.replyReg)
        callerExtraCapsFailK st tid extraCaps
          (fun _ => endpointReceiveCheckedArmR ctx tid true replyAddr executingCore cap st)
          (fun _ =>
            let resolved := fun rcap rid c badge grant =>
              replyRecvResolvedR ctx epId tid c rid badge grant layout rf len label executingCore
                (replyRecvSignalArmR ctx layout rf len extraCaps label tid executingCore rcap) st
            resolveReplyRecvK st tid replyAddr (fun e => .error (e, st))
              (fun _ => endpointReceiveCheckedArmR ctx tid true replyAddr executingCore cap st)
              resolved)
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
    rw [hExt]
    split
    · rfl
    · simp only [callerExtraCapsFailK_eq]
      cases callerExtraCapsFault? st tid extraCaps with
      | some _ => rfl
      | none =>
      simp only []
      rw [resolveReplyRecvK_eq_of st tid _ _ _ _ (fun rid c badge grant =>
        replyRecvResolvedR ctx epId tid c rid badge grant layout rf len label executingCore
          (fun st' => match replyRecvCompletesSignalArm ctx tid c label
              { registers := Architecture.regMessageBody layout rf len, badge := badge } grant
              executingCore st' with
            | .ok r => .ok r
            | .error e => .error (e, st')) st)
        (fun rcap rid c hT hA => by
          simp only [replyRecvResolvedR]
          split
          · next hFlow =>
            rw [replyRecvSignalArmR_eq ctx layout rf len extraCaps label tid executingCore rcap rid
              c st hT hA hFlow]
          · rfl)]
      cases resolveReplyRecvReplyR st tid (SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf layout.replyReg)) with
      | error e => rfl
      | ok r =>
        cases r with
        | none => rfl
        | some r =>
        obtain ⟨rid, c, badge, grant⟩ := r
        simp only [replyRecvResolvedR]
        split
        · next hFlow =>
          by_cases hSig : receiveCompletesSignal ctx st tid = true
          · simp only [hSig, if_true]
          simp only [hSig, if_false, Bool.false_eq_true]
          split
          · next hFault =>
            rw [replyRecvCallFaultArmR_eq epId tid c rid badge grant layout rf len label
              executingCore st hFault]
            simp only [replyRecvRendezvousR]
          rename_i hNoFault
          rw [replyRecvTransferOnCore_of_no_fault (h := by simpa using hNoFault)]
          split
          · next hG =>
            simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hG
            obtain ⟨⟨hSz, hK⟩, hI⟩ := hG
            obtain ⟨ct, rt, ep, rp, hAd, hT, hRO, hE, hS, hR, hEnq, hRp, hStash, hRecR, hTail⟩ :=
              replyRecvBlockArmCode_spec hK
            have hInert := replyRecvReplyInertW_spec hI hT
            have h := replyRecvOnCore_arm_deliveredRegs _ st epId tid c rid layout rf len badge grant
              executingCore ct rt ep rp hAd hSz hT hRO hE hS hR hEnq hRp hStash hRecR hInert
            rw [hTail]
            generalize endpointReplyRecvOnCore epId tid rid c
              { registers := Architecture.regMessageBody layout rf len, badge := badge } grant
              executingCore st = r at h ⊢
            rcases r with e | ⟨a, st'⟩
            · cases h
            · simp only [Except.ok.injEq] at h ⊢
              exact h.symm
          rw [replyRecvArmCallTakeR_eq epId tid c rid badge grant layout rf len label executingCore
            st (by simpa using hNoFault)]
          simp only [replyRecvRendezvousR]
          rw [replyRecvTransferOnCore_of_no_fault (h := by simpa using hNoFault)]
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
    (hReply : decoded.replyCPtr = SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf layout.replyReg))
    (hCaller : gate.callerId = tid)
    (hRoot : gate.cspaceRootCap = callerCspaceRoot st tid) :
    endpointReplyRecvCheckedArmR ctx layout rf decoded.msgInfo.length decoded.msgInfo.extraCaps
        decoded.msgInfo.label tid executingCore cap st =
      RefusalCarrying.ofKernelReporting
        (replyRecvArmReport ctx tid decoded.msgInfo.extraCaps
          decoded.replyCPtr executingCore cap)
        (dispatchWithCapChecked ctx decoded tid executingCore gate cap) st := by
  rw [endpointReplyRecvCheckedArmR_eq_general]
  unfold endpointReplyRecvCheckedArmRegsR
  rw [hRegs, ← hReply]
  exact endpointReplyRecvCheckedArmGeneralR_eq ctx decoded tid executingCore gate cap st hRR
    hCaller hRoot

/-- The caller a reply-receive's reply leg reaches, read from the pre-state
before the arm, as its code (`SeLe4n.ThreadId.optCode`): the caller recorded
by the reply object the capability at the reply register (x6, WS-SX SX7.3)
names (`replyRecvReplyLegEdges`).  The slot is resolved in continuation form, so
nothing is built. -/
@[inline] def replyRecvTaintCallerCode (st : SystemState) (tid : SeLe4n.ThreadId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (extraCaps : Nat) :
    Nat :=
  callerExtraCapsFailK st tid extraCaps (fun _ => 0) fun _ =>
    match callerCspaceRoot st tid with
    | none => 0
    | some root =>
    lookupSlotFromK root
      (SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf layout.replyReg)) st (fun _ _ _ _ => 0)
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

theorem replyRecvReplyLegEdges_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (tcb : TCB)
    (hTcb : st.getObject? tid.toObjId = some (.tcb tcb))
    (hReply : decoded.replyCPtr = SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf layout.replyReg)) :
    replyRecvReplyLegEdges st tid decoded =
      match replyRecvTaintCallerCode st tid layout rf decoded.msgInfo.extraCaps with
      | 0 => []
      | k + 1 => [{ sink := (⟨k⟩ : SeLe4n.ThreadId).toObjId, source := tid.toObjId }] := by
  have hCR : callerCspaceRoot st tid = tcb.spaceCells[0] := by simp only [callerCspaceRoot, hTcb]
  have hOp : ∀ p, syscallOperandCap? st tid p =
      match lookupSlot tcb p st with
      | .error _ => none
      | .ok ref => SystemState.lookupSlotCap st ref := by
    intro p
    simp only [SystemState.getObject?_eq_getElem] at hTcb
    simp only [syscallOperandCap?, SystemState.getTcb?, hTcb]
    rfl
  unfold replyRecvReplyLegEdges replyRecvTaintCallerCode
  simp only [callerExtraCapsFailK_eq]
  cases callerExtraCapsFault? st tid decoded.msgInfo.extraCaps with
  | some _ => simp
  | none =>
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hReply]
  simp only [hOp, hCR]
  unfold lookupSlot
  cases tcb.spaceCells[0] with
  | none => rfl
  | some root =>
  simp only [lookupSlotFromK_eq]
  cases lookupSlotFrom root _ st with
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

/-- The reply leg's caller code for the capability the operand resolved to:
`replyRecvTaintCallerCode` when it names an endpoint, the only target a
reply-receive declares edges for, and none otherwise. -/
@[inline] def replyRecvTaintCallerCodeOf (st : SystemState) (tid : SeLe4n.ThreadId)
    (cap : Capability) (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (extraCaps : Nat) : Nat :=
  match cap.target with
  | .object _ => replyRecvTaintCallerCode st tid layout rf extraCaps
  | _ => 0

/-- The reply-receive's taint step, without the plan: the receive leg's bound
notification words `wN` and sender words `wS` join the server's, then the server's words `wT` — both captured
before the arm, so the server's are its pre-state's — join the answered
caller's (`replyRecvTaintStep_eq`). -/
@[inline] def replyRecvTaintStep (signalCode sourceCode callerCode : Nat)
    (tid : SeLe4n.ThreadId) (wN wS wT : TaintWords) (post : SystemState) : SystemState :=
  sendTaintStep callerCode tid wT (receiveTaintStep signalCode sourceCode tid wN wS post)

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
            (replyRecvTaintCallerCodeOf st tid cap layout rf decoded.msgInfo.extraCaps) tid
              (wN cap) (wS cap)
            wT post
        | none => post) := by
  simp only [syscallTaintPlan, contentFlowClass, hRR, contentFlowEdges, contentFlowClears,
    contentFlowBypassed]
  rcases syscallOperandCap? st tid decoded.capAddr with _ | cap
  · simp [applySyscallTaintAfter, syscallRecordsDeclassification,
      applyOrigination, applyTaintClears, applyTaintFlow, applyTaintStep]
  · have h := hS cap
    have hN := hN cap
    rcases cap with ⟨target, _, _⟩
    cases target with
    | object epId =>
      simp only [receiveTaintSourceCode, receiveTaintSignalCode, receiverTaintEdges,
        boundSignalTaintEdges, replyRecvTaintCallerCodeOf,
        replyRecvReplyLegEdges_eq st tid decoded layout rf tcb hTcb hReply,
        replyRecvTaintStep] at h hN ⊢
      generalize replyRecvTaintCallerCode st tid layout rf decoded.msgInfo.extraCaps = k
      revert h hN
      generalize boundSignalTaintCode st tid = sc
      cases st.getEndpoint? epId with
      | none =>
        cases sc <;> cases k <;> intro _ hn <;>
          simp only [notifObjOfCode, Nat.add_sub_cancel] at hn <;>
          simp [receiveTaintStep, sendTaintStep, applySyscallTaintAfter,
            syscallRecordsDeclassification, applyOrigination, applyTaintClears, applyTaintFlow,
            applyTaintStep, joinTaintAt_toWords_of_decode _ _ hT,
            joinTaintAt_toWords_of_decode _ _ hn]
      | some ep =>
        simp only [Option.bind_some, ← Endpoint.ofOptCode_sendHeadCode]
        cases sc <;> cases ep.sendHeadCode <;> cases k <;> intro h hn <;>
          simp only [threadObjOfCode, notifObjOfCode, Nat.add_sub_cancel] at h hn <;>
          simp [receiveTaintStep, sendTaintStep, SeLe4n.ThreadId.ofOptCode,
            applySyscallTaintAfter, syscallRecordsDeclassification, applyOrigination,
            applyTaintClears, applyTaintFlow, applyTaintStep,
            joinTaintAt_toWords_of_decode _ _ hT, joinTaintAt_toWords_of_decode _ _ h,
            joinTaintAt_toWords_of_decode _ _ hn]
    | _ =>
      simp [receiveTaintSourceCode, receiveTaintSignalCode, replyRecvTaintCallerCodeOf, replyRecvTaintStep,
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
          let signalCode := receiveTaintSignalCode st tid cap
          let sourceCode := receiveTaintSourceCode st cap
          let callerCode := replyRecvTaintCallerCodeOf st tid cap layout rf extraCaps
          withTaintWordsAt st (notifObjOfCode signalCode) fun n0 n1 n2 n3 n4 n5 n6 n7 nc ns =>
          withTaintWordsAt st (threadObjOfCode sourceCode) fun a0 a1 a2 a3 a4 a5 a6 a7 ac as =>
          withTaintWordsAt st tid.toObjId fun b0 b1 b2 b3 b4 b5 b6 b7 bc bs =>
          match endpointReplyRecvCheckedArmR ctx layout rf len extraCaps label tid executingCore
              cap st with
          | .error refusal => .error refusal
          | .ok ((), stPost) =>
              .ok ((), replyRecvTaintStep signalCode sourceCode callerCode tid
                ⟨n0, n1, n2, n3, n4, n5, n6, n7, nc, ns⟩ ⟨a0, a1, a2, a3, a4, a5, a6, a7, ac, as⟩ ⟨b0, b1, b2, b3, b4, b5, b6, b7, bc, bs⟩
                stPost)
        else .error (syscallMissingRightError .replyRecv, st)

/-- **The state a refusal of a reply-receive's operand arm reports**: its
arm's (`replyRecvArmReport`) once the operand's slot check and rights pass; the
state it was handed otherwise, since every refusal before the arm writes
nothing. -/
def replyRecvOperandReport (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (extraCaps : Nat) (replyAddr : SeLe4n.CPtr) (executingCore : Concurrency.CoreId)
    (requiredRight : AccessRight) (operand : Option Capability) (st : SystemState) :
    SystemState :=
  match operand with
  | none => st
  | some cap =>
    if SeLe4n.Kernel.capTargetsReservedKernelObject cap then st
    else if !syscallTargetAccepted .replyRecv st cap then st
    else if cap.hasRight requiredRight then
      replyRecvArmReport ctx tid extraCaps replyAddr executingCore cap st
    else st

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
    (hRef : lookupSlot tcb decoded.capAddr st = .ok ref) :
    replyRecvOperandArmThenTaintR ctx layout rf decoded.msgInfo.length decoded.msgInfo.extraCaps
        decoded.msgInfo.label tid executingCore
        (syscallRequiredRight decoded.syscallId) (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernelReporting
        (replyRecvOperandReport ctx tid decoded.msgInfo.extraCaps
          decoded.replyCPtr executingCore (syscallRequiredRight decoded.syscallId)
          (SystemState.lookupSlotCap st ref))
        (dispatchCheckedArmThenTaint ctx decoded tid executingCore
        { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr, requiredRight := syscallRequiredRight decoded.syscallId } none
        (syscallTaintPlan st tid decoded) preEpoch preLength st.declassificationTaint) st := by
  have hOperand := syscallOperandCap?_of_resolved st tid _ tcb ref hTcb hRef
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernelReporting,
    hRR, ↓reduceIte, syscallInvokeTyped, syscallResolveCap, SyscallGate.lookupSlot_mk, hRef]
  simp only [replyRecvTaintStep_eq st tid decoded hRR layout rf tcb hTcb hReply
    (wN := fun cap => st.taintWordsAt (notifObjOfCode (receiveTaintSignalCode st tid cap)))
    (wS := fun cap => st.taintWordsAt (threadObjOfCode (receiveTaintSourceCode st cap)))
    (wT := st.taintWordsAt tid.toObjId) (hN := fun _ => decode_taintWordsAt st _)
    (hS := fun _ => decode_taintWordsAt st _)
    (hT := decode_taintWordsAt st _), hOperand]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [replyRecvOperandArmThenTaintR, replyRecvOperandReport]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hType : syscallTargetAccepted .replyRecv st cap = false
      · simp only [hIdle, hType, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      replace hType : syscallTargetAccepted .replyRecv st cap = true := by simpa using hType
      by_cases hRight : cap.hasRight (syscallRequiredRight .replyRecv) = true
      · simp only [hIdle, hType, Bool.not_true, Bool.false_eq_true, hRight, ↓reduceIte, Bool.false_eq_true, withTaintWordsAt_eq,
          TaintWords.mk_fields]
        rw [endpointReplyRecvCheckedArmR_eq ctx decoded tid executingCore
          { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr, requiredRight := syscallRequiredRight decoded.syscallId }
          cap layout rf st hRR hRegs hReply rfl (by simp only [callerCspaceRoot, hTcb])]
        simp only [RefusalCarrying.ofKernelReporting, hRR]
        rcases dispatchWithCapChecked ctx decoded tid executingCore
          { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr, requiredRight := syscallRequiredRight .replyRecv }
          cap st with _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hType, Bool.not_true, Bool.false_eq_true, hRight, ↓reduceIte, Bool.false_eq_true]

/-- WS-ZA ZA4.7: the reply-receive's dispatch: `dispatchOperandCheckedR` with
the reply-receive's arm (`dispatchReplyRecvCheckedR_eq`).

A specification: the compiled entry runs the arm out of line
(`syscallEntryRoutedK`), so no code is generated for it. -/
noncomputable def dispatchReplyRecvCheckedR (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (xc : Nat) : RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore xc
    (replyRecvOperandArmThenTaintR ctx layout rf len extraCaps label tid executingCore
      (syscallRequiredRight .replyRecv))

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
        (operandReport decoded.capAddr tid executingCore
          (syscallExtraCapCount decoded.syscallId decoded.msgInfo.extraCaps)
          (replyRecvOperandReport ctx tid decoded.msgInfo.extraCaps
            decoded.replyCPtr executingCore (syscallRequiredRight .replyRecv)))
        (dispatchSyscallChecked ctx decoded tid executingCore) := by
  funext st
  apply dispatchOperandCheckedR_eq_reporting_at ctx decoded tid executingCore _ _
    (by rw [hRR]; decide) st
  intro tcb ref hTcb hRef
  have hArm := replyRecvOperandArmThenTaintR_eq ctx decoded tid executingCore
    st.declassificationAuditEpoch st.declassificationAudit.length
    st tcb ref layout rf hRR hRegs hReply hTcb hRef
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
  grant && !threadHasPendingFault st c && replyRecvBlockArmCode st epId tid c rid != 0

/-- Whether a long reply-receive answering a caller blocked on this server, the
caller unfaulted, takes a waiting sender in place on some reply arm
(`replyRecvTakeArmCode`).  Out of
line, so the checks are one call. -/
@[noinline] def replyRecvLongTakeAdmits (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) : Bool :=
  !threadHasPendingFault st c && replyRecvTakeArmCode st epId tid c rid != 0

/-- **The long reply-receive whose receive leg takes a waiting sender**
(seL4-MCS's `handleReplyRecv` with a reply of more than four words:
`doReplyTransfer` copying the overflow words, then `receiveIPC` taking a sender
already queued): when `replyRecvLongTakeAdmits` passes and the sender's saved
frame routes as a capability-free send, the reply's writes, the reply leg's
transfer, the take, the caller's long frame and the server's frame, the
sender's six words read from its saved registers before any write.  A reply leg
transferring no capability runs `performReplyRecvArmTakeDeliveredLong`; a granting
one `performReplyRecvArmTakeCapsDeliveredLong`, over the arm.  Any other takes the
specification's path (`replyRecvLongTakeArmR_eq`). -/
@[inline] def replyRecvLongTakeArmR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (rf : SeLe4n.RegisterFile) (len label : Nat) (executingCore : Concurrency.CoreId) :
    RefusalCarrying Unit :=
  fun st =>
    if replyRecvLongTakeAdmits st epId tid c rid then
      match st.getEndpoint? epId with
      | some ep =>
        match ep.sendQ.head with
        | some s =>
          match st.getTcb? s with
          | some sTcb =>
            match Architecture.RegisterDecode.registerRoutedSyscallOf
                (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
                SeLe4n.arm64DefaultLayout sTcb.registerContext with
            | .send _ mi =>
              let f := Architecture.regMessageFrameW SeLe4n.arm64DefaultLayout
                sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged
              if replyRecvReplyInertW st tid c grant then
                .ok ((), performReplyRecvArmTakeDeliveredLong
                  (ReplyRecvArm.ofCode (replyRecvTakeArmCode st epId tid c rid))
                  ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId s
                  sTcb.queueNextCode executingCore rf len badge f.x0 f.x1 f.x2 f.x3 f.x4 f.x5)
              else if grant then
                match st.getTcb? tid with
                | some stcb =>
                  match st.getTcb? c with
                  | some ct =>
                    .ok ((), performReplyRecvArmTakeCapsDeliveredLong
                      (ReplyRecvArm.ofCode (replyRecvTakeArmCode st epId tid c rid))
                      ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid
                      epId s sTcb.queueNextCode executingCore rf len badge f.x0 f.x1 f.x2 f.x3 f.x4 f.x5
                      stcb.spaceCells[2] stcb.ipcBuffer stcb.spaceCells[0] (routedExtraCaps rf)
                      ct.spaceCells[2] ct.ipcBuffer ct.spaceCells[0])
                  | none => replyRecvLongRendezvousR epId tid c rid badge grant rf len label
                      executingCore st
                | none => replyRecvLongRendezvousR epId tid c rid badge grant rf len label
                    executingCore st
              else replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
            | _ => replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
          | none => replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
        | none => replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
      | none => replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
    else replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st

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
    simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hA
    obtain ⟨hNoF, hK⟩ := hA
    obtain ⟨ct, rp, ep, s, sTcb, hAd, hT, hRO, hRp, hEp, hH, hTs, hSC, hF, hG⟩ :=
      replyRecvTakeArmCode_spec hK
    have hE := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp
    have hS := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTs
    simp only [hEp, hH, hTs]
    split
    · next capAddr mi hR =>
      have hR' := (Architecture.RegisterDecode.registerRoutedSyscall_default _).trans hR
      split
      · next hI =>
        have h := replyRecvOnCore_arm_takeDeliveredLong _ st epId tid c rid rf len badge grant
          executingCore ct rp ep s sTcb capAddr mi hAd hLen hSzL hT hRO hRp
          (replyRecvReplyInertW_spec hI hT) hE hH hS hSC hG hR' hF
        rw [Architecture.regMessageFrameW_eq, ← TCB.ipcBadgeView_eq_opt]
        unfold replyRecvLongRendezvousR
        rw [replyRecvTransferOnCore_of_no_fault (h := hNoF)]
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
          split
          · next stcb hS' =>
            split
            · next ct0 hTc0 =>
              have hTc0' := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc0
              obtain rfl : ct = ct0 := by rw [hT] at hTc0'; cases hTc0'; rfl
              have h := replyRecvOnCore_arm_takeCapsDeliveredLong _ st epId tid c rid rf len badge
                executingCore ct rp ep s sTcb capAddr mi stcb _ hAd hLen hSzL hT hRO
                hRp hE hH hS hSC hG hR' hF (hReqOf stcb hS')
              rw [Architecture.regMessageFrameW_eq, ← TCB.ipcBadgeView_eq_opt]
              unfold replyRecvLongRendezvousR
              rw [replyRecvTransferOnCore_of_no_fault (h := hNoF)]
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
    · rfl
  · rfl

/-- Whether a reply-receive with a reply longer than four words, to a caller
with no pending fault, takes the queued caller in place on some reply arm
(`replyRecvCallTakeArmCode`): its reply leg transferring no capability
(`replyRecvReplyInertW`), or granting with the replier's TCB present.  Out of
line and a `Bool`, so the checks are one call and allocate nothing. -/
@[noinline] def replyRecvLongCallTakeAdmits (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (grant : Bool) : Bool :=
  !threadHasPendingFault st c && replyRecvCallTakeArmCode st epId tid c rid != 0 &&
    (replyRecvCallTakeReplyInert st tid c grant || grant && (st.getTcb? tid).isSome)

/-- **The reply-receive taking a queued caller, its reply longer than four
words**: the arm's reply leg and pop, the reply leg's transfer, the take, the
arm's lend and the frames, every context, core and word it takes read on the
pre-state.  A reply leg transferring no capability runs
`performReplyRecvArmCallTakeDeliveredLong`; a granting one
`performReplyRecvArmCallTakeCapsDeliveredLong`.  Out of line, it returns the
state, so nothing is built around it; read only where
`replyRecvLongCallTakeAdmits` passes, and the state unchanged on a shape it
does not admit; the granting leg's capability count (`count`) is read of the
replier's frame by the arm too. The reply enters as the four inline words the arm reads of the replier's
message registers on the pre-state (`Architecture.regLayoutWord`), not as its
register file, so nothing outside the server's TCB holds the register file
when the server's frame is written. -/
@[noinline] def replyRecvLongCallTakeAnswer (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (m0 m1 m2 m3 : UInt64) (count len : Nat) (executingCore : Concurrency.CoreId)
    (st : SystemState) : SystemState :=
  match st.getEndpoint? epId with
  | some ep =>
    match ep.sendQ.head with
    | some s =>
      match st.getTcb? s with
      | some sTcb =>
        match Architecture.RegisterDecode.registerRoutedSyscallOf
            (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
            SeLe4n.arm64DefaultLayout sTcb.registerContext with
        | .call _ mi =>
          if replyRecvCallTakeReplyInert st tid c grant then
            performReplyRecvArmCallTakeDeliveredLong
              (ReplyRecvArm.ofCode (replyRecvCallTakeArmCode st epId tid c rid))
              ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId s
              sTcb.queueNextCode ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s)
              (determineTargetCore st tid) executingCore len badge m0 m1 m2 m3
              sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge)
              sTcb.ipcBadged
          else
            match st.getTcb? tid with
            | some stcb =>
              match st.getTcb? c with
              | some ct =>
                performReplyRecvArmCallTakeCapsDeliveredLong
                  (ReplyRecvArm.ofCode (replyRecvCallTakeArmCode st epId tid c rid))
                  ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid
                  epId s sTcb.queueNextCode ⟨sTcb.scBindingScCode - 1⟩
                  (determineTargetCore st s) (determineTargetCore st tid) executingCore
                  len badge m0 m1 m2 m3 sTcb.registerContext mi.length
                  (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged
                  stcb.spaceCells[2] stcb.ipcBuffer stcb.spaceCells[0]
                  count ct.spaceCells[2] ct.ipcBuffer
                  ct.spaceCells[0]
              | none => st
            | none => st
        | _ => st
      | none => st
    | none => st
  | none => st

/-- **The checked reply-receive whose receive leg takes a queued caller, over
every reply arm** (seL4-MCS's `handleReplyRecv`: `doReplyTransfer`, the reply
arm's `reply_pop`, then `receiveIPC` taking a caller queued by a `Call`, and
`reply_push (canDonate)` lending that caller's context to a server holding
none): when a reply longer than four words, to a caller with no pending fault,
takes the caller in place on some reply arm (`replyRecvLongCallTakeAdmits`),
the take out of line (`replyRecvLongCallTakeAnswer`).  Otherwise the long take
arm (`replyRecvLongTakeArmR`); the specification's path
(`replyRecvLongCallTakeArmR_eq`). -/
@[inline] def replyRecvLongCallTakeArmR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (rf : SeLe4n.RegisterFile) (len label : Nat) (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    if replyRecvLongCallTakeAdmits st epId tid c rid grant then
      .ok ((), replyRecvLongCallTakeAnswer epId tid c rid badge grant
        (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 0)
        (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 1)
        (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 2)
        (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 3) (routedExtraCaps rf) len executingCore st)
    else replyRecvLongTakeArmR epId tid c rid badge grant rf len label executingCore st

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
    simp only [replyRecvLongCallTakeAdmits, Bool.and_eq_true, Bool.or_eq_true,
      Bool.not_eq_true', bne_iff_ne, ne_eq] at hA
    obtain ⟨⟨hNoF, hK⟩, hShape⟩ := hA
    obtain ⟨ct, rp, ep, s, sTcb, capAddr, mi, hAd, hCA, hT, hRO, hRp, hEp, hH, hTs, hSC, hF, hRt⟩ :=
      replyRecvCallTakeArmCode_spec hK
    have hE := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp
    have hS := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTs
    have hTc := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
    have hR' := (Architecture.RegisterDecode.registerRoutedSyscall_default _).trans hRt
    unfold replyRecvLongCallTakeAnswer
    simp only [hEp, hH, hTs, hRt]
    split
    · next hI =>
      have h := replyRecvOnCore_arm_callTakeDeliveredLong _ st epId tid c rid rf len badge grant
        executingCore ct rp ep s sTcb capAddr mi hAd hCA hLen hSzL hT hRO hRp
        (replyRecvReplyInertW_spec hI hT) hE hH hS hSC hR' hF
      unfold replyRecvLongRendezvousR
      rw [replyRecvTransferOnCore_of_no_fault (h := hNoF)]
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
      simp only [hS', hTc]
      have h := replyRecvOnCore_arm_callTakeCapsDeliveredLong _ st epId tid c rid rf len
        badge executingCore ct rp ep s sTcb capAddr mi stcb _ hAd hCA hLen hSzL hT hRO
        hRp hE hH hS hSC hR' hF (hReqOf stcb hS')
      unfold replyRecvLongRendezvousR
      rw [replyRecvTransferOnCore_of_no_fault (h := hNoF)]
      generalize endpointReplyRecvOnCore epId tid rid c
        { registers := longReplyRecvRegs rf st tid len, badge := badge } true
        executingCore st = r at h ⊢
      rcases r with e | ⟨a, st'⟩
      · cases h
      · simp only [Except.ok.injEq] at h ⊢
        exact h.symm
  · exact replyRecvLongTakeArmR_eq epId tid c rid badge grant rf len label executingCore st hLen
      hSzL hReqOf

/-- The long reply-receive whose reply leg transfers, its caller unfaulted:
under the grant right, on every reply arm whose receive leg blocks in place
(`replyRecvBlockArmCode`), the arm's reply leg and pop, the transfer in place,
then the receive's block and the long frame
(`performReplyRecvArmCapsDeliveredLong`); the take arm
(`replyRecvLongTakeArmR`) otherwise (`replyRecvLongCapsR_eq`).  Each shape's guard is one out-of-line call, so a
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
              .ok ((), performReplyRecvArmCapsDeliveredLong
                (ReplyRecvArm.ofCode (replyRecvBlockArmCode st epId tid c rid))
                ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId
                (receiveQueueTailCode st epId) rf len badge executingCore stcb.spaceCells[2]
                stcb.ipcBuffer stcb.spaceCells[0] (routedExtraCaps rf) ct.spaceCells[2] ct.ipcBuffer
                ct.spaceCells[0])
          | none => replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
      | none => replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
    else replyRecvLongCallTakeArmR epId tid c rid badge grant rf len label executingCore st

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
    simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hG
    obtain ⟨⟨hGr, hNoFault⟩, hK⟩ := hG
    subst hGr
    obtain ⟨ct, rt, ep, rp, hAd, hT, hRO, hE, hS, hR', hEnq, hRp, hStash, hRecR, hTail⟩ :=
      replyRecvBlockArmCode_spec hK
    split
    · next stcb hS' =>
      split
      · next ct0 hTc0 =>
        obtain rfl : ct = ct0 := by
          rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp hTc0] at hT; cases hT; rfl
        unfold replyRecvLongRendezvousR
        rw [replyRecvTransferOnCore_of_no_fault (h := hNoFault)]
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
      · rfl
    · rfl
  · exact replyRecvLongCallTakeArmR_eq epId tid c rid badge grant rf len label executingCore st
      hLen hSzL hReqOf

/-- The long reply-receive answering a caller carrying a fault: the long fault
answer (`performFaultAnswerLong`, the reply's words past MR0 read in the
replier's registers and IPC buffer) on every reply arm whose receive leg
blocks in place (`replyRecvBlockArmCode`,
`performReplyRecvArmFaultAnswerLong`) and on every reply arm whose receive
takes a waiting sender (`replyRecvTakeArmCode`,
`performReplyRecvArmFaultTakeDeliveredLong`); the specification's path
otherwise (`replyRecvLongFaultArmR_eq`).  The caller's words are read before the writes
and its TCB is not held across them. -/
@[inline] def replyRecvLongFaultArmR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (rf : SeLe4n.RegisterFile) (len label : Nat) (executingCore : Concurrency.CoreId) :
    RefusalCarrying Unit :=
  fun st =>
    match st.getTcb? c with
    | some ct =>
        if replyRecvBlockArmCode st epId tid c rid != 0 then
          .ok ((), performReplyRecvArmFaultAnswerLong
            (ReplyRecvArm.ofCode (replyRecvBlockArmCode st epId tid c rid))
            ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId
            (receiveQueueTailCode st epId) executingCore ct.faultKind label ct.faultIp ct.faultSp
            ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5
            ct.faultX6 ct.faultX7 rf len)
        else if replyRecvTakeArmCode st epId tid c rid != 0 then
          match st.getEndpoint? epId with
          | some ep =>
            match ep.sendQ.head with
            | some s =>
              match st.getTcb? s with
              | some sTcb =>
                match Architecture.RegisterDecode.registerRoutedSyscallOf
                    (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
                    SeLe4n.arm64DefaultLayout sTcb.registerContext with
                | .send _ mi =>
                  let f := Architecture.regMessageFrameW SeLe4n.arm64DefaultLayout
                    sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge)
                    sTcb.ipcBadged
                  .ok ((), performReplyRecvArmFaultTakeDeliveredLong
                    (ReplyRecvArm.ofCode (replyRecvTakeArmCode st epId tid c rid))
                    ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId s
                    sTcb.queueNextCode executingCore ct.faultKind label ct.faultIp ct.faultSp
                    ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5
                    ct.faultX6 ct.faultX7 rf len f.x0 f.x1 f.x2 f.x3 f.x4 f.x5)
                | _ => replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
              | none => replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
            | none => replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
          | none => replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
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
    · next hK =>
      obtain ⟨ct, rt, ep, rp, hAd, hT, hRO, hE, hS, hR, hEnq, hRp, hStash, hRecR, hTail⟩ :=
        replyRecvBlockArmCode_spec (by simpa using hK)
      obtain rfl : ct = ct0 := by
        rw [hT] at hTc0'; cases hTc0'; rfl
      obtain ⟨hEq, hStg⟩ := replyRecvTransferOnCore_arm_fault_inPlaceLong _ st epId tid c rid
        label rf len badge grant executingCore ct rt ep rp tf hAd hLen hPF hT hRO hE hS hR hEnq hRp
        hStash hRecR
      unfold replyRecvLongRendezvousR
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
        simp only [hEp, hH, hTs]
        split
        · next capAddr mi hR =>
          have h := replyRecvTransferOnCore_arm_faultTakeLong _ st epId tid c rid label
            rf len badge grant executingCore ct rp ep tf s sTcb capAddr mi hAd hLen hPF hT hRO
            hRp hE hH hS hSC hG
            ((Architecture.RegisterDecode.registerRoutedSyscall_default _).trans hR) hFs
          rw [Architecture.regMessageFrameW_eq, ← TCB.ipcBadgeView_eq_opt]
          unfold replyRecvLongRendezvousR
          generalize replyRecvTransferOnCore epId tid rid c label
            { registers := longReplyRecvRegs rf st tid len, badge := badge } grant
            executingCore st = r at h ⊢
          rcases r with e | ⟨a, st'⟩
          · cases h
          · simp only [Except.ok.injEq] at h ⊢
            exact h.symm
        · rfl
      · rfl
  · rfl

/-- **The fault answered and a queued caller taken, its reply longer than four
words**: the arm's reply leg with no message and pop, the take, the arm's lend,
the fault answered from the caller's words and the reply's registers past MR0
(`performReplyRecvArmCallFaultTakeDeliveredLong`, its words past MR3 read from
the replier's buffer), every word read on the pre-state.  Out of line, it
returns the state, so nothing is built around it; read only where
`replyRecvCallTakeArmCode` admits, and the state unchanged on a shape it does
not. The reply enters as the four inline words the arm reads of the replier's
message registers on the pre-state (`Architecture.regLayoutWord`), not as its
register file, so nothing outside the server's TCB holds the register file
when the server's frame is written. -/
@[noinline] def replyRecvLongCallFaultTakeAnswer (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (m0 m1 m2 m3 : UInt64)
    (len label : Nat) (executingCore : Concurrency.CoreId) (st : SystemState) : SystemState :=
  match st.getTcb? c with
  | some ct =>
    match st.getEndpoint? epId with
    | some ep =>
      match ep.sendQ.head with
      | some s =>
        match st.getTcb? s with
        | some sTcb =>
          match Architecture.RegisterDecode.registerRoutedSyscallOf
              (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
              SeLe4n.arm64DefaultLayout sTcb.registerContext with
          | .call _ mi =>
            performReplyRecvArmCallFaultTakeDeliveredLong
              (ReplyRecvArm.ofCode (replyRecvCallTakeArmCode st epId tid c rid))
              ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId s
              sTcb.queueNextCode ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s)
              (determineTargetCore st tid) executingCore ct.faultKind label ct.faultIp
              ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4
              ct.faultX5 ct.faultX6 ct.faultX7 len m0 m1 m2 m3 sTcb.registerContext mi.length
              (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged
          | _ => st
        | none => st
      | none => st
    | none => st
  | none => st

/-- **The checked reply-receive answering a faulted caller and taking a queued
caller, over every reply arm**, its reply longer than four words: when the
receive leg takes a caller queued by a routed capability-free call in place on
some reply arm (`replyRecvCallTakeArmCode`), the take out of line
(`replyRecvLongCallFaultTakeAnswer`); the fault arm (`replyRecvLongFaultArmR`)
otherwise (`replyRecvLongCallFaultArmR_eq`). -/
@[inline] def replyRecvLongCallFaultArmR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (rf : SeLe4n.RegisterFile) (len label : Nat) (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    if replyRecvCallTakeArmCode st epId tid c rid != 0 then
      .ok ((), replyRecvLongCallFaultTakeAnswer epId tid c rid
        (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 0)
        (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 1)
        (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 2)
        (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 3) len label executingCore st)
    else replyRecvLongFaultArmR epId tid c rid badge grant rf len label executingCore st

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
    have h := replyRecvTransferOnCore_arm_callFaultTakeLong _ st epId tid c rid label rf len
      badge grant executingCore ct rp ep tf s sTcb capAddr mi hAd hCA hLen hPF hT hRO hRp hE hH hS
      hSC ((Architecture.RegisterDecode.registerRoutedSyscall_default _).trans hRt) hFs
    unfold replyRecvLongRendezvousR
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

/-- **The long reply-receive whose receive completes the bound notification, in
place**: the long `.reply` arm's reply on the reply capability `rcap`
(`endpointReplyLongCheckedArmR`, its overflow words copied in place), then the
completion, as `replyRecvSignalArmR` runs them for a short reply
(`replyRecvLongSignalArmR_eq`). -/
@[inline] def replyRecvLongSignalArmR (ctx : LabelingContext) (rf : SeLe4n.RegisterFile)
    (len extraCaps label : Nat) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (rcap : Capability) : RefusalCarrying Unit :=
  fun st =>
    match endpointReplyLongCheckedArmR ctx rf len extraCaps label tid executingCore rcap st with
    | .error r => .error r
    | .ok ((), st1) =>
        if receiveCompletesSignal ctx st1 tid && receiverIpcReady st1 tid then
          match notificationWaitGatedR ctx tid (receiverBoundNotification st1 tid) executingCore
              st1 with
          | .ok r => .ok r
          | .error (e, _) => .error (e, st)
        else .ok ((), st1)

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
    .replyRecv (.inr ⟨hR, rfl⟩) hRead hRf]
  unfold endpointReplyLongGeneralR
  simp only [endpointReplyCheckedArmGeneralR, hTgt, hAns, hFlow, ↓reduceIte]
  rw [replyTransferOnCoreChecked_congr_words ctx tid c
    { length := mi.length, extraCaps := mi.extraCaps, label := mi.label }
    (replyRecvReplyMessageInfo mi.label
      { registers := longReplyRecvRegs rf st tid mi.length, badge := rcap.badge })
    (longReplyRegs st tid rf mi.length) (longReplyRecvRegs rf st tid mi.length) _ _ _ st rfl
    (fun i fb hi => by
      rw [← hExt]
      exact replyWordOr_extractMessageRegisters _ _ _ i fb
        (by unfold maxMessageRegisters; omega) rfl)]
  have hMsg : ({ registers := extractMessageRegisters (longReplyRegs st tid rf mi.length) { length := mi.length, extraCaps := mi.extraCaps, label := mi.label }, badge := rcap.badge } : IpcMessage) =
      { registers := longReplyRecvRegs rf st tid mi.length, badge := rcap.badge } := by
    rw [hExt]
  rw [hMsg]
  rcases replyTransferOnCoreChecked ctx tid c _ _
      { registers := longReplyRecvRegs rf st tid mi.length, badge := rcap.badge }
      (rcap.rights.mem .grant) executingCore st with e | ⟨⟨⟩, st1⟩
  · rfl
  · exact replyRecvSignalLeg_eq ctx tid executingCore st st1

/-- The checked long reply-receive once its reply capability resolved to reply
object `rid`, answering caller `c`: the reply leg's flow gate, then a caller
carrying a fault answered by the long fault answer (`replyRecvLongFaultArmR`, in
place when the receive blocks), and for a caller carrying no fault when the
reply-receive may block in place on any reply arm
(`replyRecvBlockArmCode`) and its reply leg transfers no capability
(`replyRecvReplyInertW`), the in-place delivery
(`performReplyRecvArmDeliveredLong`); otherwise the transferring arm
(`replyRecvLongCapsR`), which runs the transfer in place or the
specification's path. -/
@[inline] def replyRecvLongResolvedR (ctx : LabelingContext) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (rf : SeLe4n.RegisterFile) (len label : Nat) (executingCore : Concurrency.CoreId)
    (signalArm : RefusalCarrying Unit) : RefusalCarrying Unit :=
  fun st =>
    if securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf c) then
      if receiveCompletesSignal ctx st tid then signalArm st
      else if threadHasPendingFault st c then
        replyRecvLongCallFaultArmR epId tid c rid badge grant rf len label executingCore st
      else if replyRecvBlockArmCode st epId tid c rid != 0 && replyRecvReplyInertW st tid c grant
          then
        .ok ((), performReplyRecvArmDeliveredLong
          (ReplyRecvArm.ofCode (replyRecvBlockArmCode st epId tid c rid))
          ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId
          (receiveQueueTailCode st epId) rf len badge executingCore)
      else replyRecvLongCapsR epId tid c rid badge grant rf len label executingCore st
    else .error (.replyCapInvalid, st)

/-- The long reply-receive's general arm, its words read where it runs. -/
@[inline] def endpointReplyRecvLongGeneralR (ctx : LabelingContext) (rf : SeLe4n.RegisterFile)
    (len extraCaps label : Nat) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (cap : Capability) : RefusalCarrying Unit :=
  fun st => endpointReplyRecvCheckedArmGeneralR ctx
    { length := len, extraCaps := extraCaps, label := label } (longReplyRegs st tid rf len)
    (SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf SeLe4n.arm64DefaultLayout.replyReg)) tid
    executingCore cap st

/-- The checked reply-receive arm for a message of `len` words, more than four,
refusing in the state it was handed (`endpointReplyRecvLongCheckedArmR_eq`).
The reply capability in the reply register is resolved in continuation form; a reply-receive
that answers an unfaulted caller and then blocks writes in place, copying the
replier's overflow words into the caller's buffer
(`replyRecvOnCore_arm_deliveredLong`), as seL4's `doReplyTransfer` does. -/
@[inline] def endpointReplyRecvLongCheckedArmR (ctx : LabelingContext) (rf : SeLe4n.RegisterFile)
    (len extraCaps label : Nat) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (cap : Capability) : RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object epId =>
      if !endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) then
        .error (.flowDenied, st)
      else
        let replyAddr := SeLe4n.CPtr.ofWord
          (SeLe4n.readRegWord rf SeLe4n.arm64DefaultLayout.replyReg)
        callerExtraCapsFailK st tid extraCaps
          (fun _ => endpointReceiveCheckedArmR ctx tid true replyAddr executingCore cap st)
          (fun _ =>
            resolveReplyRecvK st tid replyAddr (fun e => .error (e, st))
              (fun _ => endpointReceiveCheckedArmR ctx tid true replyAddr executingCore cap st)
              (fun rcap rid c badge grant =>
                replyRecvLongResolvedR ctx epId tid c rid badge grant rf len label executingCore
                  (replyRecvLongSignalArmR ctx rf len extraCaps label tid executingCore rcap) st))
    | _ => .error (.invalidCapability 0, st)

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
  split
  · next epId hTgt =>
    split
    · rfl
    · simp only [callerExtraCapsFailK_eq]
      cases callerExtraCapsFault? st tid mi.extraCaps with
      | some _ => rfl
      | none =>
      simp only []
      rw [resolveReplyRecvK_eq_of st tid _ _ _ _ (fun rid c badge grant =>
        replyRecvLongResolvedR ctx epId tid c rid badge grant rf mi.length mi.label executingCore
          (fun st' => match replyRecvCompletesSignalArm ctx tid c mi.label
              { registers := longReplyRecvRegs rf st' tid mi.length, badge := badge } grant
              executingCore st' with
            | .ok r => .ok r
            | .error e => .error (e, st')) st)
        (fun rcap rid c hT hA => by
          simp only [replyRecvLongResolvedR]
          split
          · next hFlow =>
            rw [replyRecvLongSignalArmR_eq ctx rf capAddr mi tid executingCore rcap rid c st hR
              hRead hRf hT hA hFlow]
          · rfl)]
      cases resolveReplyRecvReplyR st tid
          (SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf SeLe4n.arm64DefaultLayout.replyReg)) with
      | error e => rfl
      | ok r =>
        cases r with
        | none => rfl
        | some r =>
        obtain ⟨rid, c, badge, grant⟩ := r
        simp only [replyRecvLongResolvedR, hExt, hM]
        split
        · by_cases hSig : receiveCompletesSignal ctx st tid = true
          · simp only [hSig, if_true]
          simp only [hSig, if_false, Bool.false_eq_true]
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
              rw [replyRecvTransferOnCore_of_no_fault (h := hNoFault), hTail]
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
  · rfl

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
        (replyRecvArmReport ctx tid decoded.msgInfo.extraCaps
          decoded.replyCPtr executingCore cap)
        (dispatchWithCapChecked ctx decoded tid executingCore gate cap) st := by
  rw [endpointReplyRecvLongCheckedArmR_eq_general ctx rf capAddr decoded.msgInfo tid executingCore
    cap st hR hRead hRf]
  unfold endpointReplyRecvLongGeneralR
  rw [hRegs, ← hReply]
  exact endpointReplyRecvCheckedArmGeneralR_eq ctx decoded tid executingCore gate cap st hRR
    hCaller hRoot

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
          let signalCode := receiveTaintSignalCode st tid cap
          let sourceCode := receiveTaintSourceCode st cap
          let callerCode := replyRecvTaintCallerCodeOf st tid cap SeLe4n.arm64DefaultLayout rf
            extraCaps
          withTaintWordsAt st (notifObjOfCode signalCode) fun n0 n1 n2 n3 n4 n5 n6 n7 nc ns =>
          withTaintWordsAt st (threadObjOfCode sourceCode) fun a0 a1 a2 a3 a4 a5 a6 a7 ac as =>
          withTaintWordsAt st tid.toObjId fun b0 b1 b2 b3 b4 b5 b6 b7 bc bs =>
          match endpointReplyRecvLongCheckedArmR ctx rf len extraCaps label tid executingCore
              cap st with
          | .error refusal => .error refusal
          | .ok ((), stPost) =>
              .ok ((), replyRecvTaintStep signalCode sourceCode callerCode tid
                ⟨n0, n1, n2, n3, n4, n5, n6, n7, nc, ns⟩ ⟨a0, a1, a2, a3, a4, a5, a6, a7, ac, as⟩ ⟨b0, b1, b2, b3, b4, b5, b6, b7, bc, bs⟩
                stPost)
        else .error (syscallMissingRightError .replyRecv, st)

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
    (hRf : ∀ stcb, st.getTcb? tid = some stcb → stcb.registerContext = rf) :
    replyRecvLongOperandArmThenTaintR ctx rf decoded.msgInfo.length decoded.msgInfo.extraCaps
        decoded.msgInfo.label tid executingCore
        (syscallRequiredRight decoded.syscallId) (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernelReporting
        (replyRecvOperandReport ctx tid decoded.msgInfo.extraCaps
          decoded.replyCPtr executingCore (syscallRequiredRight decoded.syscallId)
          (SystemState.lookupSlotCap st ref))
        (dispatchCheckedArmThenTaint ctx decoded tid executingCore
        { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr, requiredRight := syscallRequiredRight decoded.syscallId } none
        (syscallTaintPlan st tid decoded) preEpoch preLength st.declassificationTaint) st := by
  have hOperand := syscallOperandCap?_of_resolved st tid _ tcb ref hTcb hRef
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernelReporting,
    hRR, ↓reduceIte, syscallInvokeTyped, syscallResolveCap, SyscallGate.lookupSlot_mk, hRef]
  simp only [replyRecvTaintStep_eq st tid decoded hRR SeLe4n.arm64DefaultLayout rf tcb hTcb hReply
    (wN := fun cap => st.taintWordsAt (notifObjOfCode (receiveTaintSignalCode st tid cap)))
    (wS := fun cap => st.taintWordsAt (threadObjOfCode (receiveTaintSourceCode st cap)))
    (wT := st.taintWordsAt tid.toObjId) (hN := fun _ => decode_taintWordsAt st _)
    (hS := fun _ => decode_taintWordsAt st _)
    (hT := decode_taintWordsAt st _), hOperand]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [replyRecvLongOperandArmThenTaintR, replyRecvOperandReport]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hType : syscallTargetAccepted .replyRecv st cap = false
      · simp only [hIdle, hType, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      replace hType : syscallTargetAccepted .replyRecv st cap = true := by simpa using hType
      by_cases hRight : cap.hasRight (syscallRequiredRight .replyRecv) = true
      · simp only [hIdle, hType, Bool.not_true, Bool.false_eq_true, hRight, ↓reduceIte, Bool.false_eq_true, withTaintWordsAt_eq,
          TaintWords.mk_fields]
        rw [endpointReplyRecvLongCheckedArmR_eq ctx decoded tid executingCore
          { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr, requiredRight := syscallRequiredRight decoded.syscallId }
          cap rf capAddr st hRR hR hRegs hReply rfl (by simp only [callerCspaceRoot, hTcb])
          hRead hRf]
        simp only [RefusalCarrying.ofKernelReporting, hRR]
        rcases dispatchWithCapChecked ctx decoded tid executingCore
          { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr, requiredRight := syscallRequiredRight .replyRecv }
          cap st with _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hType, Bool.not_true, Bool.false_eq_true, hRight, ↓reduceIte, Bool.false_eq_true]

/-- The long reply-receive's operand dispatch (`dispatchReplyRecvLongCheckedR_eq`).
A specification: the compiled entry runs the arm out of line. -/
noncomputable def dispatchReplyRecvLongCheckedR (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (xc : Nat) : RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore xc
    (replyRecvLongOperandArmThenTaintR ctx rf len extraCaps label tid executingCore
      (syscallRequiredRight .replyRecv))

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
        (operandReport decoded.capAddr tid executingCore
          (syscallExtraCapCount decoded.syscallId decoded.msgInfo.extraCaps)
          (replyRecvOperandReport ctx tid decoded.msgInfo.extraCaps
            decoded.replyCPtr executingCore (syscallRequiredRight .replyRecv)))
        (dispatchSyscallChecked ctx decoded tid executingCore) st := by
  apply dispatchOperandCheckedR_eq_reporting_at ctx decoded tid executingCore _ _
    (by rw [hRR]; decide) st
  intro tcb ref hTcb hRef
  have hArm := replyRecvLongOperandArmThenTaintR_eq ctx decoded tid executingCore
    st.declassificationAuditEpoch st.declassificationAudit.length
    st tcb ref rf capAddr hRR hR hRegs hReply hTcb hRef hRead hRf
  simp only [hRR] at hArm ⊢
  exact hArm

end SeLe4n.Kernel
