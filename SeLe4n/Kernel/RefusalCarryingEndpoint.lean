-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RefusalCarryingDispatch

/-!
# The endpoint syscalls, refusing in the state they were refused in

WS-ZA ZA4.7.  `RefusalCarryingDispatch` gives the signal, the wait and the yield
dispatches that refuse in the state they were handed; this module gives the
endpoint syscalls theirs, each proven equal to `RefusalCarrying.ofKernel` of
the specification's dispatch.  A send with no capabilities to transfer checks
everything before its first write (`endpointSendCrossCoreDispatchChecked_error_state`),
so the state goes to the send and nothing keeps it for a refusal.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open Architecture.RegisterDecode
open Architecture.SyscallArgDecode

/-- The checked send arm (`dispatchWithCapChecked`'s `.send` case) for a
message with no capabilities to transfer, refusing in the state it was handed
(`endpointSendCheckedArmR_eq`).  It takes the message words rather than the
decode, so a caller that reads them from the register file builds no decode
record. -/
@[inline] def endpointSendCheckedArmR (ctx : LabelingContext) (body : Array SeLe4n.RegValue)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability) :
    RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object epId =>
        let woken? := (st.getEndpoint? epId).bind (·.receiveQ.head)
        match endpointSendCrossCoreDispatchChecked ctx epId tid
            { registers := body, caps := #[], badge := cap.badge,
              capsGranted := cap.rights.mem .grant } cap.rights (SeLe4n.Slot.ofNat 0)
            executingCore st with
        | (st', .ok (summary, _)) =>
            .ok ((), Architecture.stageWokenDelivery (clearWokenReceiverStashPure woken? st')
              woken? summary.installedCount)
        | (st', .error e) => .error (e, st')
    | _ => .error (.invalidCapability, st)

theorem endpointSendCheckedArmR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (body : Array SeLe4n.RegValue)
    (hSend : decoded.syscallId = .send)
    (hCaps : decodeExtraCapAddrs decoded = #[])
    (hSlot : decoded.capRecvSlot = SeLe4n.Slot.ofNat 0)
    (hBody : body = extractMessageRegisters decoded.msgRegs decoded.msgInfo) :
    endpointSendCheckedArmR ctx body tid executingCore cap =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap) := by
  subst hBody
  funext st
  simp only [endpointSendCheckedArmR, RefusalCarrying.ofKernel, dispatchWithCapChecked,
    dispatchCapabilityOnly, hSend, hCaps, hSlot, resolveExtraCaps_empty]
  cases cap.target with
  | object epId =>
    simp only []
    rcases hRun : endpointSendCrossCoreDispatchChecked ctx epId tid
        { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo, caps := #[],
          badge := cap.badge, capsGranted := cap.rights.mem .grant } cap.rights
        (SeLe4n.Slot.ofNat 0) executingCore st with ⟨st', _ | ⟨summary, sgi⟩⟩
    · have hst := endpointSendCrossCoreDispatchChecked_error_state ctx epId tid _ cap.rights
        (SeLe4n.Slot.ofNat 0) executingCore st _ rfl (by rw [hRun])
      rw [hRun] at hst
      simp only at hst
      rw [hst]
    · simp only [clearWokenReceiverStash_eq_pure]
  | _ => rfl

/-- The receiver a send's content reaches, read from the pre-state before the
arm: the head of the receive queue of the endpoint its capability names
(`senderTaintEdges`). -/
@[inline] def sendTaintHead? (st : SystemState) (cap : Capability) : Option SeLe4n.ThreadId :=
  match cap.target with
  | .object epId => (st.getEndpoint? epId).bind (·.receiveQ.head)
  | _ => none

/-- The send's taint step, without the plan: the sender's pre-state taint joins
the receiver's (`sendTaintStep_eq`).  It builds no edge list and no plan
record. -/
@[inline] def sendTaintStep (head? : Option SeLe4n.ThreadId) (tid : SeLe4n.ThreadId)
    (preTaint : TaintTable) (post : SystemState) : SystemState :=
  match head? with
  | some r =>
      { post with declassificationTaint :=
          post.declassificationTaint.joinAt r.toObjId (preTaint tid.toObjId) }
  | none => post

theorem sendTaintStep_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (hSend : decoded.syscallId = .send)
    (preEpoch : Nat) (preLog : DeclassificationAuditLog) (preTaint : TaintTable)
    (post : SystemState) :
    applySyscallTaintAfter (syscallTaintPlan st tid decoded) preEpoch preLog preTaint post =
      (match syscallOperandCap? st tid decoded.capAddr with
        | some cap => sendTaintStep (sendTaintHead? st cap) tid preTaint post
        | none => post) := by
  simp only [syscallTaintPlan, contentFlowClass, hSend, contentFlowEdges, contentFlowClears,
    contentFlowBypassed]
  rcases syscallOperandCap? st tid decoded.capAddr with _ | ⟨target, _, _⟩
  · simp [applySyscallTaintAfter, syscallRecordsDeclassification,
      applyOrigination, applyTaintClears, applyTaintFlow]
  · cases target with
    | object epId =>
      simp only [sendTaintHead?, senderTaintEdges]
      cases (st.getEndpoint? epId).bind (·.receiveQ.head) <;>
        simp [sendTaintStep, applySyscallTaintAfter, syscallRecordsDeclassification,
          applyOrigination, applyTaintClears, applyTaintFlow]
    | _ =>
      simp [sendTaintHead?, sendTaintStep, applySyscallTaintAfter,
        syscallRecordsDeclassification, applyOrigination, applyTaintClears, applyTaintFlow]

/-- The send's slot check, gate, arm and taint step on the capability its
operand resolved to, every refusal carrying the state it was handed
(`sendOperandArmThenTaintR_eq`). -/
@[inline] def sendOperandArmThenTaintR (ctx : LabelingContext) (body : Array SeLe4n.RegValue)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (requiredRight : AccessRight)
    (preTaint : TaintTable) (operand : Option Capability) : RefusalCarrying Unit :=
  fun st =>
    match operand with
    | none => .error (.invalidCapability, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedIdleObject cap then .error (.invalidCapability, st)
        else if cap.hasRight requiredRight then
          let head? := sendTaintHead? st cap
          match endpointSendCheckedArmR ctx body tid executingCore cap st with
          | .error refusal => .error refusal
          | .ok ((), stPost) => .ok ((), sendTaintStep head? tid preTaint stPost)
        else .error (.illegalAuthority, st)

theorem sendOperandArmThenTaintR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (preEpoch : Nat) (preLog : DeclassificationAuditLog)
    (preTaint : TaintTable) (st : SystemState) (ref : CSpaceAddr)
    (body : Array SeLe4n.RegValue)
    (hSend : decoded.syscallId = .send)
    (hCaps : decodeExtraCapAddrs decoded = #[])
    (hSlot : decoded.capRecvSlot = SeLe4n.Slot.ofNat 0)
    (hBody : body = extractMessageRegisters decoded.msgRegs decoded.msgInfo)
    (hRef : resolveCapAddress gate.cspaceRoot gate.capAddr gate.capDepth st = .ok ref)
    (hOperand : syscallOperandCap? st tid decoded.capAddr = SystemState.lookupSlotCap st ref) :
    sendOperandArmThenTaintR ctx body tid executingCore gate.requiredRight
        preTaint (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore gate
        (syscallTaintPlan st tid decoded) preEpoch preLog preTaint) st := by
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel,
    hSend, syscallChecksTargetFirst, Bool.false_eq_true, ↓reduceIte, syscallInvoke,
    syscallLookupCap, syscallResolveCap, hRef]
  simp only [sendTaintStep_eq st tid decoded hSend, hOperand]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [sendOperandArmThenTaintR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedIdleObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hRight : cap.hasRight gate.requiredRight = true
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]
        rw [endpointSendCheckedArmR_eq ctx decoded tid executingCore gate cap body hSend hCaps
          hSlot hBody]
        simp only [RefusalCarrying.ofKernel]
        rcases dispatchWithCapChecked ctx decoded tid executingCore gate cap st with
          _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]

/-- The send's dispatch for a message with no capabilities to transfer:
`dispatchOperandCheckedR` with the send's arm (`dispatchSendCheckedR_eq`). -/
@[inline] def dispatchSendCheckedR (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (body : Array SeLe4n.RegValue) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore
    (sendOperandArmThenTaintR ctx body tid executingCore (syscallRequiredRight .send))

theorem dispatchSendCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (body : Array SeLe4n.RegValue) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId)
    (hSend : decoded.syscallId = .send)
    (hCaps : decodeExtraCapAddrs decoded = #[])
    (hSlot : decoded.capRecvSlot = SeLe4n.Slot.ofNat 0)
    (hBody : body = extractMessageRegisters decoded.msgRegs decoded.msgInfo) :
    dispatchSendCheckedR ctx decoded.capAddr body tid executingCore =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) := by
  apply dispatchOperandCheckedR_eq ctx decoded tid executingCore _ (by rw [hSend]; rfl)
    (by rw [hSend]; decide)
  intro st tcb rootCn ref hTcb hRoot hRef
  have hArm := sendOperandArmThenTaintR_eq ctx decoded tid executingCore
    { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
      capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
    st.declassificationAuditEpoch st.declassificationAuditLog st.declassificationTaint
    st ref body hSend hCaps hSlot hBody hRef
    (syscallOperandCap?_of_resolved st tid _ tcb rootCn ref hTcb hRoot hRef)
  simp only [hSend] at hArm ⊢
  exact hArm

end SeLe4n.Kernel
