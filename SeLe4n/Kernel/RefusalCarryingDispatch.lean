-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.API

/-!
# The checked syscall entry, refusing in the state it was refused in

WS-ZA ZA1.3.  `Platform.FFI.syscallDispatchFromAbi` answers a refused syscall
from the state the syscall was handed (the cap-fault delivery and the refusal
record).  Against `Kernel`, which drops the state on `.error`, that means
keeping the state alive across the whole dispatch, so every table the syscall
writes is shared and copied whole.  This module gives the entry a
`RefusalCarrying` form proven equal to `RefusalCarrying.ofKernel` of the
specification (`syscallEntryCheckedR_eq`): its refusals carry exactly the state
it was handed, so the caller reads that state off the refusal.

A path refuses in the state it was handed without keeping it only when it
checks everything before its first write.  The notification signal does, on
a call with no overflow words: its refusals all come before the store, and the
cross-core signal itself answers a refusal with the state it was handed
(`notificationSignalBoundOnCore_error_state`).  Every other syscall, and a
signal with overflow words, takes `RefusalCarrying.ofKernel` of the
specification, which keeps the state as before.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- `clearWokenReceiverStash` as the pure update it is: its one write is a
store, which cannot fail. -/
def clearWokenReceiverStashPure (receiver? : Option SeLe4n.ThreadId) (st : SystemState) :
    SystemState :=
  match receiver? with
  | none => st
  | some receiver =>
      match st.getTcb? receiver with
      | some rTcb =>
          match rTcb.pendingReceiveReply with
          | some _ =>
              st.withObjectStored receiver.toObjId (.tcb { rTcb with pendingReceiveReply := none })
          | none => st
      | none => st

theorem clearWokenReceiverStash_eq_pure (receiver? : Option SeLe4n.ThreadId)
    (st : SystemState) :
    clearWokenReceiverStash receiver? st = .ok ((), clearWokenReceiverStashPure receiver? st) := by
  cases receiver? with
  | none => rfl
  | some receiver =>
    simp only [clearWokenReceiverStash, clearWokenReceiverStashPure]
    rcases st.getTcb? receiver with _ | rTcb
    · rfl
    · simp only []
      rcases rTcb.pendingReceiveReply with _ | _
      · rfl
      · exact SystemState.storeObject_eq_withObjectStored _ _ _

/-- The checked cross-core signal answers a refusal with the state it was
handed: the flow gates refuse before anything is written, and the signal
itself returns its pre-state on every error. -/
theorem notificationSignalBoundCrossCoreDispatchChecked_error_state (ctx : LabelingContext)
    (notificationId : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId) (badge : SeLe4n.Badge)
    (executingCore : Concurrency.CoreId) (st : SystemState) (e : KernelError)
    (h : (notificationSignalBoundCrossCoreDispatchChecked ctx notificationId signaler badge
      executingCore st).2 = .error e) :
    (notificationSignalBoundCrossCoreDispatchChecked ctx notificationId signaler badge
      executingCore st).1 = st := by
  unfold notificationSignalBoundCrossCoreDispatchChecked at h ⊢
  by_cases hFlow : securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf notificationId)
  · simp only [hFlow, ↓reduceIte] at h ⊢
    cases hTarget : boundDeliveryTarget? st notificationId with
    | none =>
      simp only [hTarget] at h ⊢
      exact notificationSignalBoundOnCore_error_state _ _ _ st e h
    | some target =>
      obtain ⟨receiver, _⟩ := target
      simp only [hTarget] at h ⊢
      by_cases hRecv : securityFlowsTo (ctx.objectLabelOf notificationId) (ctx.threadLabelOf receiver)
      · simp only [hRecv, ↓reduceIte] at h ⊢
        exact notificationSignalBoundOnCore_error_state _ _ _ st e h
      · simp only [hRecv, Bool.false_eq_true, ↓reduceIte]
  · simp only [hFlow, Bool.false_eq_true, ↓reduceIte]

/-- The checked signal arm (`dispatchWithCapChecked`'s `.notificationSignal`
case), refusing in the state it was handed.  Its refusals all precede its
writes, so the state on a refusal is the one the arm was handed
(`notificationSignalCheckedArmR_eq`). -/
def notificationSignalCheckedArmR (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability) :
    RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object notifId =>
        match Architecture.SyscallArgDecode.decodeNotificationSignalArgs decoded with
        | .error e => .error (e, st)
        | .ok args =>
            let woken? := (boundDeliveryTarget? st notifId).map (·.1)
            let plainWaiter? := notificationSignalWaiter? st notifId
            match notificationSignalBoundCrossCoreDispatchChecked ctx notifId tid args.badge
                executingCore st with
            | (st', .ok _) =>
                .ok ((), Architecture.stageWokenDelivery
                          (Architecture.stageWokenDelivery
                            (clearWokenReceiverStashPure woken? st') woken? 0)
                          plainWaiter? 0)
            | (st', .error e) => .error (e, st')
    | _ => .error (.invalidCapability, st)

theorem notificationSignalCheckedArmR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (hSig : decoded.syscallId = .notificationSignal) :
    notificationSignalCheckedArmR ctx decoded tid executingCore cap =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap) := by
  funext st
  simp only [notificationSignalCheckedArmR, RefusalCarrying.ofKernel, dispatchWithCapChecked,
    dispatchCapabilityOnly, hSig]
  cases cap.target with
  | object notifId =>
    simp only []
    cases Architecture.SyscallArgDecode.decodeNotificationSignalArgs decoded with
    | error e => rfl
    | ok args =>
      simp only []
      rcases hRun : notificationSignalBoundCrossCoreDispatchChecked ctx notifId tid args.badge
          executingCore st with ⟨st', _ | r⟩
      · have hst := notificationSignalBoundCrossCoreDispatchChecked_error_state ctx notifId tid
          args.badge executingCore st _ (by rw [hRun])
        rw [hRun] at hst
        simp only at hst
        rw [hst]
      · simp only [clearWokenReceiverStash_eq_pure]
  | _ => rfl

/-- The signal's taint plan (`syscallTaintPlan`) from its operand, resolved
once by the caller instead of once per plan field
(`syscallTaintPlan_eq_signalTaintPlanOf`). -/
def signalTaintPlanOf (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (operand : Option Capability) : TaintPlan :=
  match operand with
  | some cap =>
      match cap.target with
      | .object nid =>
          { edges := signalTaintEdges st tid nid
            cleared := signalClearedNotification st nid
            bypassed := signalBypassedNotification st nid
            originates := syscallRecordsDeclassification decoded.syscallId }
      | _ => { originates := syscallRecordsDeclassification decoded.syscallId }
  | none => { originates := syscallRecordsDeclassification decoded.syscallId }

theorem syscallTaintPlan_eq_signalTaintPlanOf (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (hSig : decoded.syscallId = .notificationSignal) :
    syscallTaintPlan st tid decoded =
      signalTaintPlanOf st tid decoded (syscallOperandCap? st tid decoded.capAddr) := by
  simp only [syscallTaintPlan, contentFlowClass, hSig, contentFlowEdges, contentFlowClears,
    contentFlowBypassed, signalTaintPlanOf]
  rcases syscallOperandCap? st tid decoded.capAddr with _ | ⟨target, _, _⟩
  · rfl
  · cases target <;> rfl

/-- The signal's gate and arm, from its operand resolved once by the caller:
`syscallResolveCap`'s slot check and idle-object check, the rights gate, then
`notificationSignalCheckedArmR` and the taint step, every refusal carrying the
state it was handed (`signalResolvedArmThenTaintR_eq`). -/
@[noinline] def signalResolvedArmThenTaintR (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (requiredRight : AccessRight)
    (plan : TaintPlan) (preEpoch : Nat) (preLog : DeclassificationAuditLog)
    (preTaint : TaintTable) (operand : Option Capability) : RefusalCarrying Unit :=
  fun st =>
    match operand with
    | none => .error (.invalidCapability, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedIdleObject cap then .error (.invalidCapability, st)
        else if cap.hasRight requiredRight then
          match notificationSignalCheckedArmR ctx decoded tid executingCore cap st with
          | .error refusal => .error refusal
          | .ok ((), stPost) =>
              .ok ((), applySyscallTaintAfter plan preEpoch preLog preTaint stPost)
        else .error (.illegalAuthority, st)

theorem signalResolvedArmThenTaintR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (plan : TaintPlan) (preEpoch : Nat) (preLog : DeclassificationAuditLog)
    (preTaint : TaintTable) (st : SystemState) (ref : CSpaceAddr)
    (hSig : decoded.syscallId = .notificationSignal)
    (hRef : resolveCapAddress gate.cspaceRoot gate.capAddr gate.capDepth st = .ok ref) :
    signalResolvedArmThenTaintR ctx decoded tid executingCore gate.requiredRight plan preEpoch
        preLog preTaint (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore gate
        plan preEpoch preLog preTaint) st := by
  simp only [signalResolvedArmThenTaintR, dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel,
    hSig, syscallChecksTargetFirst, Bool.false_eq_true, ↓reduceIte, syscallInvoke,
    syscallLookupCap, syscallResolveCap, hRef]
  rcases SystemState.lookupSlotCap st ref with _ | cap
  · rfl
  · by_cases hIdle : SeLe4n.Kernel.capTargetsReservedIdleObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hRight : cap.hasRight gate.requiredRight = true
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]
        rw [notificationSignalCheckedArmR_eq ctx decoded tid executingCore gate cap hSig]
        simp only [RefusalCarrying.ofKernel]
        rcases dispatchWithCapChecked ctx decoded tid executingCore gate cap st with
          _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]

/-- Whether `tid` is the thread `current` names, compared on the identifier's
word: no `some tid` is built and no equality instance is passed
(`isCurrent_iff`). -/
@[inline] def isCurrent (current : Option SeLe4n.ThreadId) (tid : SeLe4n.ThreadId) : Bool :=
  match current with
  | some cur => cur.val == tid.val
  | none => false

theorem isCurrent_iff (current : Option SeLe4n.ThreadId) (tid : SeLe4n.ThreadId) :
    isCurrent current tid = true ↔ current = some tid := by
  cases current with
  | none => simp [isCurrent]
  | some cur =>
    cases cur; cases tid
    simp [isCurrent]

/-- `dispatchSyscallChecked`, refusing in the state it was handed.  The signal
resolves its operand once, for the gate and the taint plan alike, and takes
`signalResolvedArmThenTaintR`, whose every refusal precedes its first write; every other syscall takes `RefusalCarrying.ofKernel` of the
specification. -/
def dispatchSyscallCheckedR (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    if decoded.syscallId = .notificationSignal then
      if !isCurrent (st.scheduler.currentOnCore executingCore) tid then .error (.illegalState, st)
      else
      match st.getObject? tid.toObjId with
      | some (.tcb tcb) =>
        match st.getObject? tcb.cspaceRoot with
        | some (.cnode rootCn) =>
          match resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth st with
          | .error e => .error (e, st)
          | .ok ref =>
            let operand := SystemState.lookupSlotCap st ref
            signalResolvedArmThenTaintR ctx decoded tid executingCore
              (syscallRequiredRight decoded.syscallId) (signalTaintPlanOf st tid decoded operand)
              st.declassificationAuditEpoch st.declassificationAuditLog
              st.declassificationTaint operand st
        | some _ => .error (.invalidCapability, st)
        | none   => .error (.objectNotFound, st)
      | some _ => .error (.illegalState, st)
      | none   => .error (.objectNotFound, st)
    else
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) st

theorem dispatchSyscallCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) :
    dispatchSyscallCheckedR ctx decoded tid executingCore =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) := by
  funext st
  by_cases hSig : decoded.syscallId = .notificationSignal
  · rw [dispatchSyscallChecked_eq_impl]
    simp only [dispatchSyscallCheckedR, hSig, ↓reduceIte, RefusalCarrying.ofKernel,
      dispatchSyscallCheckedImpl]
    by_cases hCur : st.scheduler.currentOnCore executingCore = some tid
    · have hIs : isCurrent (st.scheduler.currentOnCore executingCore) tid = true :=
        (isCurrent_iff _ _).2 hCur
      have hNot : ¬ (st.scheduler.currentOnCore executingCore ≠ some tid) := fun h => h hCur
      rw [if_neg (by simp only [hIs, Bool.not_true, Bool.false_eq_true, not_false_eq_true]),
        if_neg hNot]
      split
      · next hTcb =>
        split
        · next tcb hTcb' rootCn hRoot =>
          simp only [hTcb, hRoot]
          rcases hRef : resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth st with
            e | ref
          · simp only [dispatchCheckedArmThenTaint, hSig, syscallChecksTargetFirst,
              Bool.false_eq_true, ↓reduceIte, syscallInvoke, syscallLookupCap,
              syscallResolveCap, hRef]
          · have hOperand : syscallOperandCap? st tid decoded.capAddr =
                SystemState.lookupSlotCap st ref := by
              simp only [SystemState.getObject?_eq_getElem] at hTcb hRoot
              simp only [syscallOperandCap?, SystemState.getTcb?, SystemState.getCNode?, hTcb,
                hRoot, hRef]
            simp only []
            rw [syscallTaintPlan_eq_signalTaintPlanOf st tid decoded hSig, hOperand]
            have hArm := signalResolvedArmThenTaintR_eq ctx decoded tid executingCore
              { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
                capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
              (signalTaintPlanOf st tid decoded (SystemState.lookupSlotCap st ref))
              st.declassificationAuditEpoch st.declassificationAuditLog st.declassificationTaint
              st ref hSig hRef
            simp only [hSig, RefusalCarrying.ofKernel] at hArm
            exact hArm
        · next hRoot => simp only [hTcb, hRoot]
        · next hRoot => simp only [hTcb, hRoot]
      · next hTcb => simp only [hTcb]
      · next hTcb => simp only [hTcb]
    · have hIs : isCurrent (st.scheduler.currentOnCore executingCore) tid = false := by
        cases h : isCurrent (st.scheduler.currentOnCore executingCore) tid
        · rfl
        · exact absurd ((isCurrent_iff _ _).1 h) hCur
      rw [if_pos (by simp only [hIs, Bool.not_false]), if_pos hCur]
  · simp only [dispatchSyscallCheckedR, hSig, ↓reduceIte]

/-- `syscallEntryChecked`, refusing in the state it was handed
(`syscallEntryCheckedR_eq`).  The decode writes nothing, and a call with no
overflow words fills no TLB entry (`tlbFillIpcBufferOnCore_zero`), so such a
call hands the dispatcher the entry's own state and `dispatchSyscallCheckedR`
refuses in it.  A call with overflow words keeps the specification's form. -/
def syscallEntryCheckedR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout)
    (executingCore : Concurrency.CoreId)
    (regCount : Nat := 32) : RefusalCarrying Unit :=
  fun st =>
    if isInsecureDefaultContext ctx then .error (.policyDenied, st)
    else
    match st.scheduler.currentOnCore executingCore with
    | none => .error (.illegalState, st)
    | some tid =>
      match lookupThreadRegisterContext tid st with
      | .error e => .error (e, st)
      | .ok (regs, _) =>
        match SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState
                st tid layout regs regCount with
        | .error e => .error (e, st)
        | .ok decoded =>
          if decoded.overflowCount = 0 then
            dispatchSyscallCheckedR ctx decoded tid executingCore st
          else
            RefusalCarrying.ofKernel (syscallEntryChecked ctx layout executingCore regCount) st

theorem syscallEntryCheckedR_eq (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : Concurrency.CoreId)
    (regCount : Nat) :
    syscallEntryCheckedR ctx layout executingCore regCount =
      RefusalCarrying.ofKernel (syscallEntryChecked ctx layout executingCore regCount) := by
  funext st
  simp only [syscallEntryCheckedR]
  split
  · next hCtx => simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, ↓reduceIte]
  · next hCtx =>
    split
    · next hCur => simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur,
        Bool.false_eq_true, ↓reduceIte]
    · next tid hCur =>
      split
      · next e hRegs => simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur,
          hRegs, Bool.false_eq_true, ↓reduceIte]
      · next regs _ hRegs =>
        split
        · next e hDec => simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur,
            hRegs, hDec, Bool.false_eq_true, ↓reduceIte]
        · next decoded hDec =>
          split
          · next hZero =>
            rw [dispatchSyscallCheckedR_eq]
            simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
              hZero, Bool.false_eq_true, ↓reduceIte,
              SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_zero]
          · rfl

end SeLe4n.Kernel
