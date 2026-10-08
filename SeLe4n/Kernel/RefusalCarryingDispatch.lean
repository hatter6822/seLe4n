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

/-- WS-ZA ZA2.4: **where a signal's taint goes**, read from the pre-state before
the arm: no object operand, or the object's `signalDelivery`.  Its constructors
without a thread are boxed scalars, so the common case builds nothing. -/
inductive SignalTaintCase where
  | noObject
  | stored
  | toWaiter (w : SeLe4n.ThreadId)
  | toBound (t : SeLe4n.ThreadId)

/-- WS-ZA ZA2.4: the signal's taint case, from the capability it resolved. -/
def signalTaintCaseOfCap (st : SystemState) (cap : Capability) : SignalTaintCase :=
  match cap.target with
  | .object nid =>
      match signalDelivery st nid with
      | .stored => .stored
      | .toWaiter w => .toWaiter w
      | .toBound t => .toBound t
  | _ => .noObject

/-- WS-ZA ZA2.4: the signal's taint case, from its resolved operand. -/
def signalTaintCaseOf (st : SystemState) (operand : Option Capability) : SignalTaintCase :=
  match operand with
  | some cap => signalTaintCaseOfCap st cap
  | none => .noObject

/-- WS-ZA ZA2.4: the notification the signal's capability names (`⟨0⟩` when it
names none, where `signalTaintCaseOfCap` is `.noObject` and the sink is never
read). -/
def signalTaintSinkOfCap (cap : Capability) : SeLe4n.ObjId :=
  match cap.target with
  | .object nid => nid
  | _ => ⟨0⟩

/-- WS-ZA ZA2.4: the notification the signal's operand names. -/
def signalTaintSinkOf (operand : Option Capability) : SeLe4n.ObjId :=
  match operand with
  | some cap => signalTaintSinkOfCap cap
  | none => ⟨0⟩

/-- WS-ZA ZA2.4: **the signal's taint step, without the plan.**  A signal
originates nothing, so `applySyscallTaintAfter` of its plan is its content
edges and its clear applied to the post-state's table (`signalTaintStep_eq`);
this applies them directly, building no edge list and no plan record. -/
def signalTaintStep (tc : SignalTaintCase) (nid : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (preTaint : TaintTable) (post : SystemState) : SystemState :=
  match tc with
  | .noObject => post
  | .stored =>
      { post with declassificationTaint :=
          post.declassificationTaint.joinAt nid (preTaint tid.toObjId) }
  | .toWaiter w =>
      { post with declassificationTaint :=
          ((post.declassificationTaint.joinAt w.toObjId (preTaint tid.toObjId)).joinAt
            w.toObjId (preTaint nid)).clearAt nid }
  | .toBound t =>
      { post with declassificationTaint :=
          post.declassificationTaint.joinAt t.toObjId (preTaint tid.toObjId) }

theorem signalTaintStep_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (operand : Option Capability)
    (hSig : decoded.syscallId = .notificationSignal) (preEpoch : Nat)
    (preLog : DeclassificationAuditLog) (preTaint : TaintTable) (post : SystemState) :
    applySyscallTaintAfter (signalTaintPlanOf st tid decoded operand) preEpoch preLog preTaint
        post =
      signalTaintStep (signalTaintCaseOf st operand) (signalTaintSinkOf operand) tid preTaint
        post := by
  rcases operand with _ | ⟨target, _, _⟩
  · simp [signalTaintPlanOf, signalTaintCaseOf, signalTaintStep, applySyscallTaintAfter, hSig,
      syscallRecordsDeclassification, applyOrigination, applyTaintClears, applyTaintFlow]
  · cases target with
    | object nid =>
      simp only [signalTaintPlanOf, signalTaintCaseOf, signalTaintSinkOf, signalTaintCaseOfCap,
        signalTaintSinkOfCap, signalTaintEdges, signalClearedNotification,
        signalBypassedNotification]
      cases signalDelivery st nid <;>
        simp [signalTaintStep, applySyscallTaintAfter, hSig, syscallRecordsDeclassification,
          applyOrigination, applyTaintClears, applyTaintFlow]
    | _ =>
      simp [signalTaintPlanOf, signalTaintCaseOf, signalTaintCaseOfCap, signalTaintStep,
        applySyscallTaintAfter, hSig, syscallRecordsDeclassification, applyOrigination,
        applyTaintClears, applyTaintFlow]

/-- The signal's gate and arm, from the capability its operand resolved to:
`syscallResolveCap`'s idle-object check, the rights gate, then
`notificationSignalCheckedArmR` and the taint step, every refusal carrying the
state it was handed (`signalOperandArmThenTaintR_eq`). -/
@[noinline] def signalResolvedArmThenTaintR (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (requiredRight : AccessRight)
    (taintCase : SignalTaintCase) (sink : SeLe4n.ObjId)
    (preTaint : TaintTable) (cap : Capability) : RefusalCarrying Unit :=
  fun st =>
    if SeLe4n.Kernel.capTargetsReservedIdleObject cap then .error (.invalidCapability, st)
    else if cap.hasRight requiredRight then
      match notificationSignalCheckedArmR ctx decoded tid executingCore cap st with
      | .error refusal => .error refusal
      | .ok ((), stPost) =>
          .ok ((), signalTaintStep taintCase sink tid preTaint stPost)
    else .error (.illegalAuthority, st)

/-- The signal's slot check, then `signalResolvedArmThenTaintR` on the
capability found.  Inlined, so the slot read builds no `some`. -/
@[inline] def signalOperandArmThenTaintR (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (requiredRight : AccessRight)
    (preTaint : TaintTable) (operand : Option Capability) : RefusalCarrying Unit :=
  fun st =>
    match operand with
    | none => .error (.invalidCapability, st)
    | some cap =>
        signalResolvedArmThenTaintR ctx decoded tid executingCore requiredRight
          (signalTaintCaseOfCap st cap) (signalTaintSinkOfCap cap) preTaint cap st

theorem signalOperandArmThenTaintR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (preEpoch : Nat) (preLog : DeclassificationAuditLog)
    (preTaint : TaintTable) (st : SystemState) (ref : CSpaceAddr)
    (hSig : decoded.syscallId = .notificationSignal)
    (hRef : resolveCapAddress gate.cspaceRoot gate.capAddr gate.capDepth st = .ok ref) :
    signalOperandArmThenTaintR ctx decoded tid executingCore gate.requiredRight
        preTaint (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore gate
        (signalTaintPlanOf st tid decoded (SystemState.lookupSlotCap st ref))
        preEpoch preLog preTaint) st := by
  simp only [signalOperandArmThenTaintR, dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel,
    hSig, syscallChecksTargetFirst, Bool.false_eq_true, ↓reduceIte, syscallInvoke,
    syscallLookupCap, syscallResolveCap, hRef]
  simp only [signalTaintStep_eq st tid decoded _ hSig]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [signalResolvedArmThenTaintR, signalTaintCaseOf, signalTaintSinkOf]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedIdleObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hRight : cap.hasRight gate.requiredRight = true
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]
        rw [notificationSignalCheckedArmR_eq ctx decoded tid executingCore gate cap hSig]
        simp only [RefusalCarrying.ofKernel]
        rcases dispatchWithCapChecked ctx decoded tid executingCore gate cap st with
          _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]

/-- `Option.isEqSome` decides `current = some tid` without building
`some tid`. -/
theorem threadId_isEqSome_iff (current : Option SeLe4n.ThreadId) (tid : SeLe4n.ThreadId) :
    current.isEqSome tid = true ↔ current = some tid := by
  cases current with
  | none => simp [Option.isEqSome]
  | some cur => simp [Option.isEqSome]

/-- `dispatchSyscallChecked`, refusing in the state it was handed.  The signal
resolves its operand once, for the gate and the taint plan alike, and takes
`signalResolvedArmThenTaintR`, whose every refusal precedes its first write; every other syscall takes `RefusalCarrying.ofKernel` of the
specification. -/
def dispatchSyscallCheckedR (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    if decoded.syscallId = .notificationSignal then
      if !(st.scheduler.currentOnCore executingCore).isEqSome tid then .error (.illegalState, st)
      else
      match st.getObject? tid.toObjId with
      | some (.tcb tcb) =>
        match st.getObject? tcb.cspaceRoot with
        | some (.cnode rootCn) =>
          resolveCapAddressK tcb.cspaceRoot decoded.capAddr rootCn.depth st
            (fun e => .error (e, st))
            (fun cnode slot =>
              signalOperandArmThenTaintR ctx decoded tid executingCore
                (syscallRequiredRight decoded.syscallId) st.declassificationTaint
                (SystemState.lookupSlotCap st { cnode := cnode, slot := slot }) st)
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
    · have hIs : (st.scheduler.currentOnCore executingCore).isEqSome tid = true :=
        (threadId_isEqSome_iff _ _).2 hCur
      have hNot : ¬ (st.scheduler.currentOnCore executingCore ≠ some tid) := fun h => h hCur
      rw [if_neg (by simp only [hIs, Bool.not_true, Bool.false_eq_true, not_false_eq_true]),
        if_neg hNot]
      split
      · next hTcb =>
        split
        · next tcb hTcb' rootCn hRoot =>
          simp only [hTcb, hRoot]
          rw [resolveCapAddressK_eq]
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
            have hArm := signalOperandArmThenTaintR_eq ctx decoded tid executingCore
              { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
                capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
              st.declassificationAuditEpoch st.declassificationAuditLog st.declassificationTaint
              st ref hSig hRef
            simp only [hSig, RefusalCarrying.ofKernel] at hArm
            exact hArm
        · next hRoot => simp only [hTcb, hRoot]
        · next hRoot => simp only [hTcb, hRoot]
      · next hTcb => simp only [hTcb]
      · next hTcb => simp only [hTcb]
    · have hIs : (st.scheduler.currentOnCore executingCore).isEqSome tid = false := by
        cases h : (st.scheduler.currentOnCore executingCore).isEqSome tid
        · rfl
        · exact absurd ((threadId_isEqSome_iff _ _).1 h) hCur
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
      -- `lookupThreadRegisterContext`, read in place: its `.ok (regs, st)` is
      -- two cells this match never needs.
      match st.getObject? tid.toObjId with
      | some (.tcb tcb) =>
        match SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState
                st tid layout tcb.registerContext regCount with
        | .error e => .error (e, st)
        | .ok decoded =>
          if decoded.overflowCount = 0 then
            dispatchSyscallCheckedR ctx decoded tid executingCore st
          else
            RefusalCarrying.ofKernel (syscallEntryChecked ctx layout executingCore regCount) st
      | some _ => .error (.illegalState, st)
      | none => .error (.objectNotFound, st)

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
      · next tcb hObj =>
        have hRegs : lookupThreadRegisterContext tid st = .ok (tcb.registerContext, st) := by
          simp only [lookupThreadRegisterContext, hObj]
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
      · next o hNot hObj =>
        have hRegs : lookupThreadRegisterContext tid st = .error .illegalState := by
          unfold lookupThreadRegisterContext; rw [hObj]
          cases o <;> first | rfl | exact absurd rfl (hNot _)
        simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs,
          Bool.false_eq_true, ↓reduceIte]
      · next hObj =>
        have hRegs : lookupThreadRegisterContext tid st = .error .objectNotFound := by
          simp only [lookupThreadRegisterContext, hObj]
        simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs,
          Bool.false_eq_true, ↓reduceIte]

end SeLe4n.Kernel
