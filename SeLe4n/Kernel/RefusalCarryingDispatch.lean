-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.API
import SeLe4n.Kernel.Scheduler.Operations.PerCoreScheduleFrames

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
(`notificationSignalCheckedArmR_eq`).  It takes the decode's signal arguments
rather than the decode, so a caller that reads the badge straight from the
register file builds no message array. -/
@[inline] def notificationSignalCheckedArmR (ctx : LabelingContext)
    (sigArgs : Except KernelError Architecture.SyscallArgDecode.NotificationSignalArgs)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability) :
    RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object notifId =>
        match sigArgs with
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
    (sigArgs : Except KernelError Architecture.SyscallArgDecode.NotificationSignalArgs)
    (hSig : decoded.syscallId = .notificationSignal)
    (hArgs : sigArgs = Architecture.SyscallArgDecode.decodeNotificationSignalArgs decoded) :
    notificationSignalCheckedArmR ctx sigArgs tid executingCore cap =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap) := by
  subst hArgs
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
@[inline] def signalResolvedArmThenTaintR (ctx : LabelingContext)
    (sigArgs : Except KernelError Architecture.SyscallArgDecode.NotificationSignalArgs) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (requiredRight : AccessRight)
    (taintCase : SignalTaintCase) (sink : SeLe4n.ObjId)
    (preTaint : TaintTable) (cap : Capability) : RefusalCarrying Unit :=
  fun st =>
    if SeLe4n.Kernel.capTargetsReservedIdleObject cap then .error (.invalidCapability, st)
    else if cap.hasRight requiredRight then
      match notificationSignalCheckedArmR ctx sigArgs tid executingCore cap st with
      | .error refusal => .error refusal
      | .ok ((), stPost) =>
          .ok ((), signalTaintStep taintCase sink tid preTaint stPost)
    else .error (.illegalAuthority, st)

/-- The signal's slot check, then `signalResolvedArmThenTaintR` on the
capability found.  Inlined, so the slot read builds no `some`. -/
@[inline] def signalOperandArmThenTaintR (ctx : LabelingContext)
    (sigArgs : Except KernelError Architecture.SyscallArgDecode.NotificationSignalArgs) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (requiredRight : AccessRight)
    (preTaint : TaintTable) (operand : Option Capability) : RefusalCarrying Unit :=
  fun st =>
    match operand with
    | none => .error (.invalidCapability, st)
    | some cap =>
        signalResolvedArmThenTaintR ctx sigArgs tid executingCore requiredRight
          (signalTaintCaseOfCap st cap) (signalTaintSinkOfCap cap) preTaint cap st

theorem signalOperandArmThenTaintR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (preEpoch : Nat) (preLog : DeclassificationAuditLog)
    (preTaint : TaintTable) (st : SystemState) (ref : CSpaceAddr)
    (sigArgs : Except KernelError Architecture.SyscallArgDecode.NotificationSignalArgs)
    (hSig : decoded.syscallId = .notificationSignal)
    (hArgs : sigArgs = Architecture.SyscallArgDecode.decodeNotificationSignalArgs decoded)
    (hRef : resolveCapAddress gate.cspaceRoot gate.capAddr gate.capDepth st = .ok ref) :
    signalOperandArmThenTaintR ctx sigArgs tid executingCore gate.requiredRight
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
        rw [notificationSignalCheckedArmR_eq ctx decoded tid executingCore gate cap sigArgs hSig
          hArgs]
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

/-- The wait answers a refusal with the state it was handed: every refusal in
`notificationWaitOnCore` precedes its writes or returns its pre-state. -/
theorem notificationWaitOnCore_error_state (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (st : SystemState)
    (e : KernelError)
    (h : (notificationWaitOnCore notificationId waiter executingCore st).2 = .error e) :
    (notificationWaitOnCore notificationId waiter executingCore st).1 = st := by
  unfold notificationWaitOnCore at h ⊢
  repeat' split at h <;> (try simp only [] at h ⊢) <;> (try split) <;> (try rfl) <;>
    (try simp_all)

/-- The wait's consumed badge staged into the caller's return registers:
`writeReturnFrameToTcb` of `returnFrameOfBadge` (`stageBadgeReturn_eq`), with
the frame's words written straight into the register file, so no frame record
is built and an exclusively held TCB is rewritten in its slot. -/
@[inline] def stageBadgeReturn (st : SystemState) (tid : SeLe4n.ThreadId)
    (badge : SeLe4n.Badge) : SystemState :=
  st.updateTcb tid (fun t => { t with registerContext :=
    { t.registerContext with
      x0 := badge.word, x1 := 0, x2 := 0, x3 := 0, x4 := 0, x5 := 0 } })

theorem stageBadgeReturn_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (badge : SeLe4n.Badge) :
    stageBadgeReturn st tid badge =
      Architecture.writeReturnFrameToTcb st tid (Architecture.returnFrameOfBadge badge) := rfl

/-- The wait arm's specification form, refusing in the state it was handed
(`notificationWaitOnCore_error_state`): the path every wait takes that does
not consume its badge in place. -/
def notificationWaitArmGeneralR (notifId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    match notificationWaitOnCore notifId tid executingCore st with
    | (st', .ok (some badge)) =>
        .ok ((), Architecture.writeReturnFrameToTcb st' tid (Architecture.returnFrameOfBadge badge))
    | (st', .ok none) => .ok ((), st')
    | (st', .error e) => .error (e, st')

/-- The checked wait arm (`dispatchWithCapChecked`'s `.notificationWait` case),
refusing in the state it was handed (`notificationWaitCheckedArmR_eq`).  A wait
that consumes a pending badge in place (`waitConsumesInPlace`) writes the
notification, the waiter's state and its return registers each in its slot and
builds no result; every other wait takes the specification's form. -/
@[inline] def notificationWaitCheckedArmR (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (cap : Capability) : RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object notifId =>
        if securityFlowsTo (ctx.objectLabelOf notifId) (ctx.threadLabelOf tid) then
          match st.getNotification? notifId with
          | some ntfn =>
              match ntfn.pendingBadge with
              | some badge =>
                  if waitConsumesInPlace st notifId tid then
                    .ok ((), stageBadgeReturn (storeWaitConsumed st notifId tid) tid badge)
                  else notificationWaitArmGeneralR notifId tid executingCore st
              | none => notificationWaitArmGeneralR notifId tid executingCore st
          | none => notificationWaitArmGeneralR notifId tid executingCore st
        else .error (.flowDenied, st)
    | _ => .error (.invalidCapability, st)

theorem notificationWaitArmGeneralR_eq (notifId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (st : SystemState) :
    notificationWaitArmGeneralR notifId tid executingCore st =
      RefusalCarrying.ofKernel (fun st =>
        match notificationWaitOnCore notifId tid executingCore st with
        | (st', .ok (some badge)) =>
            .ok ((), Architecture.writeReturnFrameToTcb st' tid
              (Architecture.returnFrameOfBadge badge))
        | (st', .ok none) => .ok ((), st')
        | (_, .error e) => .error e) st := by
  simp only [notificationWaitArmGeneralR, RefusalCarrying.ofKernel]
  rcases hRun : notificationWaitOnCore notifId tid executingCore st with ⟨st', _ | _ | badge⟩
  · have hst := notificationWaitOnCore_error_state notifId tid executingCore st _
      (by rw [hRun])
    rw [hRun] at hst
    simp only at hst
    rw [hst]
  · rfl
  · rfl

theorem notificationWaitCheckedArmR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (hWait : decoded.syscallId = .notificationWait) :
    notificationWaitCheckedArmR ctx tid executingCore cap =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap) := by
  funext st
  simp only [notificationWaitCheckedArmR, dispatchWithCapChecked, dispatchCapabilityOnly, hWait]
  cases cap.target with
  | object notifId =>
    simp only [notificationWaitCrossCoreDispatchChecked]
    by_cases hFlow : securityFlowsTo (ctx.objectLabelOf notifId) (ctx.threadLabelOf tid) = true
    · simp only [hFlow, ↓reduceIte]
      have hGen := notificationWaitArmGeneralR_eq notifId tid executingCore st
      simp only [RefusalCarrying.ofKernel] at hGen ⊢
      split
      · next ntfn hN =>
        split
        · next badge hB =>
          split
          · next hG =>
            rw [notificationWaitOnCore_eq_impl]
            simp only [notificationWaitOnCoreImpl, hN, hB, hG, ↓reduceIte,
              stageBadgeReturn_eq]
          · exact hGen
        · exact hGen
      · exact hGen
    · simp only [hFlow, Bool.false_eq_true, ↓reduceIte, RefusalCarrying.ofKernel]
  | _ => rfl

/-- The wait's taint step from the capability its operand resolved to: the
notification's taint moves to the waiter and the notification's is cleared
(`syscallTaintPlan`'s `.notificationWait` plan, `waitTaintStep_eq`). -/
def waitTaintStepOfCap (cap : Capability) (tid : SeLe4n.ThreadId)
    (preTaint : TaintTable) (post : SystemState) : SystemState :=
  match cap.target with
  | .object nid =>
      { post with declassificationTaint :=
          (post.declassificationTaint.joinAt tid.toObjId (preTaint nid)).clearAt nid }
  | _ => post

theorem waitTaintStep_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (hWait : decoded.syscallId = .notificationWait)
    (preEpoch : Nat) (preLog : DeclassificationAuditLog) (preTaint : TaintTable)
    (post : SystemState) :
    applySyscallTaintAfter (syscallTaintPlan st tid decoded) preEpoch preLog preTaint post =
      (match syscallOperandCap? st tid decoded.capAddr with
        | some cap => waitTaintStepOfCap cap tid preTaint post
        | none => post) := by
  simp only [syscallTaintPlan, contentFlowClass, hWait, contentFlowEdges, contentFlowClears,
    contentFlowBypassed]
  rcases syscallOperandCap? st tid decoded.capAddr with _ | ⟨target, _, _⟩
  · simp [applySyscallTaintAfter, syscallRecordsDeclassification,
      applyOrigination, applyTaintClears, applyTaintFlow]
  · cases target <;>
      simp [waitTaintStepOfCap, waitTaintEdges, applySyscallTaintAfter,
        syscallRecordsDeclassification, applyOrigination, applyTaintClears, applyTaintFlow]

/-- The wait's slot check, gate, arm and taint step on the capability its
operand resolved to, every refusal carrying the state it was handed
(`waitOperandArmThenTaintR_eq`). -/
@[inline] def waitOperandArmThenTaintR (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (requiredRight : AccessRight)
    (preTaint : TaintTable) (operand : Option Capability) : RefusalCarrying Unit :=
  fun st =>
    match operand with
    | none => .error (.invalidCapability, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedIdleObject cap then .error (.invalidCapability, st)
        else if cap.hasRight requiredRight then
          match notificationWaitCheckedArmR ctx tid executingCore cap st with
          | .error refusal => .error refusal
          | .ok ((), stPost) => .ok ((), waitTaintStepOfCap cap tid preTaint stPost)
        else .error (.illegalAuthority, st)

theorem waitOperandArmThenTaintR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (preEpoch : Nat) (preLog : DeclassificationAuditLog)
    (preTaint : TaintTable) (st : SystemState) (ref : CSpaceAddr)
    (hWait : decoded.syscallId = .notificationWait)
    (hRef : resolveCapAddress gate.cspaceRoot gate.capAddr gate.capDepth st = .ok ref)
    (hOperand : syscallOperandCap? st tid decoded.capAddr = SystemState.lookupSlotCap st ref) :
    waitOperandArmThenTaintR ctx tid executingCore gate.requiredRight
        preTaint (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore gate
        (syscallTaintPlan st tid decoded) preEpoch preLog preTaint) st := by
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel,
    hWait, syscallChecksTargetFirst, Bool.false_eq_true, ↓reduceIte, syscallInvoke,
    syscallLookupCap, syscallResolveCap, hRef]
  simp only [waitTaintStep_eq st tid decoded hWait, hOperand]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [waitOperandArmThenTaintR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedIdleObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hRight : cap.hasRight gate.requiredRight = true
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]
        rw [notificationWaitCheckedArmR_eq ctx decoded tid executingCore gate cap hWait]
        simp only [RefusalCarrying.ofKernel]
        rcases dispatchWithCapChecked ctx decoded tid executingCore gate cap st with
          _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]

/-- `dispatchSyscallChecked` for a syscall whose arm and taint step are given as
`arm`, refusing in the state it was handed.  It resolves the operand once, for
the gate and the taint step alike, and hands `arm` the pre-state's taint table
and the capability found (`dispatchOperandCheckedR_eq`).  It reads the decode
only through the operand address and the required right, so the entry hands it
both straight from the register file and builds no decode record. -/
@[inline] def dispatchOperandCheckedR (capAddr : SeLe4n.CPtr) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId)
    (arm : TaintTable → Option Capability → RefusalCarrying Unit) : RefusalCarrying Unit :=
  fun st =>
    if !(st.scheduler.currentOnCore executingCore).isEqSome tid then .error (.illegalState, st)
    else
    match st.getObject? tid.toObjId with
    | some (.tcb tcb) =>
      match st.getObject? tcb.cspaceRoot with
      | some (.cnode rootCn) =>
        resolveCapAddressKUnrolled tcb.cspaceRoot capAddr rootCn.depth st
          (fun e => .error (e, st))
          (fun cnode slot =>
            arm st.declassificationTaint
              (SystemState.lookupSlotCap st { cnode := cnode, slot := slot }) st)
      | some _ => .error (.invalidCapability, st)
      | none   => .error (.objectNotFound, st)
    | some _ => .error (.illegalState, st)
    | none   => .error (.objectNotFound, st)

/-- `dispatchOperandCheckedR` is `dispatchSyscallChecked` for a syscall that
resolves its operand before its arm (`hFirst`), given an `arm` that is the
specification's arm and taint step on every capability the operand resolves
to (`hArm`). -/
theorem dispatchOperandCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId)
    (arm : TaintTable → Option Capability → RefusalCarrying Unit)
    (hFirst : syscallChecksTargetFirst decoded.syscallId = false)
    (hNotYield : decoded.syscallId ≠ .yield)
    (hArm : ∀ (st : SystemState) (tcb : TCB) (rootCn : CNode) (ref : CSpaceAddr),
      st.getObject? tid.toObjId = some (.tcb tcb) →
      st.getObject? tcb.cspaceRoot = some (.cnode rootCn) →
      resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth st = .ok ref →
      arm st.declassificationTaint (SystemState.lookupSlotCap st ref) st =
        RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore
          { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
            capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
          (syscallTaintPlan st tid decoded) st.declassificationAuditEpoch
          st.declassificationAuditLog st.declassificationTaint) st) :
    dispatchOperandCheckedR decoded.capAddr tid executingCore arm =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) := by
  funext st
  rw [dispatchSyscallChecked_eq_impl]
  simp only [dispatchOperandCheckedR, RefusalCarrying.ofKernel, dispatchSyscallCheckedImpl]
  by_cases hCur : st.scheduler.currentOnCore executingCore = some tid
  · have hIs : (st.scheduler.currentOnCore executingCore).isEqSome tid = true :=
      (threadId_isEqSome_iff _ _).2 hCur
    have hNot : ¬ (st.scheduler.currentOnCore executingCore ≠ some tid) := fun h => h hCur
    rw [if_neg (by simp only [hIs, Bool.not_true, Bool.false_eq_true, not_false_eq_true]),
      if_neg hNot, if_neg hNotYield]
    split
    · next tcb hTcb =>
      split
      · next rootCn hRoot =>
        simp only [hTcb, hRoot]
        rw [resolveCapAddressKUnrolled_eq, resolveCapAddressK_eq]
        rcases hRef : resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth st with
          e | ref
        · simp only [dispatchCheckedArmThenTaint, hFirst, Bool.false_eq_true, ↓reduceIte,
            syscallInvoke, syscallLookupCap, syscallResolveCap, hRef]
        · have h := hArm st tcb rootCn ref hTcb hRoot hRef
          simp only [RefusalCarrying.ofKernel] at h
          exact h
      · next hRoot => simp only [hTcb, hRoot]
      · next hRoot => simp only [hTcb, hRoot]
    · next hTcb => simp only [hTcb]
    · next hTcb => simp only [hTcb]
  · have hIs : (st.scheduler.currentOnCore executingCore).isEqSome tid = false := by
      cases h : (st.scheduler.currentOnCore executingCore).isEqSome tid
      · rfl
      · exact absurd ((threadId_isEqSome_iff _ _).1 h) hCur
    rw [if_pos (by simp only [hIs, Bool.not_false]), if_pos hCur]

/-- The operand a dispatch resolves is the one the taint plan reads. -/
theorem syscallOperandCap?_of_resolved (st : SystemState) (tid : SeLe4n.ThreadId)
    (capAddr : SeLe4n.CPtr) (tcb : TCB) (rootCn : CNode) (ref : CSpaceAddr)
    (hTcb : st.getObject? tid.toObjId = some (.tcb tcb))
    (hRoot : st.getObject? tcb.cspaceRoot = some (.cnode rootCn))
    (hRef : resolveCapAddress tcb.cspaceRoot capAddr rootCn.depth st = .ok ref) :
    syscallOperandCap? st tid capAddr = SystemState.lookupSlotCap st ref := by
  simp only [SystemState.getObject?_eq_getElem] at hTcb hRoot
  simp only [syscallOperandCap?, SystemState.getTcb?, SystemState.getCNode?, hTcb, hRoot, hRef]

/-- The signal's dispatch: `dispatchOperandCheckedR` with the signal's arm
(`dispatchSignalCheckedR_eq`). -/
@[inline] def dispatchSignalCheckedR (ctx : LabelingContext)
    (capAddr : SeLe4n.CPtr)
    (sigArgs : Except KernelError Architecture.SyscallArgDecode.NotificationSignalArgs)
    (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore
    (signalOperandArmThenTaintR ctx sigArgs tid executingCore
      (syscallRequiredRight .notificationSignal))

theorem dispatchSignalCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult)
    (sigArgs : Except KernelError Architecture.SyscallArgDecode.NotificationSignalArgs)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (hSig : decoded.syscallId = .notificationSignal)
    (hArgs : sigArgs = Architecture.SyscallArgDecode.decodeNotificationSignalArgs decoded) :
    dispatchSignalCheckedR ctx decoded.capAddr sigArgs tid executingCore =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) := by
  apply dispatchOperandCheckedR_eq ctx decoded tid executingCore _ (by rw [hSig]; rfl)
    (by rw [hSig]; decide)
  intro st tcb rootCn ref hTcb hRoot hRef
  rw [syscallTaintPlan_eq_signalTaintPlanOf st tid decoded hSig,
    syscallOperandCap?_of_resolved st tid _ tcb rootCn ref hTcb hRoot hRef]
  have hArm := signalOperandArmThenTaintR_eq ctx decoded tid executingCore
    { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
      capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
    st.declassificationAuditEpoch st.declassificationAuditLog st.declassificationTaint
    st ref sigArgs hSig hArgs hRef
  simp only [hSig] at hArm ⊢
  exact hArm

/-- The wait's dispatch: `dispatchOperandCheckedR` with the wait's arm
(`dispatchWaitCheckedR_eq`). -/
@[inline] def dispatchWaitCheckedR (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore
    (waitOperandArmThenTaintR ctx tid executingCore (syscallRequiredRight .notificationWait))

theorem dispatchWaitCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId)
    (hWait : decoded.syscallId = .notificationWait) :
    dispatchWaitCheckedR ctx decoded.capAddr tid executingCore =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) := by
  apply dispatchOperandCheckedR_eq ctx decoded tid executingCore _ (by rw [hWait]; rfl)
    (by rw [hWait]; decide)
  intro st tcb rootCn ref hTcb hRoot hRef
  have hArm := waitOperandArmThenTaintR_eq ctx decoded tid executingCore
    { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
      capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
    st.declassificationAuditEpoch st.declassificationAuditLog st.declassificationTaint
    st ref hWait hRef (syscallOperandCap?_of_resolved st tid _ tcb rootCn ref hTcb hRoot hRef)
  simp only [hWait] at hArm ⊢
  exact hArm

/-- WS-ZA ZA4.3: core `c`'s scheduling point as the total function it is
(`scheduleEffectiveOnCore_ne_error`); the refusal arm is unreachable. -/
@[inline] def scheduleEffectiveOnCoreTotal (st : SystemState) (c : Concurrency.CoreId) :
    SystemState :=
  match h : scheduleEffectiveOnCore st c with
  | .ok st' => st'
  | .error e => absurd h (scheduleEffectiveOnCore_ne_error st c e)

/-- WS-ZA ZA4.3: the yield on core `c`, refusing in the state it was handed
(`yieldOnCoreR_eq`).  Its refusals are the three lookups before the charge
writes (no caller, no TCB, no SchedContext), and the scheduling point after the
charge cannot refuse, so the state goes to the charge and nothing keeps it.
The bound arm reads the caller's scheduling parameters before the charge
consumes the state (D1). -/
@[inline] def yieldOnCoreR (st : SystemState) (c : Concurrency.CoreId) :
    Except (KernelError × SystemState) SystemState :=
  match st.scheduler.currentOnCore c with
  | none => .error (.illegalState, st)
  | some tid =>
    match st.getTcbWitnessed? tid with
    | none => .error (.schedulerInvariantViolation, st)
    | some ⟨tcb, hTcb⟩ =>
      match tcb.schedContextBinding with
      | .unbound => .ok (scheduleEffectiveOnCoreTotal (sliceExpireOnCore st c tid tcb hTcb) c)
      | .bound scId | .donated scId _ =>
        match st.getSchedContextWitnessed? scId with
        | some ⟨sc, hSc⟩ =>
          let params := effectiveSchedParams st tcb
          .ok (scheduleEffectiveOnCoreTotal (markKeyChangeFor
            (spendBudgetOnCore st c tid scId sc hSc sc.budgetRemaining.val) tid params) c)
        | none => .error (.missingSchedContext, st)

theorem scheduleEffectiveOnCoreTotal_eq (st : SystemState) (c : Concurrency.CoreId) :
    scheduleEffectiveOnCore st c = .ok (scheduleEffectiveOnCoreTotal st c) := by
  unfold scheduleEffectiveOnCoreTotal
  split
  · next st' h => exact h
  · next e h => exact absurd h (scheduleEffectiveOnCore_ne_error st c e)

theorem yieldOnCoreR_eq (st : SystemState) (c : Concurrency.CoreId) :
    yieldOnCoreR st c =
      match yieldOnCore st c with
      | .error e => .error (e, st)
      | .ok st' => .ok st' := by
  unfold yieldOnCoreR yieldOnCore yieldChargeOnCore
  cases st.scheduler.currentOnCore c with
  | none => rfl
  | some tid =>
    simp only []
    cases st.getTcbWitnessed? tid with
    | none => rfl
    | some p =>
      obtain ⟨tcb, hTcb⟩ := p
      simp only []
      cases tcb.schedContextBinding with
      | unbound => simp only [scheduleEffectiveOnCoreTotal_eq]
      | bound scId =>
        simp only []
        cases st.getSchedContextWitnessed? scId with
        | none => rfl
        | some q => obtain ⟨sc, hSc⟩ := q; simp only [scheduleEffectiveOnCoreTotal_eq]
      | donated scId _ =>
        simp only []
        cases st.getSchedContextWitnessed? scId with
        | none => rfl
        | some q => obtain ⟨sc, hSc⟩ := q; simp only [scheduleEffectiveOnCoreTotal_eq]

/-- `syscallEntryChecked`, refusing in the state it was handed
(`syscallEntryCheckedR_eq`).  A signal or wait whose arguments all sit in
registers is routed on the register file itself (`registerRoutedSyscall`),
before any decode record exists: the decode writes nothing and such a call
fills no TLB entry (`tlbFillIpcBufferOnCore_zero`), so its dispatch is handed
the entry's own state and refuses in it.  Every other call keeps the
specification's form. -/
@[inline] def syscallEntryCheckedR (ctx : LabelingContext)
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
        match SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall
                layout tcb.registerContext regCount with
        | .signal capAddr badge =>
          dispatchSignalCheckedR ctx capAddr (.ok { badge }) tid executingCore st
        | .wait capAddr =>
          dispatchWaitCheckedR ctx capAddr tid executingCore st
        -- WS-ZA ZA4.3: a yield reads no operand and checks nothing a write
        -- precedes, so a refusal is in the entry's own state.
        | .yield =>
          match yieldOnCoreR st executingCore with
          | .error r => .error r
          | .ok st' => .ok ((), st')
        | .viaDecode =>
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
        · next capAddr badge hSigRegs =>
          obtain ⟨decoded, hDec, hSig, hCap, hZero, h0, hBadge⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedSignal
              st tid layout tcb.registerContext regCount capAddr badge hSigRegs
          subst hCap
          have hArgs : (.ok { badge } : Except KernelError
                Architecture.SyscallArgDecode.NotificationSignalArgs) =
              Architecture.SyscallArgDecode.decodeNotificationSignalArgs decoded := by
            simp only [Architecture.SyscallArgDecode.decodeNotificationSignalArgs,
              Architecture.SyscallArgDecode.requireMsgReg, h0, ↓reduceDIte, hBadge, bind,
              Except.bind, pure, Except.pure]
          rw [dispatchSignalCheckedR_eq ctx decoded _ tid executingCore hSig hArgs]
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte,
            SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_zero]
        · next capAddr hWaitRegs =>
          obtain ⟨decoded, hDec, hWait, hCap, hZero⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedWait
              st tid layout tcb.registerContext regCount capAddr hWaitRegs
          subst hCap
          rw [dispatchWaitCheckedR_eq ctx decoded tid executingCore hWait]
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte,
            SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_zero]
        · next hYieldRegs =>
          obtain ⟨decoded, hDec, hYield, hZero⟩ :=
            SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedYield
              st tid layout tcb.registerContext regCount hYieldRegs
          simp only [RefusalCarrying.ofKernel, syscallEntryChecked, hCtx, hCur, hRegs, hDec,
            hZero, Bool.false_eq_true, ↓reduceIte,
            SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_zero,
            dispatchSyscallChecked, hYield, ne_eq, not_true_eq_false, dispatchYield,
            yieldOnCoreR_eq]
          cases yieldOnCore st executingCore <;> rfl
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
