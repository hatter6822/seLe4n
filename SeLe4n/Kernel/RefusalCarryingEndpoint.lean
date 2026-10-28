-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RefusalCarryingDispatch
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyInPlace
import SeLe4n.Kernel.IPC.CrossCore.DeliveredInPlace
import SeLe4n.Kernel.IPC.CrossCore.EndpointReceiveInPlace

/-!
# The endpoint syscalls, refusing in the state they were refused in

WS-ZA ZA4.7.  `RefusalCarryingDispatch` gives the signal, the wait and the yield
dispatches that refuse in the state they were handed; this module gives the
endpoint syscalls theirs, each proven equal to `RefusalCarrying.ofKernel` of
the specification's dispatch.  A send with no capabilities to transfer checks
everything before its first write (`endpointSendCrossCoreDispatchChecked_error_state`),
so the state goes to the send and nothing keeps it for a refusal.  A receive
that names no reply object and blocks makes its writes in place, after every
check (`receiveBlock_inPlace_eq`), so it too holds no pre-state.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open Architecture.RegisterDecode
open Architecture.SyscallArgDecode

/-- WS-ZA ZA4.7: **a frame that routes as a capability-free send or call**, read
for the sender `tid` whose saved registers `rf` are: whatever endpoint it
names, it asks to transfer no capability, and a present sender's message is the
inline words of `rf` (`sendFrame_of_routed`). -/
theorem routedSenderFrame (st : SystemState) (tid : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .send capAddr mi ∨
      registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .call capAddr mi) :
    (∀ endpointId badge grant, sendCapRequest st endpointId tid (.frame badge grant) = none) ∧
      ∀ badge grant, (st.getTcb? tid).isSome = true →
        sendPayloadMessage st tid (.frame badge grant) =
          { registers := Architecture.regMessageBody SeLe4n.arm64DefaultLayout rf mi.length,
            badge := badge } := by
  cases hT : st.getTcb? tid with
  | none =>
    refine ⟨fun endpointId _ _ => ?_, fun _ _ h => by cases h⟩
    unfold sendCapRequest
    split
    · rfl
    · rw [hT]
  | some tcb =>
    have hRf := hFrame tcb hT
    subst hRf
    exact ⟨fun endpointId badge grant =>
        (sendFrame_of_routed st tid tcb hT capAddr mi hR endpointId badge grant).2,
      fun badge grant _ => (sendFrame_of_routed st tid tcb hT capAddr mi hR tid.toObjId badge
        grant).1⟩

/-- The checked send arm (`dispatchWithCapChecked`'s `.send` case) through the
specification's send, refusing in the state it was handed
(`endpointSendCheckedArmGeneralR_eq`).  As the specification's, it is handed
only the capability's badge and grant right: the words are read from the
sender's frame. -/
def endpointSendCheckedArmGeneralR (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (cap : Capability) : RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object epId =>
        let woken? := (st.getEndpoint? epId).bind (·.receiveQ.head)
        match endpointSendCrossCoreDispatchChecked ctx epId tid
            (.frame cap.badge (cap.rights.mem .grant)) (SeLe4n.Slot.ofNat 0)
            executingCore st with
        | (st', .ok (summary, _)) =>
            .ok ((), Architecture.stageWokenDelivery (clearWokenReceiverStashPure woken? st')
              woken? summary.installedCount)
        | (st', .error e) => .error (e, st')
    | _ => .error (.invalidCapability, st)

/-- The general send arm is the specification's for a sender whose frame asks
to transfer no capability: a refusal then precedes every write
(`endpointSendCrossCoreDispatchChecked_error_state`). -/
theorem endpointSendCheckedArmGeneralR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (st : SystemState)
    (hSend : decoded.syscallId = .send)
    (hSlot : decoded.capRecvSlot = SeLe4n.Slot.ofNat 0)
    (hReq : ∀ endpointId badge grant,
      sendCapRequest st endpointId tid (.frame badge grant) = none) :
    endpointSendCheckedArmGeneralR ctx tid executingCore cap st =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap)
        st := by
  simp only [endpointSendCheckedArmGeneralR, RefusalCarrying.ofKernel, dispatchWithCapChecked,
    dispatchCapabilityOnly, hSend, hSlot]
  cases cap.target with
  | object epId =>
    simp only []
    rcases hRun : endpointSendCrossCoreDispatchChecked ctx epId tid
        (.frame cap.badge (cap.rights.mem .grant)) (SeLe4n.Slot.ofNat 0) executingCore st with
      ⟨st', _ | ⟨summary, sgi⟩⟩
    · have hst := endpointSendCrossCoreDispatchChecked_error_state ctx epId tid _
        (SeLe4n.Slot.ofNat 0) executingCore st _ (hReq _ _ _) (by rw [hRun])
      rw [hRun] at hst
      simp only at hst
      rw [hst]
    · simp only [clearWokenReceiverStash_eq_pure]
  | _ => rfl

/-- WS-ZA ZA4.7: **a checked send to a waiting receiver, in place**: for a
send whose message is `msg` and which transfers no capability, with the sender
present and the rendezvous's writes in their slots (`sendWakesInPlace`), the
checked send is the in-place rendezvous and the receiver's wake. -/
theorem sendDispatchChecked_inPlace (ctx : LabelingContext) (st : SystemState)
    (endpointId : SeLe4n.ObjId) (ep : Endpoint) (sender r : SeLe4n.ThreadId) (rt : TCB)
    (payload : SendPayload) (msg : IpcMessage) (executingCore : Concurrency.CoreId)
    (hM : sendPayloadMessage st sender payload = msg)
    (hReq : sendCapRequest st endpointId sender payload = none)
    (hE : st.getEndpoint? endpointId = some ep) (hH : ep.receiveQ.head = some r)
    (hT : st.getTcb? r = some rt) (hS : (st.getTcb? sender).isSome = true)
    (hW : sendWakesInPlace st endpointId r rt.queueNext = true)
    (hFlow : endpointFlowGate ctx endpointId (ctx.threadLabelOf sender)
      (ctx.endpointLabelOf endpointId) = true) :
    endpointSendCrossCoreDispatchChecked ctx endpointId sender payload
        (SeLe4n.Slot.ofNat 0) executingCore st =
      ((wakeThread (storeSendRendezvous st endpointId r rt.queueNext msg) r executingCore).1,
        .ok ({ results := #[] },
          (wakeThread (storeSendRendezvous st endpointId r rt.queueNext msg) r
            executingCore).2)) := by
  obtain ⟨sTcb, hSTcb⟩ := Option.isSome_iff_exists.mp hS
  unfold endpointSendCrossCoreDispatchChecked
  rw [if_pos hFlow, endpointSendDualWithCapsOnCore_no_caps _ _ _ _ _ _ hReq,
    endpointSendDualOnCore_eq_impl]
  unfold endpointSendDualOnCoreImpl
  simp only [hE, hH, hSTcb, hT, hW, hM, ↓reduceIte]
  rfl

/-- Dropping the stash of a thread whose last write left none drops nothing. -/
theorem clearWokenReceiverStashPure_mapTcbInPlace (Y : SystemState) (r : SeLe4n.ThreadId)
    (g : TCB → TCB) (h : ∀ t, (g t).pendingReceiveReply = none) :
    clearWokenReceiverStashPure (some r) (Y.mapTcbInPlace r g) = Y.mapTcbInPlace r g := by
  unfold clearWokenReceiverStashPure
  simp only [SystemState.getTcb?_mapTcbInPlace, ↓reduceIte]
  cases Y.getTcb? r with
  | none => rfl
  | some t => simp only [Option.map_some, h]

/-- WS-ZA ZA4.7: **the staged send rendezvous is the delivered one** for a
message of at most four words read in the sender's registers. -/
theorem sendRendezvous_eq_delivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (r : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (core : Concurrency.CoreId)
    (hNo : st.objects.noResizeDue) (hSz : Architecture.regMessageLength layout len ≤ 4) :
    Architecture.stageWokenDelivery
        (clearWokenReceiverStashPure (some r)
          (wakeThread (storeSendRendezvous st endpointId r next
            { registers := Architecture.regMessageBody layout rf len,
              badge := SeLe4n.Badge.opt badgeWord badged }) r core).1)
        (some r) 0 =
      performSendDelivered st endpointId r (ThreadId.optCode next) layout rf len badgeWord badged
        core := by
  have hNo0 := storeSendRendezvousWith_noResizeDue st endpointId r next ipcReadyTcb hNo
  unfold performSendDelivered storeSendRendezvousReady
  rw [Architecture.regMessageFrameW_eq, SeLe4n.ThreadId.ofOptCode_optCode]
  rw [storeSendRendezvous_eq_with, receiveCompleteTcb_eq_slots, receiveReadyTcb_eq_slots,
    storeSendRendezvousWith_comp _ _ _ _ _ _ hNo, storeSendRendezvousWith_comp _ _ _ _ _ _ hNo]
  simp only [receiveCompleteSlots, clearMessageSlots]
  rw [wakeThread_msg _ _ _ _ _ _ _ hNo0, wakeThread_msg _ _ _ _ _ _ _ hNo0]
  dsimp only
  have hD : ∀ M : IpcMessage,
      TCB.withMessageSlots id (fun _ => some M) (fun _ : Nat => 0) =
        holdMessage M ∘ TCB.withMessageSlots id (fun _ => none) (fun _ => 0) := fun _ => rfl
  rw [clearWokenReceiverStashPure_mapTcbInPlace _ _ _ (fun _ => rfl),
    hD, ← SystemState.mapTcbInPlace_mapTcbInPlace,
    Architecture.stageWokenDelivery_some,
    stageDeliveredMessage_holdMessage _ _ _
      ((SystemState.mapTcbInPlace_noResizeDue _ _ _).mpr (wakeThread_noResizeDue _ _ _ hNo0))
      (by rw [Architecture.regMessageBody_size]; exact hSz),
    Architecture.returnFrameOfMessage_regMessageBody]
  rfl

/-- WS-ZA ZA4.7: a send blocks, and writes only its slots: the sender may be
enqueued (`enqueueAdmits`) and every write stays in place
(`enqueuesInPlace`), the send queue's tail read as its code. -/
@[inline] def sendBlocksFast (st : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (tailCode : Nat) : Bool :=
  match st.getTcb? sender with
  | some t => enqueueAdmits t && enqueuesInPlaceCode st endpointId sender tailCode
  | none => false

/-- WS-ZA ZA4.7: the checked send arm (`dispatchWithCapChecked`'s `.send` case)
for a sender whose saved registers `rf` hold a message of `len` words and no
capability addresses, refusing in the state it was handed
(`endpointSendCheckedArmR_eq`).  A send of at most four words to a waiting
receiver whose checks all pass before any write (`sendWakesInPlace`) wakes the
receiver in place and writes the words into its saved registers
(`performSendDelivered`, `sendRendezvous_eq_delivered`); a send with no
receiver waiting whose checks all pass (`sendBlocksFast`) blocks in place,
its words left in its registers (`sendBlock_inPlace_eq`); any other send takes
the general arm. -/
@[inline] def endpointSendCheckedArmR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability) :
    RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object epId =>
        match st.getEndpoint? epId with
        | some ep =>
            match ep.receiveQ.head with
            | some r =>
                match st.getTcb? r with
                | some rt =>
                    if decide (Architecture.regMessageLength layout len ≤ 4) &&
                        (st.getTcb? tid).isSome &&
                        endpointFlowGate ctx epId (ctx.threadLabelOf tid)
                          (ctx.endpointLabelOf epId) &&
                        sendWakesInPlace st epId r rt.queueNext then
                      .ok ((), performSendDelivered st epId r rt.queueNextCode layout rf len
                        cap.badgeWord cap.badged executingCore)
                    else endpointSendCheckedArmGeneralR ctx tid executingCore cap st
                | none => endpointSendCheckedArmGeneralR ctx tid executingCore cap st
            | none =>
                if sendBlocksFast st epId tid ep.sendTailCode &&
                    endpointFlowGate ctx epId (ctx.threadLabelOf tid)
                      (ctx.endpointLabelOf epId) then
                  .ok ((), recordSendCapWords (removeRunnableOnCore
                    (storeSendBlock st epId tid ep.sendTailCode) tid executingCore) tid
                    cap.badgeWord cap.badged (cap.rights.mem .grant))
                else endpointSendCheckedArmGeneralR ctx tid executingCore cap st
        | none => endpointSendCheckedArmGeneralR ctx tid executingCore cap st
    | _ => .error (.invalidCapability, st)

/-- The fast send arm is the general one for a sender whose saved registers
`rf` route as a capability-free send or call: the words it writes in place are
the words the specification's send reads from that frame
(`routedSenderFrame`). -/
theorem endpointSendCheckedArmR_eq_general (ctx : LabelingContext)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability)
    (st : SystemState)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .send capAddr mi ∨
      registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .call capAddr mi) :
    endpointSendCheckedArmR ctx SeLe4n.arm64DefaultLayout rf mi.length tid executingCore cap st =
      endpointSendCheckedArmGeneralR ctx tid executingCore cap st := by
  obtain ⟨hReq, hMsg⟩ := routedSenderFrame st tid rf capAddr mi hFrame hR
  unfold endpointSendCheckedArmR
  split
  · next epId hTgt =>
    split
    · next ep hE =>
      split
      · next r hH =>
        split
        · next rt hT =>
          split
          · next hG =>
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hG
            obtain ⟨⟨⟨hSz, hS⟩, hFlow⟩, hW⟩ := hG
            have hNo : st.objects.noResizeDue := by
              simp only [sendWakesInPlace, Bool.and_eq_true] at hW
              exact RobinHood.RHTable.noResizeDue_of_findsInPlace hW.1.1.1.2
            unfold endpointSendCheckedArmGeneralR
            simp only [hTgt, hE, Option.bind_some, hH]
            rw [sendDispatchChecked_inPlace ctx st epId ep tid r rt _ _ executingCore
              (hMsg _ _ hS) (hReq _ _ _) hE hH hT hS hW hFlow]
            simp only []
            rw [← TCB.optCode_queueNext,
              ← sendRendezvous_eq_delivered _ _ _ _ _ _ _ _ _ _ hNo hSz]
            rfl
          · rfl
        · rfl
      · next hH =>
        split
        · next hG =>
          simp only [Bool.and_eq_true] at hG
          obtain ⟨hB, hFlow⟩ := hG
          unfold sendBlocksFast at hB
          split at hB
          · next t hT =>
            simp only [Bool.and_eq_true] at hB
            obtain ⟨hA, hIP⟩ := hB
            rw [enqueuesInPlaceCode_eq,
              show SeLe4n.ThreadId.ofOptCode ep.sendTailCode = ep.sendQ.tail from rfl] at hIP
            unfold endpointSendCheckedArmGeneralR
            simp only [hTgt, hE, Option.bind_some, hH]
            unfold endpointSendCrossCoreDispatchChecked
            rw [if_pos hFlow,
              endpointSendDualWithCapsOnCore_no_caps _ _ _ _ _ _ (hReq _ _ _),
              sendBlock_inPlace_eq _ _ _ _ _ ep t
                ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hE) hH
                ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hA hIP,
              recordSendCapWords_eq]
            rfl
          · cases hB
        · rfl
    · rfl
  · next hTgt =>
    unfold endpointSendCheckedArmGeneralR
    split
    · next epId h => exact absurd h (hTgt epId)
    · rfl

/-- The fast send arm is the specification's for a sender whose saved
registers `rf` route as a capability-free send of `mi.length` words. -/
theorem endpointSendCheckedArmR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo) (st : SystemState)
    (hSend : decoded.syscallId = .send)
    (hSlot : decoded.capRecvSlot = SeLe4n.Slot.ofNat 0)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .send capAddr mi) :
    endpointSendCheckedArmR ctx SeLe4n.arm64DefaultLayout rf mi.length tid executingCore cap st =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap)
        st := by
  rw [endpointSendCheckedArmR_eq_general ctx rf capAddr mi tid executingCore cap st hFrame
    (.inl hR)]
  exact endpointSendCheckedArmGeneralR_eq ctx decoded tid executingCore gate cap st hSend hSlot
    (routedSenderFrame st tid rf capAddr mi hFrame (.inl hR)).1

/-- The receiver a send's content reaches, read from the pre-state before the
arm: the head of the receive queue of the endpoint its capability names
(`senderTaintEdges`), as its code (`SeLe4n.ThreadId.optCode`), so the value
held across the arm is a word, not an `Option` cell. -/
@[inline] def sendTaintHeadCode (st : SystemState) (cap : Capability) : Nat :=
  match cap.target with
  | .object epId =>
      match st.getEndpoint? epId with
      | some ep => ep.recvHeadCode
      | none => 0
  | _ => 0

/-- The send's taint step, without the plan: the sender's pre-state taint joins
the receiver's (`sendTaintStep_eq`).  It builds no edge list and no plan
record. -/
@[inline] def sendTaintStep (headCode : Nat) (tid : SeLe4n.ThreadId)
    (preTaint : TaintTable) (post : SystemState) : SystemState :=
  match headCode with
  | r + 1 =>
      let receiver : SeLe4n.ThreadId := ⟨r⟩
      { post with declassificationTaint :=
          post.declassificationTaint.joinAt receiver.toObjId (preTaint tid.toObjId) }
  | 0 => post

theorem sendTaintStep_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult)
    (hSend : decoded.syscallId = .send ∨ decoded.syscallId = .call)
    (preEpoch : Nat) (preLength : Nat) (preTaint : TaintTable)
    (post : SystemState) :
    applySyscallTaintAfter (syscallTaintPlan st tid decoded) preEpoch preLength preTaint post =
      (match syscallOperandCap? st tid decoded.capAddr with
        | some cap => sendTaintStep (sendTaintHeadCode st cap) tid preTaint post
        | none => post) := by
  rcases hSend with hSend | hSend <;>
  simp only [syscallTaintPlan, contentFlowClass, hSend, contentFlowEdges, contentFlowClears,
    contentFlowBypassed] <;>
  rcases syscallOperandCap? st tid decoded.capAddr with _ | ⟨target, _, _⟩ <;>
  first
  | simp [applySyscallTaintAfter, syscallRecordsDeclassification,
      applyOrigination, applyTaintClears, applyTaintFlow]; done
  | cases target with
    | object epId =>
      simp only [sendTaintHeadCode, senderTaintEdges]
      cases st.getEndpoint? epId with
      | none =>
        simp [sendTaintStep, applySyscallTaintAfter, syscallRecordsDeclassification,
          applyOrigination, applyTaintClears, applyTaintFlow]
      | some ep =>
        simp only [Option.bind_some, ← Endpoint.ofOptCode_recvHeadCode]
        cases ep.recvHeadCode <;>
          simp [sendTaintStep, SeLe4n.ThreadId.ofOptCode, applySyscallTaintAfter,
            syscallRecordsDeclassification, applyOrigination, applyTaintClears, applyTaintFlow]
    | _ =>
      simp [sendTaintHeadCode, sendTaintStep, applySyscallTaintAfter,
        syscallRecordsDeclassification, applyOrigination, applyTaintClears, applyTaintFlow]

/-- The send's slot check, gate, arm and taint step on the capability its
operand resolved to, every refusal carrying the state it was handed
(`sendOperandArmThenTaintR_eq`). -/
@[inline] def sendOperandArmThenTaintR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (requiredRight : AccessRight)
    (preTaint : TaintTable) (operand : Option Capability) : RefusalCarrying Unit :=
  fun st =>
    match operand with
    | none => .error (.invalidCapability, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedIdleObject cap then .error (.invalidCapability, st)
        else if cap.hasRight requiredRight then
          let headCode := sendTaintHeadCode st cap
          match endpointSendCheckedArmR ctx layout rf len tid executingCore cap st with
          | .error refusal => .error refusal
          | .ok ((), stPost) => .ok ((), sendTaintStep headCode tid preTaint stPost)
        else .error (.illegalAuthority, st)

theorem sendOperandArmThenTaintR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (preEpoch : Nat) (preLength : Nat)
    (preTaint : TaintTable) (st : SystemState) (ref : CSpaceAddr)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hSend : decoded.syscallId = .send)
    (hSlot : decoded.capRecvSlot = SeLe4n.Slot.ofNat 0)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .send capAddr mi)
    (hRef : resolveCapAddress gate.cspaceRoot gate.capAddr gate.capDepth st = .ok ref)
    (hOperand : syscallOperandCap? st tid decoded.capAddr = SystemState.lookupSlotCap st ref) :
    sendOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout rf mi.length tid executingCore
        gate.requiredRight
        preTaint (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore gate
        (syscallTaintPlan st tid decoded) preEpoch preLength preTaint) st := by
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel,
    hSend, syscallChecksTargetFirst, Bool.false_eq_true, ↓reduceIte, syscallInvoke,
    syscallLookupCap, syscallResolveCap, hRef]
  simp only [sendTaintStep_eq st tid decoded (.inl hSend), hOperand]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [sendOperandArmThenTaintR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedIdleObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hRight : cap.hasRight gate.requiredRight = true
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]
        rw [endpointSendCheckedArmR_eq ctx decoded tid executingCore gate cap rf capAddr mi st
          hSend hSlot hFrame hR]
        simp only [RefusalCarrying.ofKernel]
        rcases dispatchWithCapChecked ctx decoded tid executingCore gate cap st with
          _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]

/-- The send's dispatch for a sender whose saved registers hold its message and
no capability addresses: `dispatchOperandCheckedR` with the send's arm
(`dispatchSendCheckedR_eq`). -/
@[inline] def dispatchSendCheckedR (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore
    (sendOperandArmThenTaintR ctx layout rf len tid executingCore (syscallRequiredRight .send))

theorem dispatchSendCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (st : SystemState)
    (hSend : decoded.syscallId = .send)
    (hSlot : decoded.capRecvSlot = SeLe4n.Slot.ofNat 0)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .send capAddr mi) :
    dispatchSendCheckedR ctx decoded.capAddr SeLe4n.arm64DefaultLayout rf mi.length tid
        executingCore st =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) st := by
  apply dispatchOperandCheckedR_eq_at ctx decoded tid executingCore _ (by rw [hSend]; rfl)
    (by rw [hSend]; decide) st
  intro tcb rootCn ref hTcb hRoot hRef
  have hArm := sendOperandArmThenTaintR_eq ctx decoded tid executingCore
    { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
      capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
    st.declassificationAuditEpoch st.declassificationAudit.length st.declassificationTaint
    st ref rf capAddr mi hSend hSlot hFrame hR hRef
    (syscallOperandCap?_of_resolved st tid _ tcb rootCn ref hTcb hRoot hRef)
  simp only [hSend] at hArm ⊢
  exact hArm

/-- The checked call arm (`dispatchWithCapChecked`'s `.call` case) through the
specification's dispatch, refusing in the state it was handed
(`endpointCallCheckedArmGeneralR_eq`).  As the specification's, it is handed
only the capability's badge and grant right: the words are read from the
caller's frame. -/
def endpointCallCheckedArmGeneralR (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (cap : Capability) : RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object epId =>
        let woken? := (st.getEndpoint? epId).bind (·.receiveQ.head)
        match endpointCallCrossCoreDispatchChecked ctx epId tid
            (.frame cap.badge (cap.rights.mem .grant)) (SeLe4n.Slot.ofNat 0)
            executingCore st with
        | (st', .ok (summary, _)) =>
            .ok ((), Architecture.stageWokenDelivery st' woken? summary.installedCount)
        | (_, .error e) => .error (e, st)
    | _ => .error (.invalidCapability, st)

theorem endpointCallCheckedArmGeneralR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (hCall : decoded.syscallId = .call)
    (hSlot : decoded.capRecvSlot = SeLe4n.Slot.ofNat 0) :
    endpointCallCheckedArmGeneralR ctx tid executingCore cap =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap) := by
  funext st
  simp only [endpointCallCheckedArmGeneralR, RefusalCarrying.ofKernel, dispatchWithCapChecked,
    dispatchCapabilityOnly, hCall, hSlot]
  cases cap.target with
  | object epId =>
    simp only []
    rcases endpointCallCrossCoreDispatchChecked ctx epId tid
        (.frame cap.badge (cap.rights.mem .grant)) (SeLe4n.Slot.ofNat 0) executingCore st with
      ⟨st', _ | ⟨summary, sgi⟩⟩ <;> rfl
  | _ => rfl

/-- The checked call arm (`dispatchWithCapChecked`'s `.call` case) for a
caller whose saved registers `rf` hold a message of `len` words and no
capability addresses, refusing in the state it was handed
(`endpointCallCheckedArmR_eq`).  WS-ZA ZA4.7: a rendezvous whose checks all
pass before any write (`callWakesInPlace`, the seL4 decode/perform split) writes
in place on a state nothing else holds (`performCallRendezvous`,
`callDispatchChecked_inPlace`); any other call takes the general arm. -/
@[inline] def endpointCallCheckedArmR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability) :
    RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object epId =>
        match st.getEndpoint? epId with
        | some ep =>
            match ep.receiveQ.head with
            | some r =>
                match st.getTcb? r with
                | some rt =>
                    match rt.pendingReceiveReply with
                    | some rid =>
                        if (st.getTcb? tid).isSome &&
                            endpointFlowGate ctx epId (ctx.threadLabelOf tid)
                              (ctx.endpointLabelOf epId) &&
                            callWakesInPlace st epId tid r rt rid then
                          .ok ((), callRendezvousDelivered st epId tid r rt.queueNextCode rid
                            layout rf len
                            cap.badgeWord cap.badged executingCore)
                        else endpointCallCheckedArmGeneralR ctx tid executingCore cap st
                    | none => endpointCallCheckedArmGeneralR ctx tid executingCore cap st
                | none => endpointCallCheckedArmGeneralR ctx tid executingCore cap st
            | none => endpointCallCheckedArmGeneralR ctx tid executingCore cap st
        | none => endpointCallCheckedArmGeneralR ctx tid executingCore cap st
    | _ => .error (.invalidCapability, st)

/-- The fast call arm is the general one for a caller whose saved registers
`rf` route as a capability-free call: the words it writes in place are the
words the specification's call reads from that frame (`routedSenderFrame`). -/
theorem endpointCallCheckedArmR_eq_general (ctx : LabelingContext)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability)
    (st : SystemState)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .call capAddr mi) :
    endpointCallCheckedArmR ctx SeLe4n.arm64DefaultLayout rf mi.length tid executingCore cap st =
      endpointCallCheckedArmGeneralR ctx tid executingCore cap st := by
  obtain ⟨hReq, hMsg⟩ := routedSenderFrame st tid rf capAddr mi hFrame (.inr hR)
  unfold endpointCallCheckedArmR
  split
  · next epId hTgt =>
    split
    · next ep hE =>
      split
      · next r hH =>
        split
        · next rt hT =>
          split
          · next rid hRid =>
            split
            · next hG =>
              simp only [Bool.and_eq_true] at hG
              obtain ⟨⟨hS, hFlow⟩, hW⟩ := hG
              obtain ⟨sgi, hD⟩ := callDispatchChecked_inPlace ctx st epId ep tid r rt rid
                (.frame cap.badge (cap.rights.mem .grant)) _ (SeLe4n.Slot.ofNat 0) executingCore
                (hMsg cap.badge (cap.rights.mem .grant) hS) (hReq epId _ _)
                ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hE) hH
                ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hRid hW hFlow
              rw [callRendezvousDelivered_eq _ _ _ _ _ _ _ _ _ _ _ _ hW]
              simp only [endpointCallCheckedArmGeneralR, hTgt, hE, Option.bind_some, hH, hD]
              rfl
            · rfl
          · rfl
        · rfl
      · rfl
    · rfl
  · next hTgt =>
    unfold endpointCallCheckedArmGeneralR
    split
    · next epId h => exact absurd h (hTgt epId)
    · rfl

/-- The fast call arm is the specification's for a caller whose saved
registers `rf` route as a capability-free call of `mi.length` words. -/
theorem endpointCallCheckedArmR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo) (st : SystemState)
    (hCall : decoded.syscallId = .call)
    (hSlot : decoded.capRecvSlot = SeLe4n.Slot.ofNat 0)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .call capAddr mi) :
    endpointCallCheckedArmR ctx SeLe4n.arm64DefaultLayout rf mi.length tid executingCore cap st =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap)
        st := by
  rw [endpointCallCheckedArmR_eq_general ctx rf capAddr mi tid executingCore cap st hFrame hR,
    endpointCallCheckedArmGeneralR_eq ctx decoded tid executingCore gate cap hCall hSlot]

/-- The call's slot check, gate, arm and taint step on the capability its
operand resolved to; a call moves content as a send does (`sendTaintStep`).
Every refusal carries the state it was handed (`callOperandArmThenTaintR_eq`). -/
@[inline] def callOperandArmThenTaintR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (requiredRight : AccessRight)
    (preTaint : TaintTable) (operand : Option Capability) : RefusalCarrying Unit :=
  fun st =>
    match operand with
    | none => .error (.invalidCapability, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedIdleObject cap then .error (.invalidCapability, st)
        else if cap.hasRight requiredRight then
          let headCode := sendTaintHeadCode st cap
          match endpointCallCheckedArmR ctx layout rf len tid executingCore cap st with
          | .error refusal => .error refusal
          | .ok ((), stPost) => .ok ((), sendTaintStep headCode tid preTaint stPost)
        else .error (.illegalAuthority, st)

theorem callOperandArmThenTaintR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (preEpoch : Nat) (preLength : Nat)
    (preTaint : TaintTable) (st : SystemState) (ref : CSpaceAddr)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hCall : decoded.syscallId = .call)
    (hSlot : decoded.capRecvSlot = SeLe4n.Slot.ofNat 0)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .call capAddr mi)
    (hRef : resolveCapAddress gate.cspaceRoot gate.capAddr gate.capDepth st = .ok ref)
    (hOperand : syscallOperandCap? st tid decoded.capAddr = SystemState.lookupSlotCap st ref) :
    callOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout rf mi.length tid executingCore
        gate.requiredRight
        preTaint (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore gate
        (syscallTaintPlan st tid decoded) preEpoch preLength preTaint) st := by
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel,
    hCall, syscallChecksTargetFirst, Bool.false_eq_true, ↓reduceIte, syscallInvoke,
    syscallLookupCap, syscallResolveCap, hRef]
  simp only [sendTaintStep_eq st tid decoded (.inr hCall), hOperand]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [callOperandArmThenTaintR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedIdleObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hRight : cap.hasRight gate.requiredRight = true
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]
        rw [endpointCallCheckedArmR_eq ctx decoded tid executingCore gate cap rf capAddr mi st
          hCall hSlot hFrame hR]
        simp only [RefusalCarrying.ofKernel]
        rcases dispatchWithCapChecked ctx decoded tid executingCore gate cap st with
          _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]

/-- The call's dispatch for a caller whose saved registers hold its message
and no capability addresses: `dispatchOperandCheckedR` with the call's arm
(`dispatchCallCheckedR_eq`). -/
@[inline] def dispatchCallCheckedR (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore
    (callOperandArmThenTaintR ctx layout rf len tid executingCore (syscallRequiredRight .call))

theorem dispatchCallCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (st : SystemState)
    (hCall : decoded.syscallId = .call)
    (hSlot : decoded.capRecvSlot = SeLe4n.Slot.ofNat 0)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .call capAddr mi) :
    dispatchCallCheckedR ctx decoded.capAddr SeLe4n.arm64DefaultLayout rf mi.length tid
        executingCore st =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) st := by
  apply dispatchOperandCheckedR_eq_at ctx decoded tid executingCore _ (by rw [hCall]; rfl)
    (by rw [hCall]; decide) st
  intro tcb rootCn ref hTcb hRoot hRef
  have hArm := callOperandArmThenTaintR_eq ctx decoded tid executingCore
    { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
      capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
    st.declassificationAuditEpoch st.declassificationAudit.length st.declassificationTaint
    st ref rf capAddr mi hCall hSlot hFrame hR hRef
    (syscallOperandCap?_of_resolved st tid _ tcb rootCn ref hTcb hRoot hRef)
  simp only [hCall] at hArm ⊢
  exact hArm

/-- WS-ZA ZA4.7: the caller a reply's content reaches, read from the pre-state
before the arm: the caller the reply object its capability names records
(`replyTaintEdges`). -/
@[inline] def replyTaintCaller? (st : SystemState) (cap : Capability) :
    Option SeLe4n.ThreadId :=
  match cap.target with
  | .replyCap rid => (st.getReply? rid).bind (·.caller)
  | _ => none

/-- The reply's taint step is the send's, toward the answered caller. -/
theorem replyTaintStep_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (hReply : decoded.syscallId = .reply)
    (preEpoch : Nat) (preLength : Nat) (preTaint : TaintTable)
    (post : SystemState) :
    applySyscallTaintAfter (syscallTaintPlan st tid decoded) preEpoch preLength preTaint post =
      (match syscallOperandCap? st tid decoded.capAddr with
        | some cap => sendTaintStep (ThreadId.optCode (replyTaintCaller? st cap)) tid preTaint post
        | none => post) := by
  simp only [syscallTaintPlan, contentFlowClass, hReply, contentFlowEdges, contentFlowClears,
    contentFlowBypassed]
  rcases syscallOperandCap? st tid decoded.capAddr with _ | ⟨target, _, _⟩
  · simp [applySyscallTaintAfter, syscallRecordsDeclassification,
      applyOrigination, applyTaintClears, applyTaintFlow]
  · cases target with
    | replyCap rid =>
      simp only [replyTaintCaller?, replyTaintEdges]
      cases (st.getReply? rid).bind (·.caller) <;>
        simp [sendTaintStep, ThreadId.optCode, applySyscallTaintAfter, syscallRecordsDeclassification,
          applyOrigination, applyTaintClears, applyTaintFlow]
    | _ =>
      simp [replyTaintCaller?, sendTaintStep, applySyscallTaintAfter,
        syscallRecordsDeclassification, applyOrigination, applyTaintClears, applyTaintFlow]

/-- WS-ZA ZA4.7: the checked reply arm (`dispatchWithCapChecked`'s `.reply`
case), through the specification's transfer, refusing in the state it was
handed (`endpointReplyCheckedArmGeneralR_eq`). -/
def endpointReplyCheckedArmGeneralR (ctx : LabelingContext) (mi : MessageInfo)
    (regs : Array SeLe4n.RegValue) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (cap : Capability) : RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .replyCap rid =>
        match replyAnsweredCaller? st rid with
        | none => .error (.replyCapInvalid, st)
        | some callerTid =>
            if securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf callerTid) then
              match replyTransferOnCoreChecked ctx tid callerTid mi regs
                  { registers := extractMessageRegisters regs mi,
                    badge := cap.badge } executingCore st with
              | .ok ((), st') => .ok ((), st')
              | .error e => .error (e, st)
            else .error (.replyCapInvalid, st)
    | _ => .error (.invalidCapability, st)

theorem endpointReplyCheckedArmGeneralR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (hReply : decoded.syscallId = .reply) :
    endpointReplyCheckedArmGeneralR ctx decoded.msgInfo decoded.msgRegs tid executingCore cap =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap) := by
  funext st
  simp only [endpointReplyCheckedArmGeneralR, RefusalCarrying.ofKernel, dispatchWithCapChecked,
    dispatchCapabilityOnly, hReply]
  cases cap.target with
  | replyCap rid =>
    simp only []
    cases replyAnsweredCaller? st rid with
    | none => rfl
    | some callerTid =>
      simp only []
      split
      · rcases replyTransferOnCoreChecked ctx tid callerTid decoded.msgInfo decoded.msgRegs
          { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo,
            badge := cap.badge } executingCore st with _ | ⟨⟨⟩, st'⟩ <;> rfl
      · rfl
  | _ => rfl

/-- The general reply arm on a message read in registers: the registers are read
where this is called, so only the general arm reads them. -/
@[inline] def endpointReplyCheckedArmRegsR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability) :
    RefusalCarrying Unit :=
  endpointReplyCheckedArmGeneralR ctx
      { length := len, extraCaps := extraCaps, label := label }
      (Architecture.regMessageRegs layout rf) tid
    executingCore cap

/-- WS-ZA ZA4.7: the checked reply arm (`dispatchWithCapChecked`'s `.reply`
case), refusing in the state it was handed (`endpointReplyCheckedArmR_eq`).  A
reply to an unfaulted caller blocked on it whose checks all pass before any
write (`replyWakesInPlace`) writes in place on a state nothing else holds
(`performReplyRendezvous`, `replyTransferChecked_inPlace`); any other reply
takes the general arm. -/
@[inline] def endpointReplyCheckedArmR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (cap : Capability) : RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .replyCap rid0 =>
        match st.getReply? rid0 with
        | some rp0 =>
            match rp0.caller with
            | some c =>
                match st.getTcb? c with
                | some ct =>
                    match ct.ipcState with
                    | .blockedOnReply _ (some server) =>
                        match ct.replyObject with
                        | some rid =>
                            if !decide (Architecture.regMessageLength layout len >
                                  maxMessageRegisters) &&
                                securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf c) &&
                                !server.isReserved && replyWakesInPlace st c ct rid then
                              .ok ((), replyRendezvousDelivered st c server rid
                                layout rf len cap.badgeWord cap.badged executingCore)
                            else endpointReplyCheckedArmRegsR ctx layout rf len extraCaps label
                                tid executingCore cap st
                        | none => endpointReplyCheckedArmRegsR ctx layout rf len extraCaps label
                            tid executingCore cap st
                    | _ =>
                        endpointReplyCheckedArmRegsR ctx layout rf len extraCaps label
                          tid executingCore cap st
                | none =>
                    endpointReplyCheckedArmRegsR ctx layout rf len extraCaps label
                      tid executingCore cap st
            | none =>
                endpointReplyCheckedArmRegsR ctx layout rf len extraCaps label
                  tid executingCore cap st
        | none =>
            endpointReplyCheckedArmRegsR ctx layout rf len extraCaps label
              tid executingCore cap st
    | _ => .error (.invalidCapability, st)

theorem endpointReplyCheckedArmR_eq_general (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability) :
    endpointReplyCheckedArmR ctx layout rf len extraCaps label tid executingCore cap =
      endpointReplyCheckedArmGeneralR ctx
      { length := len, extraCaps := extraCaps, label := label }
      (Architecture.regMessageRegs layout rf) tid
        executingCore cap := by
  funext st
  unfold endpointReplyCheckedArmR
  split
  · next rid0 hTgt =>
    split
    · next rp0 hR0 =>
      split
      · next c hC =>
        split
        · next ct hT =>
          split
          · next ep server hIpc =>
            split
            · next rid hRO =>
              split
              · next hG =>
                simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hG
                obtain ⟨⟨⟨hSz, hFlow⟩, hSRes⟩, hW⟩ := hG
                have hAns : replyAnsweredCaller? st rid0 = some c := by
                  rw [replyAnsweredCaller?_of_getReply st rid0 rp0 hR0, hC]
                rw [replyRendezvousDelivered_eq _ _ _ _ _ _ _ _ _ _ _ hW]
                simp only [endpointReplyCheckedArmGeneralR, hTgt, hAns, hFlow, ↓reduceIte]
                rw [replyTransferChecked_inPlace ctx st tid c server ct ep rid
                  { length := len, extraCaps := extraCaps, label := label }
                  (Architecture.regMessageRegs layout rf) _ executingCore
                  (by rw [← Architecture.regMessageBody_size layout rf len] at hSz; exact hSz)
                  ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hIpc hRO hSRes hW hFlow]
                rfl
              · rfl
            · rfl
          · rfl
        · rfl
      · rfl
    · rfl
  · next hTgt =>
    unfold endpointReplyCheckedArmGeneralR
    split
    · next rid h => exact absurd h (hTgt rid)
    · rfl

theorem endpointReplyCheckedArmR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (hReply : decoded.syscallId = .reply)
    (hRegs : Architecture.regMessageRegs layout rf = decoded.msgRegs) :
    endpointReplyCheckedArmR ctx layout rf decoded.msgInfo.length decoded.msgInfo.extraCaps
        decoded.msgInfo.label tid executingCore cap =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap) := by
  rw [endpointReplyCheckedArmR_eq_general, hRegs]
  exact endpointReplyCheckedArmGeneralR_eq ctx decoded tid executingCore gate cap hReply

/-- WS-ZA ZA4.7: the reply's slot check, gate, arm and taint step on the
capability its operand resolved to; a reply moves content to the answered
caller (`replyTaintCaller?`).  Every refusal carries the state it was handed
(`replyOperandArmThenTaintR_eq`). -/
@[inline] def replyOperandArmThenTaintR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (requiredRight : AccessRight)
    (preTaint : TaintTable) (operand : Option Capability) : RefusalCarrying Unit :=
  fun st =>
    match operand with
    | none => .error (.invalidCapability, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedIdleObject cap then .error (.invalidCapability, st)
        else if cap.hasRight requiredRight then
          let callerCode := ThreadId.optCode (replyTaintCaller? st cap)
          match endpointReplyCheckedArmR ctx layout rf len extraCaps label tid executingCore cap
              st with
          | .error refusal => .error refusal
          | .ok ((), stPost) => .ok ((), sendTaintStep callerCode tid preTaint stPost)
        else .error (.illegalAuthority, st)

theorem replyOperandArmThenTaintR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (preEpoch : Nat) (preLength : Nat)
    (preTaint : TaintTable) (st : SystemState) (ref : CSpaceAddr)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (hReply : decoded.syscallId = .reply)
    (hRegs : Architecture.regMessageRegs layout rf = decoded.msgRegs)
    (hRef : resolveCapAddress gate.cspaceRoot gate.capAddr gate.capDepth st = .ok ref)
    (hOperand : syscallOperandCap? st tid decoded.capAddr = SystemState.lookupSlotCap st ref) :
    replyOperandArmThenTaintR ctx layout rf decoded.msgInfo.length decoded.msgInfo.extraCaps
        decoded.msgInfo.label tid executingCore
        gate.requiredRight preTaint (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore gate
        (syscallTaintPlan st tid decoded) preEpoch preLength preTaint) st := by
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel,
    hReply, syscallChecksTargetFirst, Bool.false_eq_true, ↓reduceIte, syscallInvoke,
    syscallLookupCap, syscallResolveCap, hRef]
  simp only [replyTaintStep_eq st tid decoded hReply, hOperand]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [replyOperandArmThenTaintR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedIdleObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hRight : cap.hasRight gate.requiredRight = true
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]
        rw [endpointReplyCheckedArmR_eq ctx decoded tid executingCore gate cap layout rf hReply
          hRegs]
        simp only [RefusalCarrying.ofKernel]
        rcases dispatchWithCapChecked ctx decoded tid executingCore gate cap st with
          _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]

/-- WS-ZA ZA4.7: the reply's dispatch: `dispatchOperandCheckedR` with the
reply's arm (`dispatchReplyCheckedR_eq`). -/
@[inline] def dispatchReplyCheckedR (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore
    (replyOperandArmThenTaintR ctx layout rf len extraCaps label tid executingCore
      (syscallRequiredRight .reply))

theorem dispatchReplyCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (hReply : decoded.syscallId = .reply)
    (hRegs : Architecture.regMessageRegs layout rf = decoded.msgRegs) :
    dispatchReplyCheckedR ctx decoded.capAddr layout rf decoded.msgInfo.length
        decoded.msgInfo.extraCaps
        decoded.msgInfo.label tid executingCore =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) := by
  apply dispatchOperandCheckedR_eq ctx decoded tid executingCore _ (by rw [hReply]; rfl)
    (by rw [hReply]; decide)
  intro st tcb rootCn ref hTcb hRoot hRef
  have hArm := replyOperandArmThenTaintR_eq ctx decoded tid executingCore
    { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
      capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
    st.declassificationAuditEpoch st.declassificationAudit.length st.declassificationTaint
    st ref layout rf hReply hRegs hRef
    (syscallOperandCap?_of_resolved st tid _ tcb rootCn ref hTcb hRoot hRef)
  simp only [hReply] at hArm ⊢
  exact hArm

/-- WS-ZA ZA4.7: the tail of an endpoint's receive queue, as its code
(`SeLe4n.ThreadId.optCode`): read without building an `Option`. -/
@[inline] def receiveQueueTailCode (st : SystemState) (endpointId : SeLe4n.ObjId) : Nat :=
  match st.getEndpoint? endpointId with
  | some ep => ep.recvTailCode
  | none => 0

/-- WS-ZA ZA4.7: a receive blocks, and writes only its slots: no sender is
waiting, the receiver may block (`receiveBlockAdmits`) and every write stays
in place (`receiveBlocksInPlace`). -/
@[inline] def receiveBlocksFast (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyCode : Nat) : Bool :=
  match st.getEndpoint? endpointId with
  | some ep =>
      ep.sendQ.head.isNone &&
      (match st.getTcb? receiver with
       | some rt => receiveBlockAdmits rt &&
           receiveBlocksInPlaceCode st endpointId receiver ep.recvTailCode replyCode
       | none => false)
  | none => false

/-- The CSpace root of the calling thread, as the syscall gate reads it. -/
@[inline] def callerCspaceRoot (st : SystemState) (tid : SeLe4n.ThreadId) : SeLe4n.ObjId :=
  match st.getObject? tid.toObjId with
  | some (.tcb t) => t.cspaceRoot
  | _ => tid.toObjId

/-- The depth of the calling thread's CSpace root, as the syscall gate reads it. -/
@[inline] def callerCspaceDepth (st : SystemState) (tid : SeLe4n.ThreadId) : Nat :=
  match st.getObject? tid.toObjId with
  | some (.tcb t) =>
      match st.getObject? t.cspaceRoot with
      | some (.cnode cn) => cn.depth
      | _ => 0
  | _ => 0

/-- `resolveRecvReplyId` on the message length and first message register
alone, with the gate the caller's own CSpace gives
(`resolveRecvReplyIdR_eq`), so the entry builds no decode record for it. -/
@[inline] def resolveRecvReplyIdR (st : SystemState) (tid : SeLe4n.ThreadId)
    (len : Nat) (replyAddr : SeLe4n.CPtr) : Except KernelError (Option SeLe4n.ReplyId) :=
  if len = 0 then .ok none else
  let gate : SyscallGate :=
    { callerId := tid
      cspaceRoot := callerCspaceRoot st tid
      capAddr := replyAddr
      capDepth := callerCspaceDepth st tid
      requiredRight := .write }
  match syscallLookupCap gate st with
  | .error e => .error e
  | .ok (rcap, _) =>
      match extractReplyId rcap with
      | .error e => .error e
      | .ok rid =>
          match st.getReply? rid with
          | some r =>
              if r.caller.isNone && !st.replyStashedAt rid r then .ok (some rid)
              else .error .replyCapInvalid
          | none => .error .replyCapInvalid

theorem resolveRecvReplyIdR_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (decoded : SyscallDecodeResult) (len : Nat) (replyAddr : SeLe4n.CPtr)
    (hCaller : gate.callerId = tid)
    (hRoot : gate.cspaceRoot = callerCspaceRoot st tid)
    (hDepth : gate.capDepth = callerCspaceDepth st tid)
    (hLen : decoded.msgInfo.length = len)
    (hArgs : len ≠ 0 → decodeRecvArgs decoded = .ok { replyCPtr := replyAddr }) :
    resolveRecvReplyIdR st tid len replyAddr = resolveRecvReplyId gate decoded st := by
  unfold resolveRecvReplyIdR resolveRecvReplyId
  by_cases h0 : len = 0
  · simp [h0, hLen]
  · rw [if_neg h0, hArgs h0]
    have hL : (decoded.msgInfo.length == 0) = false := by simp [hLen, h0]
    simp only [hL, Bool.false_eq_true, ↓reduceIte]
    rcases gate with ⟨c, r, a, d, rr⟩
    simp only at hCaller hRoot hDepth
    subst hCaller hRoot hDepth
    rfl

/-- The reply capability a receive names, checked as `resolveRecvReplyIdR`
checks it once its slot is found: present, not the idle thread's, carrying the
write right, naming a reply object that is free of callers and not already
stashed.  The reply object goes to `onOk` as its code (`SeLe4n.ReplyId.optCode`),
a refusal to `onErr`, so no `Except` or `some` cell is built. -/
@[inline] def recvReplyCapK {α : Type} (st : SystemState) (cap? : Option Capability)
    (onErr : KernelError → α) (onOk : Nat → α) : α :=
  match cap? with
  | none => onErr .invalidCapability
  | some cap =>
      if SeLe4n.Kernel.capTargetsReservedIdleObject cap then onErr .invalidCapability
      else if !cap.hasRight .write then onErr .illegalAuthority
      else
        match cap.target with
        | .replyCap rid =>
            match st.getReply? rid with
            | some r =>
                if r.caller.isNone && !st.replyStashedAt rid r then onOk (rid.val + 1)
                else onErr .replyCapInvalid
            | none => onErr .replyCapInvalid
        | _ => onErr .invalidCapability

/-- `resolveRecvReplyIdR` in continuation form, the reply object as its code
(`resolveRecvReplyK_eq`): the slot is resolved through
`resolveCapAddressKUnrolled`, as the operand is, so the entry builds no gate,
slot reference or result cell for the receive's reply capability.  WS-ZA ZA4.7. -/
@[inline] def resolveRecvReplyK {α : Type} (st : SystemState) (tid : SeLe4n.ThreadId)
    (len : Nat) (replyAddr : SeLe4n.CPtr) (onErr : KernelError → α) (onOk : Nat → α) : α :=
  if len = 0 then onOk 0 else
  resolveCapAddressKUnrolled (callerCspaceRoot st tid) (replyAddr)
    (callerCspaceDepth st tid) st onErr
    (fun cnode slot =>
      recvReplyCapK st (SystemState.lookupSlotCap st { cnode := cnode, slot := slot })
        onErr onOk)

theorem resolveRecvReplyK_eq {α : Type} (st : SystemState) (tid : SeLe4n.ThreadId)
    (len : Nat) (replyAddr : SeLe4n.CPtr) (onErr : KernelError → α) (onOk : Nat → α) :
    resolveRecvReplyK st tid len replyAddr onErr onOk =
      match resolveRecvReplyIdR st tid len replyAddr with
      | .error e => onErr e
      | .ok r => onOk (SeLe4n.ReplyId.optCode r) := by
  unfold resolveRecvReplyK resolveRecvReplyIdR
  by_cases h0 : len = 0
  · simp only [h0, ↓reduceIte, SeLe4n.ReplyId.optCode_none]
  · simp only [h0, ↓reduceIte, syscallLookupCap, syscallResolveCap]
    rw [resolveCapAddressKUnrolled_eq, resolveCapAddressK_eq]
    cases resolveCapAddress (callerCspaceRoot st tid) (replyAddr)
        (callerCspaceDepth st tid) st with
    | error e => rfl
    | ok ref =>
      simp only [recvReplyCapK]
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
            cases st.getReply? rid with
            | none => rfl
            | some r =>
              simp only []
              split <;> rfl
          · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true, Bool.not_false]

/-- The checked receive arm's rendezvous through the specification: the
WithCaps receive, the rendezvous hand-off, then the woken sender's completion
and the receiver's message staged. -/
@[inline] def endpointReceiveRendezvousR (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (replyCode : Nat) (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
      let rid := SeLe4n.ReplyId.ofOptCode replyCode
      let wokenSender? := (st.getEndpoint? epId).bind (·.sendQ.head)
      match endpointReceiveDualWithCapsOnCore epId tid rid (callerCspaceRoot st tid)
          (SeLe4n.Slot.ofNat 0) executingCore st with
      | (st', .ok (dequeued, summary, _sgi)) =>
          match applyReceiveRendezvousHandoff st' tid dequeued executingCore with
          | .error e => .error (e, st)
          | .ok stDon =>
              .ok ((), Architecture.stageDeliveredMessage
                (Architecture.stageWokenSendCompletion stDon wokenSender?) tid
                summary.installedCount)
      | (_, .error e) => .error (e, st)

/-- WS-ZA ZA4.7: the checked receive arm's rendezvous.  A receive that takes a
sender blocked by a capability-free send (`registerRoutedSyscall` of its saved
frame), not delivering a fault, whose writes all stay in their slots
(`receiveTakesInPlace`), takes it in place: the six words of the delivered
frame are read from the sender's saved registers before any write and written
into the receiver's (`performReceiveDelivered`, `receiveTake_delivered`).  Any
other rendezvous goes through the specification
(`endpointReceiveTakeR_eq`). -/
@[inline] def endpointReceiveTakeR (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (replyCode : Nat) (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    match st.getEndpoint? epId with
    | some ep =>
      match ep.sendQ.head with
      | some s =>
        match st.getTcb? s with
        | some sTcb =>
          match Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout
              sTcb.registerContext 32 with
          | .send _ mi =>
            if !sTcb.ipcFaultSend && receiveTakesInPlace st epId tid s sTcb then
              let f := Architecture.regMessageFrameW SeLe4n.arm64DefaultLayout sTcb.registerContext
                mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged
              .ok ((), performReceiveDelivered st epId s sTcb.queueNextCode tid executingCore
                f.x0 f.x1 f.x2 f.x3 f.x4 f.x5)
            else endpointReceiveRendezvousR epId tid replyCode executingCore st
          | _ => endpointReceiveRendezvousR epId tid replyCode executingCore st
        | none => endpointReceiveRendezvousR epId tid replyCode executingCore st
      | none => endpointReceiveRendezvousR epId tid replyCode executingCore st
    | none => endpointReceiveRendezvousR epId tid replyCode executingCore st

theorem endpointReceiveTakeR_eq (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (replyCode : Nat) (executingCore : Concurrency.CoreId) :
    endpointReceiveTakeR epId tid replyCode executingCore =
      endpointReceiveRendezvousR epId tid replyCode executingCore := by
  funext st
  unfold endpointReceiveTakeR
  split
  · next ep hEp =>
    split
    · next s hH =>
      split
      · next sTcb hT =>
        split
        · next capAddr mi hR =>
          split
          · next hG =>
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hG
            obtain ⟨hF, hG⟩ := hG
            obtain ⟨h1, h2, h3⟩ := receiveTake_delivered st epId ep tid
              (SeLe4n.ReplyId.ofOptCode replyCode) (callerCspaceRoot st tid) (SeLe4n.Slot.ofNat 0)
              executingCore s sTcb capAddr mi ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp)
              hH ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hG hR hF
            rw [Architecture.regMessageFrameW_eq, ← TCB.ipcBadgeView_eq_opt]
            unfold endpointReceiveRendezvousR
            simp only [hEp, Option.bind_some, hH, h1, h2, CapTransferSummary.installedCount_empty]
            rw [h3]
          · rfl
        all_goals rfl
      · rfl
    · rfl
  · rfl

/-- The checked receive arm once its reply object is resolved, given as its
code: the blocking receive written in place when it may be
(`receiveBlocksFast`), the rendezvous otherwise (`endpointReceiveTakeR`).
Inlined, so its result is matched by the caller rather than built. -/
@[inline] def endpointReceiveResolvedR (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (replyCode : Nat) (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    if receiveBlocksFast st epId tid replyCode then
      .ok ((), removeRunnableOnCore
        (storeReceiveBlock st epId tid (receiveQueueTailCode st epId) replyCode) tid executingCore)
    else endpointReceiveTakeR epId tid replyCode executingCore st

/-- The checked receive arm (`dispatchWithCapChecked`'s `.receive` case), on
the message length and first message register, refusing in the state it was
handed (`endpointReceiveCheckedArmR_eq`).  Every check, the reply object's
included, precedes the first write; a receive that blocks in place
(`receiveBlocksFast`) holds no pre-state (`receiveBlock_inPlace_eq`). -/
@[inline] def endpointReceiveCheckedArmR (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (len : Nat) (replyAddr : SeLe4n.CPtr) (executingCore : Concurrency.CoreId) (cap : Capability) :
    RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object epId =>
      if !endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) then
        .error (.flowDenied, st)
      else
      let resolved := fun replyCode => endpointReceiveResolvedR epId tid replyCode executingCore st
      resolveRecvReplyK st tid len replyAddr (fun e => .error (e, st)) resolved
    | _ => .error (.invalidCapability, st)

theorem endpointReceiveCheckedArmR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (st : SystemState)
    (hRecv : decoded.syscallId = .receive)
    (len : Nat) (replyAddr : SeLe4n.CPtr)
    (hRid : resolveRecvReplyIdR st tid len replyAddr = resolveRecvReplyId gate decoded st)
    (hSlot : decoded.capRecvSlot = SeLe4n.Slot.ofNat 0)
    (hRoot : callerCspaceRoot st tid = gate.cspaceRoot) :
    endpointReceiveCheckedArmR ctx tid len replyAddr executingCore cap st =
      RefusalCarrying.ofKernel (dispatchWithCapChecked ctx decoded tid executingCore gate cap)
        st := by
  simp only [endpointReceiveCheckedArmR, RefusalCarrying.ofKernel, dispatchWithCapChecked,
    dispatchCapabilityOnly, hRecv]
  cases cap.target with
  | object epId =>
    simp only []
    split
    · rfl
    · rw [resolveRecvReplyK_eq, hRid]
      cases resolveRecvReplyId gate decoded st with
      | error e => rfl
      | ok rid =>
      simp only [endpointReceiveResolvedR]
      by_cases hF : receiveBlocksFast st epId tid (SeLe4n.ReplyId.optCode rid) = true
      · rw [if_pos hF]
        unfold receiveBlocksFast at hF
        cases hEp : st.getEndpoint? epId with
        | none => rw [hEp] at hF; cases hF
        | some ep =>
          rw [hEp] at hF
          simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hF
          obtain ⟨hS, hO⟩ := hF
          cases hR : st.objects[tid.toObjId]? with
          | none => simp only [SystemState.getTcb?, hR] at hO; cases hO
          | some o =>
            cases o with
            | tcb rt =>
              simp only [SystemState.getTcb?, hR] at hO
              simp only [Bool.and_eq_true] at hO
              obtain ⟨hA, hG⟩ := hO
              rw [receiveBlocksInPlaceCode_eq, Endpoint.ofOptCode_recvTailCode,
                SeLe4n.ReplyId.ofOptCode_optCode] at hG
              have hE := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp
              have hTail : receiveQueueTailCode st epId = ep.recvTailCode := by
                simp only [receiveQueueTailCode, hEp]
              obtain ⟨t, hT, hB⟩ := receiveBlock_receiver_blocked st epId ep tid rt rid
                executingCore hE hR hA hG
              unfold endpointReceiveDualWithCapsOnCore
              rw [receiveBlock_inPlace_eq st epId ep tid rt rid executingCore hE hS hR hA hG]
              have hSnd : (receiveRendezvousSender? st epId).isNone = true := by
                simp [receiveRendezvousSender?, hEp, hS]
              simp only [hSnd, ↓reduceIte, hTail]
              have hNoCall : rendezvousDequeuedCall (removeRunnableOnCore
                  (storeReceiveBlock st epId tid ep.recvTailCode (SeLe4n.ReplyId.optCode rid))
                  tid executingCore) tid =
                  false := by
                unfold rendezvousDequeuedCall
                rw [show lookupTcb _ tid = some t from by
                  simp only [lookupTcb]
                  split
                  · next hRes =>
                    simp only [receiveBlocksInPlace, enqueuesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hG
                    rw [hG.1.1.1.1.1.1.1] at hRes; cases hRes
                  · exact hT]
                simp only [hB]
              rw [applyReceiveRendezvousHandoff_of_no_call _ _ _ _ hNoCall]
              simp only [hS, Option.bind_some, Architecture.stageWokenSendCompletion_none]
              unfold Architecture.stageDeliveredMessage
              simp only [hT, hB, reduceCtorEq, ↓reduceIte]
            | _ => simp only [SystemState.getTcb?, hR] at hO; cases hO
      · rw [if_neg hF, endpointReceiveTakeR_eq]
        unfold endpointReceiveRendezvousR
        simp only [hRoot, hSlot, SeLe4n.ReplyId.ofOptCode_optCode]
        rcases endpointReceiveDualWithCapsOnCore epId tid rid gate.cspaceRoot
          (SeLe4n.Slot.ofNat 0) executingCore st with ⟨st', _ | ⟨dq, summary, sgi⟩⟩
        · rfl
        · simp only []
          cases applyReceiveRendezvousHandoff st' tid dq executingCore <;> rfl
  | _ => rfl

/-- The sender whose content a receive takes, read from the pre-state before
the arm: the head of the send queue of the endpoint its capability names
(`receiverTaintEdges`), as its code (`SeLe4n.ThreadId.optCode`). -/
@[inline] def receiveTaintSourceCode (st : SystemState) (cap : Capability) : Nat :=
  match cap.target with
  | .object epId =>
      match st.getEndpoint? epId with
      | some ep => ep.sendHeadCode
      | none => 0
  | _ => 0

/-- The receive's taint step, without the plan: the sender's pre-state taint
joins the receiver's (`receiveTaintStep_eq`). -/
@[inline] def receiveTaintStep (sourceCode : Nat) (tid : SeLe4n.ThreadId)
    (preTaint : TaintTable) (post : SystemState) : SystemState :=
  match sourceCode with
  | s + 1 =>
      let sender : SeLe4n.ThreadId := ⟨s⟩
      { post with declassificationTaint :=
          post.declassificationTaint.joinAt tid.toObjId (preTaint sender.toObjId) }
  | 0 => post

theorem receiveTaintStep_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (hRecv : decoded.syscallId = .receive)
    (preEpoch : Nat) (preLength : Nat) (preTaint : TaintTable)
    (post : SystemState) :
    applySyscallTaintAfter (syscallTaintPlan st tid decoded) preEpoch preLength preTaint post =
      (match syscallOperandCap? st tid decoded.capAddr with
        | some cap => receiveTaintStep (receiveTaintSourceCode st cap) tid preTaint post
        | none => post) := by
  simp only [syscallTaintPlan, contentFlowClass, hRecv, contentFlowEdges, contentFlowClears,
    contentFlowBypassed]
  rcases syscallOperandCap? st tid decoded.capAddr with _ | ⟨target, _, _⟩
  · simp [applySyscallTaintAfter, syscallRecordsDeclassification,
      applyOrigination, applyTaintClears, applyTaintFlow]
  · cases target with
    | object epId =>
      simp only [receiveTaintSourceCode, receiverTaintEdges]
      cases st.getEndpoint? epId with
      | none =>
        simp [receiveTaintStep, applySyscallTaintAfter, syscallRecordsDeclassification,
          applyOrigination, applyTaintClears, applyTaintFlow]
      | some ep =>
        simp only [Option.bind_some, ← Endpoint.ofOptCode_sendHeadCode]
        cases ep.sendHeadCode <;>
          simp [receiveTaintStep, SeLe4n.ThreadId.ofOptCode, applySyscallTaintAfter,
            syscallRecordsDeclassification, applyOrigination, applyTaintClears, applyTaintFlow]
    | _ =>
      simp [receiveTaintSourceCode, receiveTaintStep, applySyscallTaintAfter,
        syscallRecordsDeclassification, applyOrigination, applyTaintClears, applyTaintFlow]

/-- The receive's slot check, gate, arm and taint step on the capability its
operand resolved to, every refusal carrying the state it was handed
(`receiveOperandArmThenTaintR_eq`). -/
@[inline] def receiveOperandArmThenTaintR (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (len : Nat) (replyAddr : SeLe4n.CPtr) (executingCore : Concurrency.CoreId) (requiredRight : AccessRight)
    (preTaint : TaintTable) (operand : Option Capability) : RefusalCarrying Unit :=
  fun st =>
    match operand with
    | none => .error (.invalidCapability, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedIdleObject cap then .error (.invalidCapability, st)
        else if cap.hasRight requiredRight then
          let sourceCode := receiveTaintSourceCode st cap
          match endpointReceiveCheckedArmR ctx tid len replyAddr executingCore cap st with
          | .error refusal => .error refusal
          | .ok ((), stPost) => .ok ((), receiveTaintStep sourceCode tid preTaint stPost)
        else .error (.illegalAuthority, st)

theorem receiveOperandArmThenTaintR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (preEpoch : Nat) (preLength : Nat)
    (preTaint : TaintTable) (st : SystemState) (ref : CSpaceAddr)
    (hRecv : decoded.syscallId = .receive) (len : Nat) (replyAddr : SeLe4n.CPtr)
    (hRid : resolveRecvReplyIdR st tid len replyAddr = resolveRecvReplyId gate decoded st)
    (hSlot : decoded.capRecvSlot = SeLe4n.Slot.ofNat 0)
    (hRoot : callerCspaceRoot st tid = gate.cspaceRoot)
    (hRef : resolveCapAddress gate.cspaceRoot gate.capAddr gate.capDepth st = .ok ref)
    (hOperand : syscallOperandCap? st tid decoded.capAddr = SystemState.lookupSlotCap st ref) :
    receiveOperandArmThenTaintR ctx tid len replyAddr executingCore gate.requiredRight
        preTaint (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore gate
        (syscallTaintPlan st tid decoded) preEpoch preLength preTaint) st := by
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel,
    hRecv, syscallChecksTargetFirst, Bool.false_eq_true, ↓reduceIte, syscallInvoke,
    syscallLookupCap, syscallResolveCap, hRef]
  simp only [receiveTaintStep_eq st tid decoded hRecv, hOperand]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [receiveOperandArmThenTaintR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedIdleObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hRight : cap.hasRight gate.requiredRight = true
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]
        rw [endpointReceiveCheckedArmR_eq ctx decoded tid executingCore gate cap st hRecv len replyAddr
          hRid hSlot hRoot]
        simp only [RefusalCarrying.ofKernel]
        rcases dispatchWithCapChecked ctx decoded tid executingCore gate cap st with
          _ | ⟨⟨⟩, stPost⟩ <;> rfl
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]

/-- The receive's dispatch, on the message length and first message register
the entry read: `dispatchOperandCheckedR` with the receive's arm
(`dispatchReceiveCheckedR_eq`). -/
@[inline] def dispatchReceiveCheckedR (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (len : Nat) (replyAddr : SeLe4n.CPtr) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) :
    RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore
    (receiveOperandArmThenTaintR ctx tid len replyAddr executingCore (syscallRequiredRight .receive))

theorem dispatchReceiveCheckedR_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (len : Nat) (replyAddr : SeLe4n.CPtr)
    (hRecv : decoded.syscallId = .receive)
    (hLen : decoded.msgInfo.length = len)
    (hSlot : decoded.capRecvSlot = SeLe4n.Slot.ofNat 0)
    (hReplyAddr : len ≠ 0 → decoded.msgRegs[0]? = some ⟨replyAddr.toNat⟩) :
    dispatchReceiveCheckedR ctx decoded.capAddr len replyAddr tid executingCore =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) := by
  apply dispatchOperandCheckedR_eq ctx decoded tid executingCore _ (by rw [hRecv]; rfl)
    (by rw [hRecv]; decide)
  intro st tcb rootCn ref hTcb hRoot hRef
  have hArgs : len ≠ 0 → decodeRecvArgs decoded = .ok { replyCPtr := replyAddr } := by
    intro hN
    have h := hReplyAddr hN
    rw [Array.getElem?_eq_some_iff] at h
    obtain ⟨h0, hv⟩ := h
    simp only [decodeRecvArgs, requireMsgReg, h0, ↓reduceDIte, hv, bind, Except.bind, pure, Except.pure,
      SeLe4n.CPtr.ofNat_toNat]
  have hRid := resolveRecvReplyIdR_eq st tid
    { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
      capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
    decoded len replyAddr rfl (by simp only [callerCspaceRoot, hTcb])
    (by simp only [callerCspaceDepth, hTcb, hRoot]) hLen hArgs
  have hArm := receiveOperandArmThenTaintR_eq ctx decoded tid executingCore
    { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
      capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
    st.declassificationAuditEpoch st.declassificationAudit.length st.declassificationTaint
    st ref hRecv len replyAddr hRid hSlot (by simp only [callerCspaceRoot, hTcb]) hRef
    (syscallOperandCap?_of_resolved st tid _ tcb rootCn ref hTcb hRoot hRef)
  simp only [hRecv] at hArm ⊢
  exact hArm

end SeLe4n.Kernel
