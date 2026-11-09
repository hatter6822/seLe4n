-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.CapTransferInPlace
import SeLe4n.Kernel.IPC.CrossCore.InertCapTransferInPlace
import SeLe4n.Kernel.RefusalCarryingDispatch

/-!
# A capability-carrying rendezvous, delivered in place

A send, call or take that transfers capabilities writes its rendezvous in
place, runs the transfer in place (`capTransferK`) on the state the rendezvous
left, and writes the delivered frame with the transfer's report.  The
specification runs the transfer after the rendezvous too, on the state holding
the message; the transfer commutes with the message write
(`receiveTransferCaps_mapTcbInPlace`), and the rendezvous reads every buffer and
CNode the transfer reads where the syscall found it (`ipcBufferReadsAgree`), so
the request and the receiver's side the transfer reads in place are the ones
the specification reads before the rendezvous.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood
open SeLe4n.Kernel.Architecture.IpcBufferRead

/-! ### The transfer's reads, where the rendezvous left them -/

namespace ipcBufferReadsAgree

variable {X st : SystemState} (h : ipcBufferReadsAgree X st)
include h

theorem bufferWordPAddrOf? (vroot : SeLe4n.ObjId) (buf : SeLe4n.VAddr) (idx : Nat) (w : Bool) :
    bufferWordPAddrOf? X vroot buf idx w = bufferWordPAddrOf? st vroot buf idx w := by
  unfold SeLe4n.Kernel.bufferWordPAddrOf?
  rw [h.getVSpaceRoot?, h.2]

theorem senderExtraCapAddr? (tcb : TCB) (i : Nat) :
    senderExtraCapAddr? X tcb i = senderExtraCapAddr? st tcb i := by
  unfold SeLe4n.Kernel.senderExtraCapAddr?
  rw [ipcBufferWordPAddr?_eq_of, ipcBufferWordPAddr?_eq_of, h.bufferWordPAddrOf?, h.2]

theorem senderExtraCapAddrs (tcb : TCB) (c : Nat) :
    senderExtraCapAddrs X tcb c = senderExtraCapAddrs st tcb c := by
  unfold SeLe4n.Kernel.senderExtraCapAddrs
  have : SeLe4n.Kernel.senderExtraCapAddr? X tcb = SeLe4n.Kernel.senderExtraCapAddr? st tcb :=
    funext fun i => h.senderExtraCapAddr? tcb i
  rw [this]

theorem frameCapRequestOf (tcb : TCB) (c : Nat) :
    frameCapRequestOf X tcb c = frameCapRequestOf st tcb c := by
  unfold SeLe4n.Kernel.frameCapRequestOf
  rw [h.senderExtraCapAddrs, h.getCNode?]

theorem receiverHasBuffer (tcb : TCB) :
    receiverHasBuffer X tcb = receiverHasBuffer st tcb := by
  unfold SeLe4n.Kernel.receiverHasBuffer
  rw [ipcBufferWordPAddr?_eq_of, ipcBufferWordPAddr?_eq_of, h.bufferWordPAddrOf?]

theorem receiverBufferWord? (tcb : TCB) (idx : Nat) :
    receiverBufferWord? X tcb idx = receiverBufferWord? st tcb idx := by
  unfold SeLe4n.Kernel.receiverBufferWord?
  rw [ipcBufferWordPAddr?_eq_of, ipcBufferWordPAddr?_eq_of, h.bufferWordPAddrOf?, h.2]

theorem receivePathSlot? (tcb : TCB) (c i d : UInt64) :
    receivePathSlot? X tcb c i d = receivePathSlot? st tcb c i d := by
  have hC : ∀ id, X.getCNode? id = st.getCNode? id := h.getCNode?
  unfold SeLe4n.Kernel.receivePathSlot?
  simp only [hC, resolveCapAddress_congr_getCNode? X st hC, lookupSlotCap_congr_getCNode? X st hC]

theorem receiveSlot? (tcb : TCB) : receiveSlot? X tcb = receiveSlot? st tcb := by
  unfold SeLe4n.Kernel.receiveSlot?
  simp only [h.receiverBufferWord?, h.receivePathSlot?]

theorem capTargetOf (tcb : TCB) : capTargetOf X tcb = capTargetOf st tcb := by
  unfold SeLe4n.Kernel.capTargetOf
  rw [h.receiverHasBuffer, h.receiveSlot?]

end ipcBufferReadsAgree

/-! ### The transfer always answers -/

theorem receiveTransferCaps_ok (req : Option (SeLe4n.ObjId × Array SeLe4n.CPtr × Nat))
    (ep : Option SeLe4n.ObjId) (tgt : Option (TCB × Option CSpaceAddr)) (Z : SystemState) :
    ∃ s Z', receiveTransferCaps req ep tgt Z = .ok (s, Z') := by
  unfold receiveTransferCaps
  rcases req with _ | ⟨root, addrs, depth⟩
  · exact ⟨_, _, rfl⟩
  · simp only []
    split
    · exact ⟨_, _, rfl⟩
    · rcases tgt with _ | ⟨rt, slot?⟩
      · exact ⟨_, _, rfl⟩
      · obtain ⟨⟨s, Z'⟩, h⟩ := ipcUnwrapCapsLoop_ok (resolveExtraCaps root addrs depth true Z) ep rt
          (resolveExtraCaps root addrs depth true Z).size 0 slot? #[] Z
        exact ⟨s, Z', h⟩

/-! ### The frame with the transfer's report -/

/-- The message-info word a frame of a register-routed message carries, with
the transfer's report `capInfo` (`returnMessageInfo`).  Out of line, as
`regMessageInfoWord`. -/
@[noinline] def regMessageInfoWordCaps (layout : SeLe4n.SyscallRegisterLayout) (len capInfo : Nat) :
    UInt64 :=
  (({ length := min (min (Architecture.regMessageLength layout len) 4) maxMessageRegisters
      extraCaps := capInfo % 4
      label := min 0 (Architecture.errorLabelBase - 1)
      capsUnwrapped := capInfo / 4 % 8 } : MessageInfo).encode).toUInt64

/-- `regMessageFrameW` with the transfer's report in its message-info word. -/
@[inline] def regMessageFrameCapsW (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (len : Nat) (badgeWord : SeLe4n.Badge) (badged : Bool) (capInfo : Nat) :
    Architecture.SyscallReturnFrame :=
  { x0 := Architecture.badgeWordIf badgeWord badged
    x1 := regMessageInfoWordCaps layout len capInfo
    x2 := Architecture.regMessageWord layout rf len 0
    x3 := Architecture.regMessageWord layout rf len 1
    x4 := Architecture.regMessageWord layout rf len 2
    x5 := Architecture.regMessageWord layout rf len 3 }

theorem returnFrameOfMessage_regMessageBody_caps (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badgeWord : SeLe4n.Badge) (badged : Bool)
    (capInfo : Nat) :
    Architecture.returnFrameOfMessage
        { registers := Architecture.regMessageBody layout rf len,
          badge := SeLe4n.Badge.opt badgeWord badged } capInfo 0 =
      regMessageFrameCapsW layout rf len badgeWord badged capInfo := by
  simp only [Architecture.returnFrameOfMessage, Architecture.returnMessageInfo,
    regMessageFrameCapsW, regMessageInfoWordCaps, Architecture.regMessageBody_size,
    Architecture.regMessageBody_word, Nat.add_zero]
  rw [← Architecture.badgeWordOrZero_opt]
  rfl

/-- **Staging a held message with a report is writing its frame**
(`stageDeliveredMessage_holdMessage` with the transfer's report). -/
theorem stageDeliveredMessage_holdMessage_caps (X : SystemState) (r : SeLe4n.ThreadId)
    (msg : IpcMessage) (capInfo : Nat) (hNo : X.objects.noResizeDue)
    (hSz : msg.registers.size ≤ 4) :
    Architecture.stageDeliveredMessage (X.mapTcbInPlace r (holdMessage msg)) r capInfo =
      writeDeliveredFrameIfReady X r (Architecture.returnFrameOfMessage msg capInfo 0)
        (fun _ => X.mapTcbInPlace r (holdMessage msg)) := by
  unfold Architecture.stageDeliveredMessage writeDeliveredFrameIfReady
  rw [SystemState.getTcb?_mapTcbInPlace, if_pos rfl]
  cases hT : X.getTcb? r with
  | none => exact mapTcbInPlace_eq_self_of_getTcb?_none X r _ hT
  | some t =>
    simp only [Option.map_some, TCB.withMessageSlots_ipcState, TCB.withMessageSlots_pendingMessage]
    split
    · rw [messageOverflowWrites_of_size_le _ _ _ hSz, Architecture.recordPhysicalWrites_nil]
      unfold Architecture.writeDeliveredFrameToTcb
      rw [SystemState.updateTcb_eq_mapTcbInPlace (X.mapTcbInPlace r (holdMessage msg)) _ _ hNo,
        SystemState.mapTcbInPlace_mapTcbInPlace]
      rfl
    · rfl

/-! ### The send -/

/-- **A delivery's last write, with the transfer's report**: the frame, its
message-info word carrying the report, written into the ready receiver's saved
registers; the message held where the receiver is, unexpectedly, not ready.
The report comes first, so it is read before the state is handed over. -/
@[noinline] def deliverCapsFrame (capInfo : Nat) (Y : SystemState) (r : SeLe4n.ThreadId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) : SystemState :=
  writeDeliveredFrameIfReady Y r (regMessageFrameCapsW layout rf len badgeWord badged capInfo)
    (fun _ => holdDeliveredBody Y r layout rf len (SeLe4n.Badge.opt badgeWord badged))

/-- **The send rendezvous that transfers capabilities, delivered**: the
receiver woken without the message, the transfer in place, then the frame
with the transfer's report.  The sender and the receiver enter as the words
the transfer reads of them (`capTransferK`), read before the rendezvous. -/
@[noinline] def performSendCapsDelivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (r : SeLe4n.ThreadId) (nextCode : Nat)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (core : Concurrency.CoreId)
    (sv : SeLe4n.ObjId) (sb : SeLe4n.VAddr) (sroot : SeLe4n.ObjId) (count : Nat)
    (rv : SeLe4n.ObjId) (rb : SeLe4n.VAddr) (rroot : SeLe4n.ObjId) : SystemState :=
  let X := (wakeThread (storeSendRendezvousReady st endpointId r nextCode) r core).1
  capTransferK X endpointId sv sb sroot count rv rb rroot fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
    deliverCapsFrame (capStepsInfo endpointId true x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl X 0 n free 0 0)
      (capStepsApply endpointId true rv rb x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n free X)
      r layout rf len badgeWord badged

/-- **The staged send rendezvous that transfers capabilities is the delivered
one**, for a message of at most four words read in the sender's registers: the
specification's transfer after the rendezvous, then the woken receiver's stage
with the transfer's report. -/
theorem sendRendezvousCaps_eq_delivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (r : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (core : Concurrency.CoreId) (stcb rt : TCB) (count : Nat)
    (hNo : st.objects.noResizeDue) (hSz : Architecture.regMessageLength layout len ≤ 4) :
    (match receiveTransferCaps (frameCapRequestOf st stcb count) (some endpointId)
        (capTargetOf st rt)
        (wakeThread (storeSendRendezvous st endpointId r next
          { registers := Architecture.regMessageBody layout rf len,
            badge := SeLe4n.Badge.opt badgeWord badged }) r core).1 with
      | .ok (s, st'') =>
        Architecture.stageWokenDelivery (clearWokenReceiverStashPure (some r) st'') (some r)
          s.capInfo
      | .error _ => st) =
      performSendCapsDelivered st endpointId r (ThreadId.optCode next) layout rf len badgeWord badged
        core stcb.vspaceRoot stcb.ipcBuffer stcb.cspaceRoot count rt.vspaceRoot rt.ipcBuffer
        rt.cspaceRoot := by
  have hNo0 := storeSendRendezvousWith_noResizeDue st endpointId r next ipcReadyTcb hNo
  have hNoY := wakeThread_noResizeDue _ r core hNo0
  have hA := ipcBufferReadsAgree_sendWoken st endpointId r (ThreadId.optCode next) core hNo
  unfold performSendCapsDelivered
  have hK := capTransferK_eq
    (wakeThread (storeSendRendezvousReady st endpointId r (ThreadId.optCode next)) r core).1
    endpointId stcb count rt
    (fun i Y => deliverCapsFrame i Y r layout rf len badgeWord badged)
  simp only at hK
  rw [hK, hA.frameCapRequestOf, hA.capTargetOf]
  unfold storeSendRendezvousReady
  rw [SeLe4n.ThreadId.ofOptCode_optCode]
  rw [storeSendRendezvous_eq_with, receiveCompleteTcb_eq_slots, receiveReadyTcb_eq_slots,
    storeSendRendezvousWith_comp _ _ _ _ _ _ hNo, storeSendRendezvousWith_comp _ _ _ _ _ _ hNo]
  simp only [receiveCompleteSlots, clearMessageSlots]
  rw [wakeThread_msg _ _ _ _ _ _ _ hNo0, wakeThread_msg _ _ _ _ _ _ _ hNo0]
  dsimp only
  generalize (wakeThread (storeSendRendezvousWith st endpointId r next ipcReadyTcb) r core).1 = Y0
    at hNoY
  rw [receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _) r _ _ _ Y0 hNoY,
    receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _) r _ _ _ Y0 hNoY]
  obtain ⟨s, Y1, hT⟩ := receiveTransferCaps_ok (frameCapRequestOf st stcb count) (some endpointId)
    (capTargetOf st rt) Y0
  have hNo1 := receiveTransferCaps_noResizeDue _ _ _ Y0 Y1 s hNoY hT
  rw [hT]
  simp only [mapStepState]
  have hD : ∀ M : IpcMessage,
      TCB.withMessageSlots id (fun _ => some M) (fun _ : Nat => 0) =
        holdMessage M ∘ TCB.withMessageSlots id (fun _ => none) (fun _ => 0) := fun _ => rfl
  rw [clearWokenReceiverStashPure_mapTcbInPlace _ _ _ (fun _ => rfl),
    hD, ← SystemState.mapTcbInPlace_mapTcbInPlace,
    Architecture.stageWokenDelivery_some,
    stageDeliveredMessage_holdMessage_caps _ _ _ _
      ((SystemState.mapTcbInPlace_noResizeDue _ _ _).mpr hNo1)
      (by rw [Architecture.regMessageBody_size]; exact hSz),
    returnFrameOfMessage_regMessageBody_caps]
  rfl

/-! ### The request a routed frame makes -/

/-- The extra-capability count a register-routed frame names: bits 7–8 of its
message-info word (`decodeMsgInfoWord`). -/
@[inline] def routedExtraCaps (rf : SeLe4n.RegisterFile) : Nat :=
  ((SeLe4n.readRegWord rf SeLe4n.arm64DefaultLayout.msgInfoReg >>> 7) &&& 3).toNat

theorem routedExtraCaps_eq {rf : SeLe4n.RegisterFile} {sid : SyscallId} {capAddr : SeLe4n.CPtr}
    {mi : MessageInfo}
    (hR : Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 =
      .transferring sid capAddr mi) :
    routedExtraCaps rf = mi.extraCaps := by
  unfold Architecture.RegisterDecode.registerRoutedSyscall at hR
  split at hR
  · unfold Architecture.RegisterDecode.registerRoutedSyscallOf at hR
    dsimp only at hR
    cases hD : Architecture.RegisterDecode.decodeMsgInfoWord
        (SeLe4n.readRegWord rf SeLe4n.arm64DefaultLayout.msgInfoReg) with
    | error e => rw [hD] at hR; cases hR
    | ok m =>
      rw [hD] at hR
      have hm : m = mi := by
        simp only [Architecture.RegisterDecode.routedShortTail_eq,
          Architecture.RegisterDecode.routedLongTail_eq] at hR
        repeat' split at hR
        all_goals first
          | (cases hR; rfl)
          | (cases hR; done)
          | (rcases Architecture.RegisterDecode.unroutedSyscall_eq hR with h | ⟨h, -⟩ <;> cases h)
          | skip
        all_goals done
      subst hm
      unfold Architecture.RegisterDecode.decodeMsgInfoWord at hD
      split at hD
      · cases hD; rfl
      · cases hD
  · cases hR

/-- The message length a register-routed frame names: bits 0–6 of its
message-info word (`decodeMsgInfoWord`), read as a word so an arm that reads
it builds no message info. -/
@[inline] def routedLength (rf : SeLe4n.RegisterFile) : Nat :=
  (SeLe4n.readRegWord rf SeLe4n.arm64DefaultLayout.msgInfoReg &&& 0x7F).toNat

theorem routedLength_eq {rf : SeLe4n.RegisterFile} {sid : SyscallId} {capAddr : SeLe4n.CPtr}
    {mi : MessageInfo}
    (hR : Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 =
      .transferring sid capAddr mi) :
    routedLength rf = mi.length := by
  unfold Architecture.RegisterDecode.registerRoutedSyscall at hR
  split at hR
  · unfold Architecture.RegisterDecode.registerRoutedSyscallOf at hR
    dsimp only at hR
    cases hD : Architecture.RegisterDecode.decodeMsgInfoWord
        (SeLe4n.readRegWord rf SeLe4n.arm64DefaultLayout.msgInfoReg) with
    | error e => rw [hD] at hR; cases hR
    | ok m =>
      rw [hD] at hR
      have hm : m = mi := by
        simp only [Architecture.RegisterDecode.routedShortTail_eq,
          Architecture.RegisterDecode.routedLongTail_eq] at hR
        repeat' split at hR
        all_goals first
          | (cases hR; rfl)
          | (cases hR; done)
          | (rcases Architecture.RegisterDecode.unroutedSyscall_eq hR with h | ⟨h, -⟩ <;> cases h)
          | skip
        all_goals done
      subst hm
      unfold Architecture.RegisterDecode.decodeMsgInfoWord at hD
      split at hD
      · cases hD; rfl
      · cases hD
  · cases hR

theorem frameCapRequestOf_zero (st : SystemState) (tcb : TCB) : frameCapRequestOf st tcb 0 = none := by
  unfold frameCapRequestOf
  rw [senderExtraCapAddrs_zero]
  rfl

/-- **The request a routed short frame makes**: what the sender's frame asks
to transfer (`senderFrameCapRequest`) is the request for the count its
message-info word names, under its capability's grant right. -/
theorem senderFrameCapRequest_routed (st : SystemState) (tid : SeLe4n.ThreadId) (stcb : TCB)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo) (sid : SyscallId)
    (g : Bool) (hRf : stcb.registerContext = rf)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 =
      .transferring sid capAddr mi)
    (hLen : mi.length ≤ 4) :
    senderFrameCapRequest st tid stcb g =
      frameCapRequestOf st stcb (if g then routedExtraCaps rf else 0) := by
  unfold senderFrameCapRequest
  cases g
  · simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true, frameCapRequestOf_zero]
  · obtain ⟨-, -, -, hShort, -⟩ :=
      Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedTransferring st tid _ _ 32
        sid capAddr mi hR
    have hDec := hShort hLen
    rw [← hRf] at hDec
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, blockedSenderDecode, hDec,
      routedExtraCaps_eq hR]
    rfl

theorem sendCapRequest_routed (st : SystemState) (epId : SeLe4n.ObjId) (tid r : SeLe4n.ThreadId)
    (stcb : TCB) (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (sid : SyscallId) (b : Option SeLe4n.Badge) (g : Bool)
    (hRecv : (st.getEndpoint? epId).bind (·.receiveQ.head) = some r)
    (hS : st.getTcb? tid = some stcb) (hRf : stcb.registerContext = rf)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 =
      .transferring sid capAddr mi)
    (hLen : mi.length ≤ 4) :
    sendCapRequest st epId tid (.frame b g) =
      frameCapRequestOf st stcb (if g then routedExtraCaps rf else 0) := by
  unfold sendCapRequest
  rw [hRecv]
  simp only [hS]
  exact senderFrameCapRequest_routed st tid stcb rf capAddr mi sid g hRf hR hLen

theorem receiverCapTarget?_eq_capTargetOf {st : SystemState} {r : SeLe4n.ThreadId} {rt : TCB}
    (hT : st.getTcb? r = some rt) : receiverCapTarget? st r = capTargetOf st rt := by
  unfold receiverCapTarget? capTargetOf
  rw [hT]

end SeLe4n.Kernel
