-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.ReplyCapsDelivered

/-!
# A capability-carrying message of more than four words, delivered in place

seL4's `doIPCTransfer` runs `transferCaps` and then copies the message
(`copyMRs`): the inline words register to register, the rest from the
sender's IPC buffer into the receiver's, and the receiver's message info
reports both what arrived and what the transfer did.  The specification holds
the whole message in the receiver, runs the transfer, then stages the message
with the transfer's report.  Here the rendezvous is written in place, the
transfer runs in place (`capTransferK`), and the frame and the overflow words
are written last, the frame carrying the report (`deliverLongSendFrame`).

The overflow words are read from the sender's buffer after the transfer.  The
transfer writes CNodes, the derivation links, an untyped source's free index
and its badge ledger, never a thread's buffer address, a VSpace root or the
machine (`receiveTransferCaps_wordReads`), so each word is the one the
specification's decode read before the rendezvous.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood
open Architecture.RegisterDecode

/-! ## The transfer keeps every buffer's words -/

/-- The states after `B` that read every buffer's words as `B` does, with no
resize due. -/
def KeepsWordReads (B s : SystemState) : Prop :=
  s.objects.noResizeDue ∧ ipcWordReadsAgree s B

theorem KeepsWordReads.refl (B : SystemState) (h : B.objects.noResizeDue) :
    KeepsWordReads B B :=
  ⟨h, .refl B⟩

/-- A write of one key that keeps the word view of the object there keeps every
buffer's words. -/
theorem KeepsWordReads.mapValueAt {B s : SystemState} (h : KeepsWordReads B s) (k : SeLe4n.ObjId)
    (F : KernelObject → KernelObject)
    (hF : ∀ o, s.objects.get? k = some o → ipcWordViewOf (F o) = ipcWordViewOf o) :
    KeepsWordReads B { s with objects := s.objects.mapValueAt k F } := by
  refine ⟨(RHTable.noResizeDue_mapValueAt _ _ _).mpr h.1, ?_⟩
  refine ipcWordReadsAgree.trans (b := s) ⟨fun x => ?_, rfl⟩ h.2
  simp only [RHTable_getElem?_eq_get?, RHTable.get?_mapValueAt]
  split
  · next hk =>
    have hk' : k = x := beq_iff_eq.mp hk
    subst hk'
    cases hg : s.objects.get? k with
    | none => rfl
    | some o => simp only [Option.map_some, Option.bind_some, hF o hg]
  · rfl

theorem KeepsWordReads.setSlotLinkWords {B s : SystemState} (h : KeepsWordReads B s)
    (o : SeLe4n.ObjId) (sl : SeLe4n.Slot) (f : LinkField) (c w : Nat) :
    KeepsWordReads B (s.setSlotLinkWords o sl f c w) := by
  rw [setSlotLinkWords_eq_modifyObject _ _ _ _ _ _ h.1,
    SystemState.modifyObject_eq_mapValueAt _ _ _ h.1]
  refine h.mapValueAt o _ (fun ob _ => ?_)
  cases ob <;> rfl

theorem KeepsWordReads.linkAddChild {B s : SystemState} (h : KeepsWordReads B s) (p c : SlotRef) :
    KeepsWordReads B (s.linkAddChild p c) := by
  unfold SystemState.linkAddChild
  dsimp only
  split <;> (repeat apply KeepsWordReads.setSlotLinkWords) <;> exact h

theorem KeepsWordReads.cdtAddChild {B s : SystemState} (h : KeepsWordReads B s) (p c : SlotRef)
    (op : DerivationOp) : KeepsWordReads B (s.cdtAddChild p c op) :=
  KeepsWordReads.linkAddChild (s := s.modifyCdt _) h p c

theorem KeepsWordReads.storeObject_cnode {B s s' : SystemState} (h : KeepsWordReads B s)
    (k : SeLe4n.ObjId) (cn0 cn : CNode) (hk : s.objects[k]? = some (.cnode cn0))
    (hS : storeObject k (.cnode cn) s = .ok ((), s')) : KeepsWordReads B s' := by
  have hg : s.objects.get? k = some (.cnode cn0) := by
    simpa only [RHTable_getElem?_eq_get?] using hk
  unfold storeObject at hS
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hS
  rw [← hS]
  have := h.mapValueAt k (fun _ => .cnode cn) (fun o ho => by
    rw [hg] at ho; cases ho; rfl)
  rw [RHTable.insert_eq_mapValueAt _ (RHTable.findsInPlace_of_get? h.1 hg)]
  exact this

theorem KeepsWordReads.storeCNodeWith {B s : SystemState} (h : KeepsWordReads B s)
    (k : SeLe4n.ObjId) (f : CNode → CNode) : KeepsWordReads B (s.storeCNodeWith k f) := by
  rcases SystemState.storeCNodeWith_cases s k f with ⟨cn, hk, hS⟩ | e
  · exact h.storeObject_cnode k cn (f cn) hk hS
  · rw [e]; exact h

theorem KeepsWordReads.untypedSourceSetFull {B s : SystemState} (h : KeepsWordReads B s)
    (src : CSpaceAddr) (cap : Capability) : KeepsWordReads B (untypedSourceSetFull s src cap) :=
  untypedSourceSetFull_of (P := KeepsWordReads B) h (fun _ => h.storeCNodeWith _ _)

theorem KeepsWordReads.ipcTransferSingleCap {B s s' : SystemState} (h : KeepsWordReads B s)
    (cap : Capability) (src : SlotRef) (dst : CSpaceAddr)
    (hT : ipcTransferSingleCap cap src dst s = .ok ((), s')) : KeepsWordReads B s' := by
  obtain ⟨_, s2, -, -, -, hIns, rfl⟩ := ipcTransferSingleCap_ok_cases hT
  obtain ⟨cn, hC, -, -, hS⟩ := cspaceInsertSlot_ok_decompose _ _ _ _ hIns
  exact ((h.storeObject_cnode _ cn _ ((SystemState.getCNode?_eq_some_iff _ _ _).mp hC)
    hS).cdtAddChild _ _ _).untypedSourceSetFull _ _

theorem KeepsWordReads.recordUnwrappedBadge {B s : SystemState} (h : KeepsWordReads B s)
    (rtcb : TCB) (i : Nat) (b : SeLe4n.Badge) :
    KeepsWordReads B (recordUnwrappedBadge s rtcb i b) := by
  have hO := recordUnwrappedBadge_objects s rtcb i b
  have hM := recordUnwrappedBadge_machine s rtcb i b
  exact ⟨hO ▸ h.1, ipcWordReadsAgree.trans (b := s) ⟨fun x => by rw [hO], hM⟩ h.2⟩

/-- **The transfer keeps every buffer's words**: it reads every thread's
buffer address, every VSpace root and the machine where it found them. -/
theorem receiveTransferCaps_wordReads
    (req : Option (SeLe4n.ObjId × Array SeLe4n.CPtr × Nat))
    (endpointId : Option SeLe4n.ObjId) (target? : Option (TCB × Option CSpaceAddr))
    {B Z Z' : SystemState} {r : CapTransferSummary} (hK : KeepsWordReads B Z)
    (h : receiveTransferCaps req endpointId target? Z = .ok (r, Z')) : KeepsWordReads B Z' := by
  unfold receiveTransferCaps at h
  rcases req with _ | ⟨root, addrs, depth⟩
  · cases h; exact hK
  · simp only [] at h
    split at h
    · cases h; exact hK
    · rcases target? with _ | ⟨rtcb, slot?⟩
      · cases h; exact hK
      · exact ipcUnwrapCapsLoop_rel (fun a b => ∀ B, KeepsWordReads B b → KeepsWordReads B a)
          (fun _ _ h => h) (fun _ _ _ h1 h2 B h => h1 B (h2 B h)) _ _ rtcb
          (fun s i b B h => h.recordUnwrappedBadge rtcb i b) _ _ _ _ _ _ _
          (fun _ _ _ _ _ _ hT B h => h.ipcTransferSingleCap _ _ _ hT) h B hK

/-- The transfer's state reads every buffer's words as the state it ran on. -/
theorem ipcWordReadsAgree_receiveTransferCaps
    (req : Option (SeLe4n.ObjId × Array SeLe4n.CPtr × Nat))
    (endpointId : Option SeLe4n.ObjId) (target? : Option (TCB × Option CSpaceAddr))
    {Z Z' : SystemState} {r : CapTransferSummary} (hNo : Z.objects.noResizeDue)
    (h : receiveTransferCaps req endpointId target? Z = .ok (r, Z')) : ipcWordReadsAgree Z' Z :=
  (receiveTransferCaps_wordReads req endpointId target? (KeepsWordReads.refl Z hNo) h).2

/-! ## What a routed long frame asks for -/

/-- **A routed capability-carrying frame of more than four words whose overflow
slots all read decodes** to the inline words and then those slots' words
(`longMessageDecode`). -/
theorem blockedSenderDecode_routedLong (st : SystemState) (tid : SeLe4n.ThreadId) (stcb : TCB)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo) (sid : SyscallId)
    (hRf : stcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .transferring sid capAddr mi)
    (hGt : 4 < mi.length)
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w) :
    blockedSenderDecode st tid stcb = .ok (longMessageDecode sid st tid rf capAddr mi) := by
  unfold blockedSenderDecode
  rw [hRf]
  exact decodeSyscallArgsFromState_of_routedReplyLong_ok st tid rf capAddr mi sid
    (.inr (.inr ⟨hR, hGt⟩)) hRead

/-- **The request a routed long frame makes**: as a short one's
(`senderFrameCapRequest_routed`), its overflow slots all reading. -/
theorem senderFrameCapRequest_routedLong (st : SystemState) (tid : SeLe4n.ThreadId) (stcb : TCB)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo) (sid : SyscallId)
    (g : Bool) (hRf : stcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .transferring sid capAddr mi)
    (hGt : 4 < mi.length)
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w) :
    senderFrameCapRequest st tid stcb g =
      frameCapRequestOf st stcb (if g then routedExtraCaps rf else 0) := by
  unfold senderFrameCapRequest
  cases g
  · simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true, frameCapRequestOf_zero]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      blockedSenderDecode_routedLong st tid stcb rf capAddr mi sid hRf hR hGt hRead,
      routedExtraCaps_eq hR]
    rfl

theorem sendCapRequest_routedLong (st : SystemState) (epId : SeLe4n.ObjId)
    (tid r : SeLe4n.ThreadId) (stcb : TCB) (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr)
    (mi : MessageInfo) (sid : SyscallId) (b : Option SeLe4n.Badge) (g : Bool)
    (hRecv : (st.getEndpoint? epId).bind (·.receiveQ.head) = some r)
    (hS : st.getTcb? tid = some stcb) (hRf : stcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .transferring sid capAddr mi)
    (hGt : 4 < mi.length)
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w) :
    sendCapRequest st epId tid (.frame b g) =
      frameCapRequestOf st stcb (if g then routedExtraCaps rf else 0) := by
  unfold sendCapRequest
  rw [hRecv]
  simp only [hS]
  exact senderFrameCapRequest_routedLong st tid stcb rf capAddr mi sid g hRf hR hGt hRead

/-- **The message a routed long capability-carrying frame sends**: its inline
words, then the words its IPC buffer holds (`longSendMessage`). -/
theorem routedLongTransferringMessage (st : SystemState) (tid : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo) (sid : SyscallId)
    (hFrame : ∀ tcb, st.getTcb? tid = some tcb → tcb.registerContext = rf)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .transferring sid capAddr mi)
    (hGt : 4 < mi.length)
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w) :
    ∀ badge grant, (st.getTcb? tid).isSome = true →
      sendPayloadMessage st tid (.frame badge grant) =
        longSendMessage SeLe4n.arm64DefaultLayout rf st tid mi.length badge := by
  intro badge grant hS
  obtain ⟨tcb, hT⟩ := Option.isSome_iff_exists.mp hS
  obtain ⟨-, -, hMax, -, -⟩ :=
    decodeSyscallArgsFromState_of_routedTransferring st tid _ _ 32 sid capAddr mi hR
  simp only [sendPayloadMessage, senderFrameDecode, hT,
    blockedSenderDecode_routedLong st tid tcb rf capAddr mi sid (hFrame tcb hT) hR hGt hRead,
    senderFrameMessage]
  exact longMessageDecode_message sid st tid rf capAddr mi badge (by omega) hMax

/-! ## The long frame, with the transfer's report -/

/-- **A long delivery's last write, with the transfer's report**: the frame,
its message-info word carrying the report and the overflow words the
receiver's buffer takes, then those words copied from the sender's buffer
(`deliverLongSendFrame`).  The report comes first, so it is read before the
state is handed over. -/
@[noinline] def deliverLongCapsFrame (capInfo : Nat) (Y : SystemState) (r : SeLe4n.ThreadId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (s : SeLe4n.ThreadId) (badgeWord : SeLe4n.Badge) (badged : Bool) : SystemState :=
  deliverLongSendFrame Y r layout rf len s badgeWord badged capInfo

/-- **The in-place long delivery with a report is the specification's stage**
of the long message with that report, its overflow words read in a state `Y`
that reads every buffer's words as the delivery's own does. -/
theorem deliverLongCapsFrame_eq (Z Y : SystemState) (r s : SeLe4n.ThreadId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (capInfo : Nat) (hNo : Z.objects.noResizeDue)
    (hA : ipcWordReadsAgree Z Y) (hSize : layout.msgRegs.size = 4) (hLen : 4 ≤ len) :
    deliverLongCapsFrame capInfo Z r layout rf len s badgeWord badged =
      Architecture.stageDeliveredMessage (Z.mapTcbInPlace r (holdMessage
        (longSendMessage layout rf Y s len (SeLe4n.Badge.opt badgeWord badged)))) r capInfo :=
  deliverLongSendFrame_eq Z Y r s layout rf len badgeWord badged capInfo hNo hA hSize hLen

/-! ## The send -/

/-- **The send rendezvous that transfers capabilities, of more than four
words, delivered**: the receiver woken without the message, the transfer in
place, then the frame with the transfer's report and the overflow words copied
from the sender `s`'s buffer.  The sender and the receiver enter as the words
the transfer reads of them (`capTransferK`), read before the rendezvous. -/
@[noinline] def performSendCapsDeliveredLong (st : SystemState) (endpointId : SeLe4n.ObjId)
    (r : SeLe4n.ThreadId) (nextCode : Nat)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (s : SeLe4n.ThreadId) (badgeWord : SeLe4n.Badge) (badged : Bool) (core : Concurrency.CoreId)
    (sv : SeLe4n.ObjId) (sb : SeLe4n.VAddr) (sroot : SeLe4n.ObjId) (count : Nat)
    (rv : SeLe4n.ObjId) (rb : SeLe4n.VAddr) (rroot : SeLe4n.ObjId) : SystemState :=
  let X := (wakeThread (storeSendRendezvousReady st endpointId r nextCode) r core).1
  capTransferK X endpointId sv sb sroot count rv rb rroot fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
    deliverLongCapsFrame
      (capStepsInfo endpointId true x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl X 0 n free 0 0)
      (capStepsApply endpointId true rv rb x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n free X)
      r layout rf len s badgeWord badged

/-- **The staged long send rendezvous that transfers capabilities is the
delivered one**: the specification's transfer after the rendezvous, then the
woken receiver's stage of the long message with the transfer's report. -/
theorem sendRendezvousCaps_eq_deliveredLong (st : SystemState) (endpointId : SeLe4n.ObjId)
    (r : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (sender : SeLe4n.ThreadId) (badgeWord : SeLe4n.Badge) (badged : Bool)
    (core : Concurrency.CoreId) (stcb rt : TCB) (count : Nat)
    (hNo : st.objects.noResizeDue) (hSize : layout.msgRegs.size = 4) (hLen : 4 ≤ len) :
    (match receiveTransferCaps (frameCapRequestOf st stcb count) (some endpointId)
        (capTargetOf st rt)
        (wakeThread (storeSendRendezvous st endpointId r next
          (longSendMessage layout rf st sender len (SeLe4n.Badge.opt badgeWord badged))) r
          core).1 with
      | .ok (s, st'') =>
        Architecture.stageWokenDelivery (clearWokenReceiverStashPure (some r) st'') (some r)
          s.capInfo
      | .error _ => st) =
      performSendCapsDeliveredLong st endpointId r (ThreadId.optCode next) layout rf len sender
        badgeWord badged core stcb.vspaceRoot stcb.ipcBuffer stcb.cspaceRoot count rt.vspaceRoot
        rt.ipcBuffer rt.cspaceRoot := by
  have hNo0 := storeSendRendezvousWith_noResizeDue st endpointId r next ipcReadyTcb hNo
  have hNoY := wakeThread_noResizeDue _ r core hNo0
  have hAY0 : ipcBufferReadsAgree
      (wakeThread (storeSendRendezvousWith st endpointId r next ipcReadyTcb) r core).1 st :=
    (ipcBufferReadsAgree_wakeThread _ r core hNo0).trans
      (ipcBufferReadsAgree_storeSendRendezvousWith st endpointId r next ipcReadyTcb
        (fun _ => ⟨rfl, rfl⟩) hNo)
  have hA := ipcBufferReadsAgree_sendWoken st endpointId r (ThreadId.optCode next) core hNo
  unfold performSendCapsDeliveredLong
  have hK := capTransferK_eq
    (wakeThread (storeSendRendezvousReady st endpointId r (ThreadId.optCode next)) r core).1
    endpointId stcb count rt
    (fun i Y => deliverLongCapsFrame i Y r layout rf len sender badgeWord badged)
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
    at hNoY hAY0
  rw [receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _) r _ _ _ Y0 hNoY,
    receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _) r _ _ _ Y0 hNoY]
  obtain ⟨s, Y1, hT⟩ := receiveTransferCaps_ok (frameCapRequestOf st stcb count) (some endpointId)
    (capTargetOf st rt) Y0
  have hNo1 := receiveTransferCaps_noResizeDue _ _ _ Y0 Y1 s hNoY hT
  have hAY1 : ipcWordReadsAgree Y1 st :=
    (ipcWordReadsAgree_receiveTransferCaps _ _ _ hNoY hT).trans hAY0.words
  rw [hT]
  simp only [mapStepState]
  have hD : ∀ M : IpcMessage,
      TCB.withMessageSlots id (fun _ => some M) (fun _ : Nat => 0) =
        holdMessage M ∘ TCB.withMessageSlots id (fun _ => none) (fun _ => 0) := fun _ => rfl
  rw [clearWokenReceiverStashPure_mapTcbInPlace _ _ _ (fun _ => rfl),
    hD, ← SystemState.mapTcbInPlace_mapTcbInPlace,
    Architecture.stageWokenDelivery_some]
  exact (deliverLongCapsFrame_eq
    (Y1.mapTcbInPlace r (TCB.withMessageSlots id (fun _ => none) fun _ => 0)) st r sender layout
    rf len badgeWord badged s.capInfo ((SystemState.mapTcbInPlace_noResizeDue _ _ _).mpr hNo1)
    ((ipcBufferReadsAgree_mapTcbInPlace Y1 r (TCB.withMessageSlots id (fun _ => none) fun _ => 0)
      (fun _ => ⟨rfl, rfl⟩)).words.trans hAY1)
    hSize hLen).symm

/-! ## The call -/

/-- **A long call's last writes, with the transfer's report**: the receiver's
priority walk on the state the transfer left, then the long frame carrying the
report and the caller `s`'s overflow words.  The report comes first, so it is
read before the state is handed over. -/
@[noinline] def finishCallCapsLong (capInfo : Nat) (Y : SystemState) (r : SeLe4n.ThreadId)
    (core : Concurrency.CoreId) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (s : SeLe4n.ThreadId) (badgeWord : SeLe4n.Badge)
    (badged : Bool) : SystemState :=
  deliverLongCapsFrame capInfo (PriorityInheritance.propagatePipChainCrossCore Y r core).1 r layout
    rf len s badgeWord badged

/-- **The call rendezvous that transfers capabilities, of more than four
words, delivered**: the receiver woken without the message and the caller
blocked on the reply, the transfer in place, the priority walk, then the long
frame with the transfer's report. -/
@[noinline] def performCallCapsDeliveredLong (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (nextCode : Nat) (rid : SeLe4n.ReplyId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (core : Concurrency.CoreId)
    (sv : SeLe4n.ObjId) (sb : SeLe4n.VAddr) (sroot : SeLe4n.ObjId) (count : Nat)
    (rv : SeLe4n.ObjId) (rb : SeLe4n.VAddr) (rroot : SeLe4n.ObjId) : SystemState :=
  let X := storeCallRendezvousReady st endpointId caller r nextCode rid core
  capTransferK X endpointId sv sb sroot count rv rb rroot fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
    finishCallCapsLong
      (capStepsInfo endpointId true x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl X 0 n free 0 0)
      (capStepsApply endpointId true rv rb x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n free X)
      r core layout rf len caller badgeWord badged

/-- **The staged long call rendezvous that transfers capabilities is the
delivered one**: the specification's transfer after the rendezvous, the
priority walk, then the woken receiver's stage of the long message with the
transfer's report. -/
theorem callRendezvousCaps_eq_deliveredLong (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (core : Concurrency.CoreId) (ctcb rt : TCB)
    (count : Nat) (hNo : st.objects.noResizeDue) (hNe : caller ≠ r)
    (hSize : layout.msgRegs.size = 4) (hLen : 4 ≤ len) :
    (match receiveTransferCaps (frameCapRequestOf st ctcb count) (some endpointId)
        (capTargetOf st rt)
        (storeCallRendezvous st endpointId caller r next rid
          (longSendMessage layout rf st caller len (SeLe4n.Badge.opt badgeWord badged)) core) with
      | .ok (s, st'') =>
        Architecture.stageWokenDelivery
          (PriorityInheritance.propagatePipChainCrossCore st'' r core).1 (some r) s.capInfo
      | .error _ => st) =
      performCallCapsDeliveredLong st endpointId caller r (ThreadId.optCode next) rid layout rf len
        badgeWord badged core ctcb.vspaceRoot ctcb.ipcBuffer ctcb.cspaceRoot count rt.vspaceRoot
        rt.ipcBuffer rt.cspaceRoot := by
  have hNoX := storeCallRendezvousReady_noResizeDue st endpointId caller r
    (ThreadId.optCode next) rid core hNo
  have hA := ipcBufferReadsAgree_storeCallRendezvousReady st endpointId caller r
    (ThreadId.optCode next) rid core hNo
  unfold performCallCapsDeliveredLong
  have hK := capTransferK_eq
    (storeCallRendezvousReady st endpointId caller r (ThreadId.optCode next) rid core)
    endpointId ctcb count rt
    (fun i Y => finishCallCapsLong i Y r core layout rf len caller badgeWord badged)
  simp only at hK
  rw [hK, hA.frameCapRequestOf, hA.capTargetOf,
    storeCallRendezvous_eq_hold _ _ _ _ _ _ _ _ hNo hNe]
  generalize storeCallRendezvousReady st endpointId caller r (ThreadId.optCode next) rid core = X
    at hNoX hA
  rw [receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _) r _ _ _ X hNoX]
  obtain ⟨s, Y1, hT⟩ := receiveTransferCaps_ok (frameCapRequestOf st ctcb count)
    (some endpointId) (capTargetOf st rt) X
  have hNo1 := receiveTransferCaps_noResizeDue _ _ _ X Y1 s hNoX hT
  have hAY1 : ipcWordReadsAgree Y1 st :=
    (ipcWordReadsAgree_receiveTransferCaps _ _ _ hNoX hT).trans hA.words
  rw [hT]
  simp only [mapStepState]
  rw [propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNo1, Architecture.stageWokenDelivery_some]
  exact (deliverLongCapsFrame_eq (PriorityInheritance.propagatePipChainCrossCore Y1 r core).1 st r
    caller layout rf len badgeWord badged s.capInfo
    (propagatePipChainCrossCore_noResizeDue _ _ _ hNo1)
    ((ipcBufferReadsAgree_propagatePipChainCrossCore Y1 r core hNo1).words.trans hAY1)
    hSize hLen).symm

end SeLe4n.Kernel
