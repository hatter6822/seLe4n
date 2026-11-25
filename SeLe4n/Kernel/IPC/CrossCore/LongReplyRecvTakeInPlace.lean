-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvTakeInPlace
import SeLe4n.Kernel.IPC.CrossCore.LongReplyRecvFrame

/-!
# The long reply-receive whose receive leg meets a waiting sender, in place

The long form of `ReplyRecvTakeInPlace`: seL4-MCS's `handleReplyRecv` with a
reply of more than four words runs `doReplyTransfer` (the frame into the
caller's saved registers, the overflow words copied into the caller's buffer,
`copyMRs`) and then `receiveIPC`, which takes a sender already queued on the
endpoint.  The specification runs the same order
(`endpointReplyRecvAnsweringOnCore`).

The caller's delivery copies the replier's overflow words, read from the
replier's buffer; the take writes the replier's TCB (its state and its held
message), never its buffer slot, its buffer address, a frame or the machine.
So the long delivery commutes past the replier's writes
(`deliverLongReplyRecvFrame_mapTcbInPlace`) and reads, after the take, the
words it read before it (`ipcBufferReadsAgree`).  The in-place performer is
proven equal to the specification (`replyRecvOnCore_take_deliveredLong`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

/-! ## The long delivery past another thread's write -/

theorem overflowSlotsFrom_congr {S S' : SystemState} (h : ipcWordReadsAgree S' S)
    (r : SeLe4n.ThreadId) : ∀ (i n : Nat), overflowSlotsFrom S' r i n = overflowSlotsFrom S r i n
  | _, 0 => rfl
  | i, n + 1 => by
    simp only [overflowSlotsFrom, h.overflowSlotOf r i, overflowSlotsFrom_congr h r (i + 1) n]

/-- **The overflow copy commutes past a TCB write that keeps every buffer
read**: the copy records machine writes, the TCB write rewrites one object. -/
theorem overflowCopyStore_mapTcbInPlace (r s t : SeLe4n.ThreadId) (g : TCB → TCB)
    (hg : ∀ x, (g x).spaceCells[2] = x.spaceCells[2] ∧ (g x).ipcBuffer = x.ipcBuffer) :
    ∀ (n i : Nat) (S : SystemState),
      overflowCopyStore (S.mapTcbInPlace t g) r s i n = (overflowCopyStore S r s i n).mapTcbInPlace t g
  | 0, _, _ => rfl
  | n + 1, i, S => by
    have hA := (ipcBufferReadsAgree_mapTcbInPlace S t g hg).words
    simp only [overflowCopyStore, hA.overflowSlotOf r i, hA.overflowWordAt s i]
    split
    · exact overflowCopyStore_mapTcbInPlace r s t g hg n (i + 1)
        (S.recordPhysicalWrite _)
    · rfl

/-- **The long delivery to `r` commutes past a write of another thread `t`
that keeps every buffer read.** -/
theorem deliverLongReplyRecvFrame_mapTcbInPlace (X : SystemState) (r s t : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (capInfo : Nat)
    (g : TCB → TCB)
    (hg : ∀ x, (g x).spaceCells[2] = x.spaceCells[2] ∧ (g x).ipcBuffer = x.ipcBuffer)
    (hNe : r ≠ t) :
    deliverLongReplyRecvFrame (X.mapTcbInPlace t g) r rf len s badge capInfo =
      (deliverLongReplyRecvFrame X r rf len s badge capInfo).mapTcbInPlace t g := by
  have hNe' : t.toObjId ≠ r.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  have hA := (ipcBufferReadsAgree_mapTcbInPlace X t g hg).words
  unfold deliverLongReplyRecvFrame deliverLongSendFrame
  rw [SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hNe']
  cases X.getTcb? r with
  | none => rfl
  | some x =>
    simp only []
    split
    · rw [overflowSlotsFrom_congr hA r 0 (len - 4),
        SystemState.mapTcbInPlace_swap _ g _ (fun e => absurd e hNe),
        overflowCopyStore_mapTcbInPlace r s t g hg]
    · unfold holdLongSendMessage longSendMessage
      rw [hA.overflowRegsFrom s 0 (len - 4),
        SystemState.mapTcbInPlace_swap _ g _ (fun e => absurd e hNe)]

/-- The overflow copy records machine writes only. -/
theorem overflowCopyStore_objects (r s : SeLe4n.ThreadId) :
    ∀ (n i : Nat) (S : SystemState), (overflowCopyStore S r s i n).objects = S.objects
  | 0, _, _ => rfl
  | n + 1, i, S => by
    simp only [overflowCopyStore]
    split
    · exact overflowCopyStore_objects r s n (i + 1) _
    · rfl

theorem deliverLongReplyRecvFrame_noResizeDue (X : SystemState) (r : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (s : SeLe4n.ThreadId) (badge : Option SeLe4n.Badge)
    (capInfo : Nat) (hNo : X.objects.noResizeDue) :
    (deliverLongReplyRecvFrame X r rf len s badge capInfo).objects.noResizeDue := by
  unfold deliverLongReplyRecvFrame deliverLongSendFrame holdLongSendMessage
  split
  · split
    · rw [overflowCopyStore_objects]; exact (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNo
    · exact (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNo
  · exact hNo

/-! ## The take -/

/-- The long take's writes before the server's own frame: the sender popped,
made ready and woken, the server made ready, its priority walk, then the
caller's long frame with the transfer's report and the replier's overflow
words copied into the caller's buffer (`deliverLongReplyRecvFrame`). -/
@[noinline] def replyRecvTakeLegsLong (capInfo : Nat) (Y : SystemState)
    (c tid s : SeLe4n.ThreadId) (epId : SeLe4n.ObjId) (nextCode : Nat) (core : CoreId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) : SystemState :=
  let W := (wakeThread ((storePopHead Y epId false s (ThreadId.ofOptCode nextCode)).updateTcb s
    receiverReady) s core).1
  let Z := (PriorityInheritance.propagatePipChainCrossCore (W.updateTcb tid receiverReady) tid
    core).1
  deliverLongReplyRecvFrame Z c rf len tid badge capInfo

/-- **The long take's tail stages the caller's held reply and the server's
message as frames** (the long form of `replyRecvTakeFrame_staged`): the caller's
long frame, its overflow words read in `st0`, whose buffers `Y` reads alike. -/
theorem replyRecvTakeFrame_stagedLong (st0 Y : SystemState) (c tid s : SeLe4n.ThreadId)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (sTcb : TCB) (core : CoreId)
    (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (capInfo : Nat) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hNo : Y.objects.noResizeDue) (hAY : ipcWordReadsAgree Y st0) (hNe : tid ≠ c) (hSC : s ≠ c)
    (hLen : 4 ≤ len)
    (hE : (Y.mapTcbInPlace c (holdMessage
      { registers := longReplyRecvRegs rf st0 tid len, badge := badge })).objects[epId]? =
        some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : (Y.mapTcbInPlace c (holdMessage
      { registers := longReplyRecvRegs rf st0 tid len, badge := badge })).objects[s.toObjId]? =
        some (.tcb sTcb))
    (hG : receiveTakesInPlace (Y.mapTcbInPlace c (holdMessage
      { registers := longReplyRecvRegs rf st0 tid len, badge := badge })) epId tid s sTcb
        = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext) SeLe4n.arm64DefaultLayout
      sTcb.registerContext 32 = .send capAddr mi)
    (hF : sTcb.ipcFaultSend = false) :
    Architecture.stageDeliveredMessage (Architecture.stageDeliveredMessage
          (PriorityInheritance.propagatePipChainCrossCore
            ((wakeThread ((storePopHead (Y.mapTcbInPlace c (holdMessage
                { registers := longReplyRecvRegs rf st0 tid len, badge := badge }))
                epId false s sTcb.queueNext).updateTcb s receiverReady) s core).1.updateTcb tid
              (callReceiverTcb (blockedSenderMessage (storePopHead (Y.mapTcbInPlace c (holdMessage
                { registers := longReplyRecvRegs rf st0 tid len, badge := badge }))
                epId false s sTcb.queueNext) s sTcb))) tid core).1 c capInfo) tid 0 =
      writeTakerFrame
        (replyRecvTakeLegsLong capInfo Y c tid s epId sTcb.queueNextCode core rf len badge) tid
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x0
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x1
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x2
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x3
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x4
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x5 := by
  generalize hM : ({ registers := longReplyRecvRegs rf st0 tid len, badge := badge } :
    IpcMessage) = m at hE hT hG
  generalize hS2 : Y.mapTcbInPlace c (holdMessage m) = S2 at hE hT hG
  have hG' := hG
  simp only [receiveTakesInPlace, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hG'
  obtain ⟨⟨⟨⟨⟨⟨⟨hSG, _⟩, hRS⟩, hRN⟩, _⟩, _⟩, hRT⟩, _⟩ := hG'
  have hSG' := hSG
  simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hSG'
  obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hFH⟩, _⟩ := hSG'
  obtain ⟨rt, hRTo⟩ := Option.isSome_iff_exists.mp hRT
  have hRo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hRTo
  have hNeER : epId ≠ tid.toObjId := fun h => by rw [h, hRo] at hE; cases hE
  have hNeSR : s.toObjId ≠ tid.toObjId := fun h =>
    hRS (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  have hNxR : ∀ n, sTcb.queueNext = some n → n.toObjId ≠ tid.toObjId := fun n hn h => by
    rw [hn] at hRN
    simp only [bne_iff_ne, ne_eq] at hRN
    exact hRN (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  obtain ⟨_, hFr⟩ := popHead_inPlace S2 epId false ep s sTcb hE
    (by simp only [Bool.false_eq_true, ↓reduceIte]; exact hH) hT hSG
  have hFH1 := (hFr.keepsFinds s.toObjId).trans hFH
  have hO1r := (hFr.other _ hNeER hNeSR hNxR).trans hRo
  have hT2s := updateTcb_getTcb?_self_of_findsInPlace receiverReady hFr.head_tcb hFH1
  have hA3 := enqueueRunnableOnCore_agree_of_findsInPlace
    ((storePopHead S2 epId false s sTcb.queueNext).updateTcb s receiverReady)
    (determineTargetCore ((storePopHead S2 epId false s sTcb.queueNext).updateTcb s receiverReady) s)
    s _ hT2s rfl (by rw [updateTcb_findsInPlace _ hFr.head_tcb hFH1]; exact hFH1)
  have hO2r := (updateTcb_get?_ne_of_findsInPlace receiverReady hFr.head_tcb hFH1 hNeSR).trans hO1r
  obtain ⟨rt3, hO3r, _⟩ := hA3.get_tcb hO2r
  have hW3r : (wakeThread ((storePopHead S2 epId false s sTcb.queueNext).updateTcb s receiverReady)
      s core).1.getTcb? tid = some rt3 := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO3r
  have hMsg := (blockedSender_of_routedSend (storePopHead S2 epId false s sTcb.queueNext) s sTcb
    capAddr mi hR hF).2
  generalize blockedSenderMessage (storePopHead S2 epId false s sTcb.queueNext) s sTcb = msgS
    at hMsg
  subst hS2
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  have hST : s ≠ tid := fun e => hRS e.symm
  have hNoPY := storePopHead_noResizeDue Y epId false s sTcb.queueNext hNo
  have hNoU := updateTcb_noResizeDue _ s receiverReady hNoPY
  have hNoWY := wakeThread_noResizeDue _ s core hNoU
  have hNoWr := updateTcb_noResizeDue _ tid receiverReady hNoWY
  have hNoZ := propagatePipChainCrossCore_noResizeDue _ tid core hNoWr
  have hNoZs : (SystemState.mapTcbInPlace (PriorityInheritance.propagatePipChainCrossCore
      ((wakeThread ((storePopHead Y epId false s sTcb.queueNext).updateTcb s receiverReady) s
        core).1.updateTcb tid receiverReady) tid core).1 tid (holdMessage msgS)).objects.noResizeDue :=
    (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoZ
  rw [storePopHead_msg c _ _ _ Y epId false s sTcb.queueNext hNo] at hW3r ⊢
  rw [updateTcb_msg c _ _ _ _ s receiverReady hNoPY (fun h => absurd h hSC)] at hW3r ⊢
  rw [wakeThread_msg c _ _ _ _ s core hNoU] at hW3r ⊢
  dsimp only at hW3r ⊢
  rw [SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hCT] at hW3r
  unfold writeTakerFrame replyRecvTakeLegsLong
  dsimp only
  rw [← TCB.optCode_queueNext, SeLe4n.ThreadId.ofOptCode_optCode]
  have hAW : ipcWordReadsAgree (wakeThread ((storePopHead Y epId false s sTcb.queueNext).updateTcb
      s receiverReady) s core).1 st0 :=
    ((ipcBufferReadsAgree_wakeThread _ s core hNoU).trans
      ((ipcBufferReadsAgree_updateTcb _ s receiverReady (fun _ => ⟨rfl, rfl⟩) hNoPY).trans
        (ipcBufferReadsAgree_storePopHead Y epId false s sTcb.queueNext hNo))).words.trans hAY
  generalize (wakeThread ((storePopHead Y epId false s sTcb.queueNext).updateTcb s receiverReady) s
    core).1 = W at hW3r hNoWY hNoWr hNoZ hNoZs hAW ⊢
  have hNoWrc : ((W.updateTcb tid receiverReady).mapTcbInPlace c (holdMessage m)).objects.noResizeDue :=
    (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoWr
  rw [updateTcb_msg c _ _ _ _ tid (callReceiverTcb msgS) hNoWY (fun h => absurd h hNe),
    SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoWY, ← holdMessage_receiverReady,
    ← SystemState.mapTcbInPlace_mapTcbInPlace, ← SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoWY,
    SystemState.mapTcbInPlace_swap _ (holdMessage msgS) (holdMessage m)
      (fun h => absurd h (fun e => hNe e.symm)),
    propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoWrc,
    propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoWr,
    SystemState.mapTcbInPlace_swap _ (holdMessage m) (holdMessage msgS) (fun h => absurd h hNe)]
  have hAZ : ipcWordReadsAgree (PriorityInheritance.propagatePipChainCrossCore
      (W.updateTcb tid receiverReady) tid core).1 st0 :=
    ((ipcBufferReadsAgree_propagatePipChainCrossCore _ tid core hNoWr).trans
      (ipcBufferReadsAgree_updateTcb _ tid receiverReady (fun _ => ⟨rfl, rfl⟩) hNoWY)).words.trans
      hAW
  have hAZs := (ipcBufferReadsAgree_mapTcbInPlace _ tid (holdMessage msgS)
    (fun _ => ⟨rfl, rfl⟩)).words.trans hAZ
  rw [← hM, ← deliverLongReplyRecvFrame_eq _ st0 c tid rf len badge capInfo hNoZs hAZs hLen,
    deliverLongReplyRecvFrame_mapTcbInPlace _ c tid tid rf len badge capInfo (holdMessage msgS)
      (fun _ => ⟨rfl, rfl⟩) (fun e => hNe e.symm)]
  have hWr : (W.updateTcb tid receiverReady).getTcb? tid = some (receiverReady rt3) := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoWY, SystemState.mapTcbInPlace_getTcb?_self,
      hW3r]; rfl
  obtain ⟨x, hX, hXs⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core hNoWr tid _ hWr
  generalize (PriorityInheritance.propagatePipChainCrossCore (W.updateTcb tid receiverReady) tid
    core).1 = Z at hX hNoZ hNoZs hAZ hAZs ⊢
  have hNoD := deliverLongReplyRecvFrame_noResizeDue Z c rf len tid badge capInfo hNoZ
  have hDr := (deliverLongReplyRecvFrame_getTcb?_ne Z c tid tid rf len badge capInfo hCT).trans hX
  generalize deliverLongReplyRecvFrame Z c rf len tid badge capInfo = D at hDr hNoD ⊢
  have hSzS : msgS.registers.size ≤ 4 := by
    rw [hMsg]
    simp only [Architecture.regMessageBody_size, Architecture.regMessageLength]
    have : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
    omega
  rw [stageDeliveredMessage_holdMessage _ _ _ hNoD hSzS, hMsg,
    Architecture.returnFrameOfMessage_regMessageBody]
  unfold writeDeliveredFrameIfReady
  rw [hDr]
  dsimp only
  rw [if_pos (by rw [hXs]; rfl)]

/-- **The long reply-receive meeting a waiting sender, its reply transferring
nothing, delivered**: the reply's writes, the take, the server's priority walk,
then the caller's long frame and its overflow words, and the server's frame, its six
words read from the sender's saved registers before any write. -/
@[noinline] def performReplyRecvTakeLegsLong (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId) (nextCode : Nat)
    (core : CoreId) (rf : SeLe4n.RegisterFile)
    (len : Nat) (badge : Option SeLe4n.Badge) : SystemState :=
  replyRecvTakeLegsLong 0 (receiveReturnSchedContextFast true (storeReplyRendezvousReady st c tid rid)
    tid.val) c tid s epId nextCode core rf len badge

/-- The inert take, the legs (`performReplyRecvTakeLegs`) and then the
server's frame (`writeTakerFrame`), each out of line so the arm releases the
server's register file between them. -/
@[inline] def performReplyRecvTakeDeliveredLong (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId) (nextCode : Nat)
    (core : CoreId) (rf : SeLe4n.RegisterFile)
    (len : Nat) (badge : Option SeLe4n.Badge) (w0 w1 w2 w3 w4 w5 : UInt64) : SystemState :=
  writeTakerFrame (performReplyRecvTakeLegsLong st c tid rid epId s nextCode core rf len badge)
    tid w0 w1 w2 w3 w4 w5

/-- **The long reply-receive meeting a waiting sender, its reply transferring
nothing, is the specification's**: under the reply's guard, a reply of more
than four words transferring no capability (`replyTransferInert`), and a sender `s`
at the head of the send queue blocked by a routed capability-free send, not
delivering a fault, whose take writes only its slots (every check read on the
pre-state), the checked arm's result is `performReplyRecvTakeDelivered`. -/
theorem replyRecvOnCore_take_deliveredLong (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (grant : Bool)
    (core : CoreId) (ct : TCB) (ep0 : SeLe4n.ObjId) (rp : Reply) (ep : Endpoint)
    (s : SeLe4n.ThreadId) (sTcb : TCB) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hLen : 5 ≤ len)
    (hSzL : ¬ (longReplyRecvRegs rf st tid len).size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hRO : ct.replyObject = some rid)
    (hG : replyWakesInPlace st c ct rid = true) (hNe : tid ≠ c)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hInert : replyTransferInert st tid ct grant = true)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hGt : receiveTakesInPlace st epId tid s sTcb = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext) SeLe4n.arm64DefaultLayout
      sTcb.registerContext 32 = .send capAddr mi)
    (hF : sTcb.ipcFaultSend = false) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := longReplyRecvRegs rf st tid len, badge := badge } grant core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvTakeDeliveredLong st c tid rid epId s sTcb.queueNextCode core rf
        len badge
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x0
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x1
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x2
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x3
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x4
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x5) := by
  have hNo := replyWakesInPlace_noResizeDue hG
  have hFC : st.objects.findsInPlace c.toObjId = true := by
    simp only [replyWakesInPlace, Bool.and_eq_true] at hG
    exact hG.1.1.1.2
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hSz := hSzL
  obtain ⟨hE1, sTcb1, hS1, hK, hG1⟩ := storeReplyRendezvous_takeGuard st c tid rid
    { registers := longReplyRecvRegs rf st tid len, badge := badge } ct rp epId ep s
    sTcb hNo hT hFC hRp hE hS hSC hGt
  have hXf := replyTransferCaps_of_inert st tid c grant ct hTc hInert
    (storeReplyRendezvous st c tid rid
      { registers := longReplyRecvRegs rf st tid len, badge := badge })
  have hR1 : Architecture.RegisterDecode.registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout sTcb1.registerContext) SeLe4n.arm64DefaultLayout
      sTcb1.registerContext 32 = .send capAddr mi := by rw [hK.regs]; exact hR
  obtain ⟨hE2, sTcb2, hS2, hK2, hG2⟩ := receiveReturnSchedContext_takeGuard true _ tid
    (storeReplyRendezvous_noResizeDue st c tid rid _ hNo) hE1 hS1 hG1
  have hKt := hK2.trans hK
  have hR2 : Architecture.RegisterDecode.registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout sTcb2.registerContext) SeLe4n.arm64DefaultLayout
      sTcb2.registerContext 32 = .send capAddr mi := by rw [hKt.regs]; exact hR
  have hF2 : sTcb2.ipcFaultSend = false := by rw [hKt.faultSend]; exact hF
  rw [replyRecvOnCore_take_transfer st epId tid c rid
    { registers := longReplyRecvRegs rf st tid len, badge := badge } grant core ct ep0 ep s capAddr mi hSz hT
    hIpc hRO hG hH hXf hE2 hS2 hG2 hR2 hF2]
  dsimp only
  rw [CapTransferSummary.capInfo_empty]
  have hNoX := storeReplyRendezvousReady_noResizeDue st c tid rid hNo
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo,
    receiveReturnSchedContext_msg c id _ id true _ tid hNoX hNe.symm] at hE2 hS2 hG2 ⊢
  have hAY := (ipcBufferReadsAgree_receiveReturnSchedContext true _ tid hNoX).trans
    (ipcBufferReadsAgree_storeReplyRendezvousReady st c tid rid hNo)
  rw [replyRecvTakeFrame_stagedLong st _ c tid s epId ep sTcb2 core rf len badge 0 capAddr mi
    (receiveReturnSchedContext_noResizeDue true _ tid hNoX) hAY.words hNe hSC (by omega) hE2 hH hS2 hG2
    hR2 hF2,
    hKt.queueNext, hKt.regs, hKt.ipcBadgeView]
  unfold performReplyRecvTakeDeliveredLong performReplyRecvTakeLegsLong
  rw [receiveReturnSchedContextFast_eq]

/-- **The long reply-receive meeting a waiting sender, its reply leg transferring,
delivered**: the reply's writes, the transfer in place on no endpoint, the take,
the server's priority walk, then the caller's long frame with the transfer's
report and its overflow words, and the server's frame.  The replier and the caller
enter as the words the transfer reads of them, the sender as its successor and
the six words of its frame, all read before the reply's writes. -/
@[noinline] def performReplyRecvTakeCapsLegsLong (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId) (nextCode : Nat)
    (core : CoreId) (rf : SeLe4n.RegisterFile)
    (len : Nat) (badge : Option SeLe4n.Badge)
    (sv : Option Capability) (sb : SeLe4n.VAddr) (sroot : Option Capability) (count : Nat)
    (rv : Option Capability) (rb : SeLe4n.VAddr) (rroot : Option Capability) : SystemState :=
  let X := storeReplyRendezvousReady st c tid rid
  capTransferK X c.toObjId sv sb sroot count rv rb rroot
    fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
    replyRecvTakeLegsLong (capStepsInfo c.toObjId false x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl X 0 n free 0 0)
      (receiveReturnSchedContextFast true
        (capStepsApply c.toObjId false rv rb x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n free X) tid.val)
      c tid s epId nextCode core rf len badge

/-- The installing take, its legs (`performReplyRecvTakeCapsLegs`) and then the
server's frame (`writeTakerFrame`), each out of line so the arm releases the
server's register file between them. -/
@[inline] def performReplyRecvTakeCapsDeliveredLong (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId) (nextCode : Nat)
    (core : CoreId) (rf : SeLe4n.RegisterFile)
    (len : Nat) (badge : Option SeLe4n.Badge) (w0 w1 w2 w3 w4 w5 : UInt64)
    (sv : Option Capability) (sb : SeLe4n.VAddr) (sroot : Option Capability) (count : Nat)
    (rv : Option Capability) (rb : SeLe4n.VAddr) (rroot : Option Capability) : SystemState :=
  writeTakerFrame (performReplyRecvTakeCapsLegsLong st c tid rid epId s nextCode core rf len
    badge sv sb sroot count rv rb rroot) tid w0 w1 w2 w3 w4 w5

/-- **The long reply-receive meeting a waiting sender, its reply leg transferring,
is the specification's**: under the guard of `replyRecvOnCore_take_deliveredLong`
(its inert transfer replaced by a granting replier whose frame asks for `count`
capabilities, `hReq`), the checked arm's result
is `performReplyRecvTakeCapsDeliveredLong`. -/
theorem replyRecvOnCore_take_capsDeliveredLong (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge)
    (core : CoreId) (ct : TCB) (ep0 : SeLe4n.ObjId) (rp : Reply) (ep : Endpoint)
    (s : SeLe4n.ThreadId) (sTcb : TCB) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (stcb : TCB) (count : Nat)
    (hLen : 5 ≤ len)
    (hSzL : ¬ (longReplyRecvRegs rf st tid len).size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hRO : ct.replyObject = some rid)
    (hG : replyWakesInPlace st c ct rid = true) (hNe : tid ≠ c)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hE : st.objects[epId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hGt : receiveTakesInPlace st epId tid s sTcb = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext) SeLe4n.arm64DefaultLayout
      sTcb.registerContext 32 = .send capAddr mi)
    (hF : sTcb.ipcFaultSend = false)
    (hReq : replyCapRequest st tid true = frameCapRequestOf st stcb count) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := longReplyRecvRegs rf st tid len, badge := badge } true core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvTakeCapsDeliveredLong st c tid rid epId s sTcb.queueNextCode core
        rf len badge
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x0
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x1
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x2
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x3
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x4
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x5
        stcb.spaceCells[2] stcb.ipcBuffer stcb.spaceCells[0] count ct.spaceCells[2] ct.ipcBuffer
        ct.spaceCells[0]) := by
  have hNo := replyWakesInPlace_noResizeDue hG
  have hFC : st.objects.findsInPlace c.toObjId = true := by
    simp only [replyWakesInPlace, Bool.and_eq_true] at hG
    exact hG.1.1.1.2
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hTgt : receiverCapTarget? st c = capTargetOf st ct := by
    unfold receiverCapTarget? capTargetOf; rw [hTc]
  have hSz := hSzL
  obtain ⟨hE1, sTcb1, hS1o, hK1, hG1⟩ := storeReplyRendezvous_takeGuard st c tid rid
    { registers := longReplyRecvRegs rf st tid len, badge := badge } ct rp epId ep s
    sTcb hNo hT hFC hRp hE hS hSC hGt
  generalize hMsg : ({ registers := longReplyRecvRegs rf st tid len, badge := badge } :
    IpcMessage) = msg at hE1 hS1o hG1
  have hNoX := storeReplyRendezvousReady_noResizeDue st c tid rid hNo
  have hAX := ipcBufferReadsAgree_storeReplyRendezvousReady st c tid rid hNo
  generalize hX : storeReplyRendezvousReady st c tid rid = X at hNoX hAX
  have hS1 : storeReplyRendezvous st c tid rid msg = X.mapTcbInPlace c (holdMessage msg) := by
    rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo, hX]
  obtain ⟨sm, Y1, hT1⟩ := receiveTransferCaps_ok (frameCapRequestOf st stcb count) none
    (capTargetOf st ct) X
  have hNoY := receiveTransferCaps_noResizeDue _ _ _ X Y1 sm hNoX hT1
  have hXf : replyTransferCaps st tid c true (storeReplyRendezvous st c tid rid msg) =
      .ok (sm, Y1.mapTcbInPlace c (holdMessage msg)) := by
    unfold replyTransferCaps
    rw [hReq, hTgt, hS1, receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _)
      c _ _ _ X hNoX, hT1]
    rfl
  rw [hS1] at hE1 hS1o hG1
  have hFr := (receiveTransferCaps_reply_transferFrame (S := X.mapTcbInPlace c (holdMessage msg))
    ((ipcBufferReadsAgree_mapTcbInPlace X c (holdMessage msg) (fun _ => ⟨rfl, rfl⟩)).trans hAX)
    ((RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoX) c.toObjId stcb ct count
    (by rw [receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _) c _ _ _ X
      hNoX, hT1]; rfl)).1
  obtain ⟨hE2', sTcb2', hS2o', hK2', hG2'⟩ := takeGuard_of_transferFrame hFr hE1 hS1o hG1
  obtain ⟨hE2, sTcb2, hS2o, hK2, hG2⟩ := receiveReturnSchedContext_takeGuard true _ tid
    ((SystemState.mapTcbInPlace_noResizeDue _ _ _).mpr hNoY) hE2' hS2o' hG2'
  have hK := hK2.trans (hK2'.trans hK1)
  have hR2 : Architecture.RegisterDecode.registerRoutedSyscall
      (SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode SeLe4n.arm64DefaultLayout sTcb2.registerContext) SeLe4n.arm64DefaultLayout
      sTcb2.registerContext 32 = .send capAddr mi := by rw [hK.regs]; exact hR
  have hF2 : sTcb2.ipcFaultSend = false := by rw [hK.faultSend]; exact hF
  rw [replyRecvOnCore_take_transfer st epId tid c rid msg true core ct ep0 ep s capAddr mi
    (hMsg ▸ hSz) hT hIpc hRO hG hH hXf hE2 hS2o hG2 hR2 hF2]
  dsimp only
  subst hMsg
  rw [CapTransferSummary.capInfo_empty]
  rw [receiveReturnSchedContext_msg c id _ id true Y1 tid hNoY hNe.symm] at hE2 hS2o hG2 ⊢
  have hAY := (ipcBufferReadsAgree_receiveReturnSchedContext true Y1 tid hNoY).words.trans
    ((ipcWordReadsAgree_receiveTransferCaps _ _ _ hNoX hT1).trans hAX.words)
  rw [replyRecvTakeFrame_stagedLong st _ c tid s epId ep sTcb2 core rf len badge sm.capInfo capAddr
    mi (receiveReturnSchedContext_noResizeDue true Y1 tid hNoY) hAY hNe hSC (by omega) hE2 hH hS2o
    hG2 hR2 hF2, hK.queueNext, hK.regs, hK.ipcBadgeView, ← receiveReturnSchedContextFast_eq]
  have hKl := capTransferK_eq_at X c.toObjId false stcb count ct
    (fun i Y => replyRecvTakeLegsLong i (receiveReturnSchedContextFast true Y tid.val) c tid s
      epId sTcb.queueNextCode core rf len badge)
  simp only [transferEndpoint?, Bool.false_eq_true, ↓reduceIte] at hKl
  rw [hAX.frameCapRequestOf, hAX.capTargetOf, hT1] at hKl
  unfold performReplyRecvTakeCapsDeliveredLong performReplyRecvTakeCapsLegsLong
  rw [hX]
  dsimp only
  rw [hKl]

end SeLe4n.Kernel
