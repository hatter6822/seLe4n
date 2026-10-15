/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.DeliveryCommute
import SeLe4n.Kernel.Architecture.RegisterMessage
import SeLe4n.Kernel.IPC.CrossCore.NotificationSignal

/-!
# The delivered message written straight into the receiver's registers

WS-ZA ZA4.7.  The specification's call and reply wake the receiver holding the
message (`pendingMessage := some msg`), walk the priority chain, and then stage
the message into the receiver's return frame, dropping it
(`Architecture.stageDeliveredMessage`).  A message of at most four words writes
no IPC-buffer word, so its whole delivery is the frame.  The holding write
commutes with every write in between (`DeliveryCommute`), so the fast paths
wake the receiver without the message and write the frame at the end
(`writeDeliveredFrameIfReady`): no message is built and none is held.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

/-- The write that holds a delivered message in the receiver's TCB. -/
abbrev holdMessage (msg : IpcMessage) : TCB → TCB :=
  TCB.withMessageSlots id (fun _ => some msg) id

theorem mapTcbInPlace_eq_self_of_getTcb?_none (st : SystemState) (t : SeLe4n.ThreadId)
    (g : TCB → TCB) (h : st.getTcb? t = none) : st.mapTcbInPlace t g = st := by
  unfold SystemState.mapTcbInPlace
  cases hg : st.objects.get? t.toObjId with
  | none => rw [RHTable.mapValueAt_of_get?_none hg]
  | some o =>
    have hid : KernelObject.mapTcb g o = id o := by
      cases o with
      | tcb u =>
        exfalso
        have : st.getTcb? t = some u :=
          (SystemState.getTcb?_eq_some_iff st t u).mpr
            (by simpa only [SeLe4n.RHTable_getElem?_eq_get?] using hg)
        rw [h] at this; cases this
      | _ => rfl
    rw [RHTable.mapValueAt_congr hg hid, RHTable.mapValueAt_id]

theorem messageOverflowWrites_of_size_le (st : SystemState) (tcb : TCB) (msg : IpcMessage)
    (h : msg.registers.size ≤ 4) : Architecture.messageOverflowWrites st tcb msg = [] := by
  unfold Architecture.messageOverflowWrites
  rw [List.drop_eq_nil_of_le (by simpa using h)]
  rfl

/-- The delivered frame's six words written into a thread's saved registers,
the held message dropped: `TCB.withDeliveredFrame` with the frame's words as
arguments, so the write captures six machine words and no frame record. -/
@[inline] def withFrameWords (w0 w1 w2 w3 w4 w5 : UInt64) (t : TCB) : TCB :=
  let rf := t.registerContext
  let rf' : SeLe4n.RegisterFile :=
    { rf with x0 := w0, x1 := w1, x2 := w2, x3 := w3, x4 := w4, x5 := w5 }
  { t with registerContext := rf', pendingMessage := none }

/-- **The delivered frame, written into a ready thread's saved registers**; a
thread that is not ready is handed to `otherwise`, and a key holding no thread
is left alone.  What the specification's stage does to a thread holding a
message of at most four words (`stageDeliveredMessage_holdMessage`). -/
@[inline] def writeDeliveredFrameIfReady (st : SystemState) (r : SeLe4n.ThreadId)
    (f : Architecture.SyscallReturnFrame) (otherwise : Unit → SystemState) : SystemState :=
  match st.getTcb? r with
  | some t => if t.ipcState = .ready then
        st.mapTcbInPlace r (withFrameWords f.x0 f.x1 f.x2 f.x3 f.x4 f.x5)
      else otherwise ()
  | none => st

/-- **Staging a held message is writing its frame**: on a table with no resize
due, a thread holding a message of at most four words stages exactly the frame
`writeDeliveredFrameIfReady` writes, with the message never held. -/
theorem stageDeliveredMessage_holdMessage (X : SystemState) (r : SeLe4n.ThreadId)
    (msg : IpcMessage) (hNo : X.objects.noResizeDue) (hSz : msg.registers.size ≤ 4) :
    Architecture.stageDeliveredMessage (X.mapTcbInPlace r (holdMessage msg)) r 0 =
      writeDeliveredFrameIfReady X r (Architecture.returnFrameOfMessage msg 0 0)
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

section NoResize

theorem updateTcb_noResizeDue (st : SystemState) (x : SeLe4n.ThreadId) (f : TCB → TCB)
    (hNo : st.objects.noResizeDue) : (st.updateTcb x f).objects.noResizeDue := by
  rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo]; exact hNo

theorem modifyObject_noResizeDue (st : SystemState) (x : SeLe4n.ObjId)
    (F : KernelObject → KernelObject) (hNo : st.objects.noResizeDue) :
    (st.modifyObject x F).objects.noResizeDue := by
  rw [SystemState.modifyObject_eq_mapValueAt _ _ _ hNo]; exact hNo

theorem storePopHead_noResizeDue (st : SystemState) (endpointId : SeLe4n.ObjId)
    (head : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (hNo : st.objects.noResizeDue) :
    (storePopHead st endpointId head next).objects.noResizeDue := by
  unfold storePopHead
  have h1 := modifyObject_noResizeDue st endpointId
    (sendRendezvousEndpoint (ThreadId.optCode next)) hNo
  cases next with
  | none => exact updateTcb_noResizeDue _ _ _ h1
  | some n => exact updateTcb_noResizeDue _ _ _ (updateTcb_noResizeDue _ _ _ h1)

theorem enqueueRunnableOnCore_noResizeDue (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (hNo : st.objects.noResizeDue) : (enqueueRunnableOnCore st c t).objects.noResizeDue := by
  rw [enqueueRunnableOnCore_eq_impl]
  unfold enqueueRunnableOnCoreImpl
  split
  · dsimp only
    split
    · exact hNo
    · exact (runEnqueueAdmitted_noResizeDue _ c t _).mpr (modifyObject_noResizeDue _ _ _ hNo)
  · exact hNo

theorem removeRunnableOnCore_noResizeDue (st : SystemState) (t : SeLe4n.ThreadId) (c : CoreId)
    (hNo : st.objects.noResizeDue) : (removeRunnableOnCore st t c).objects.noResizeDue :=
  (runRemoveOnCore_noResizeDue st c t).mpr hNo

theorem linkReplyWaiter_noResizeDue (st : SystemState) (w s : SeLe4n.ThreadId)
    (hNo : st.objects.noResizeDue) : (st.linkReplyWaiter w s).objects.noResizeDue := by
  unfold SystemState.linkReplyWaiter
  dsimp only
  exact (updateTcbAtCode_noResizeDue _ _ _).mpr hNo

theorem unlinkReplyWaiter_noResizeDue (st : SystemState) (w s : SeLe4n.ThreadId)
    (hNo : st.objects.noResizeDue) : (st.unlinkReplyWaiter w s).objects.noResizeDue := by
  unfold SystemState.unlinkReplyWaiter
  dsimp only
  exact (updateTcbAtCode_noResizeDue _ _ _).mpr ((updateTcbAtCode_noResizeDue _ _ _).mpr hNo)

end NoResize

/-- An object update that leaves every TCB alone commutes with a delivery. -/
theorem modifyObject_msg (r : SeLe4n.ThreadId) (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
    (μ : Option IpcMessage → Option IpcMessage) (st : SystemState) (x : SeLe4n.ObjId)
    (F : KernelObject → KernelObject) (hNo : st.objects.noResizeDue)
    (hF : ∀ o, F (KernelObject.mapTcb (TCB.withMessageSlots ρ μ π) o) =
      KernelObject.mapTcb (TCB.withMessageSlots ρ μ π) (F o)) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).modifyObject x F =
      (st.modifyObject x F).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  rw [SystemState.modifyObject_eq_mapValueAt _ _ _ hNo,
    SystemState.modifyObject_eq_mapValueAt (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) _ _ hNo]
  exact SystemState.mapTcbInPlace_swap_objects st r _ x F (fun _ => hF)

/-- The receiver a call or a reply wakes, ready, with no message held. -/
@[inline] def receiverReady (t : TCB) : TCB :=
  (TCB.setIpcState { t with pendingMessage := none } .ready)

theorem holdMessage_receiverReady (msg : IpcMessage) :
    holdMessage msg ∘ receiverReady = callReceiverTcb msg := rfl

/-- `storeCallRendezvous` with the receiver woken holding no message. -/
@[noinline] def storeCallRendezvousReady (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (nextCode : Nat) (rid : SeLe4n.ReplyId)
    (core : Concurrency.CoreId) : SystemState :=
  let s2 := (storePopHead st endpointId r (ThreadId.ofOptCode nextCode)).updateTcb r
    receiverReady
  let s3 := enqueueRunnableOnCore s2 (determineTargetCore s2 r) r
  let s5 := (s3.updateTcb caller (callCallerTcb endpointId r)).modifyObject rid.toObjId
    (replyWithCaller caller)
  let s7 := (s5.updateTcb caller (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) })).updateTcb r
    (fun t => { t with pendingReceiveReplyCode := 0 })
  (removeRunnableOnCore s7 caller core).linkReplyWaiter caller r

theorem storeCallRendezvousReady_noResizeDue (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (nextCode : Nat) (rid : SeLe4n.ReplyId)
    (core : Concurrency.CoreId) (hNo : st.objects.noResizeDue) :
    (storeCallRendezvousReady st endpointId caller r nextCode rid core).objects.noResizeDue := by
  unfold storeCallRendezvousReady
  dsimp only
  exact linkReplyWaiter_noResizeDue _ _ _ (removeRunnableOnCore_noResizeDue _ _ _
    (updateTcb_noResizeDue _ _ _ (updateTcb_noResizeDue _ _ _ (modifyObject_noResizeDue _ _ _
      (updateTcb_noResizeDue _ _ _ (enqueueRunnableOnCore_noResizeDue _ _ _
        (updateTcb_noResizeDue _ _ _ (storePopHead_noResizeDue _ _ _ _ hNo))))))))

/-- **The call rendezvous holds its message in one write**: the receiver woken
with the message is the receiver woken without it, the message written in
afterwards. -/
theorem storeCallRendezvous_eq_hold (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (msg : IpcMessage) (core : Concurrency.CoreId) (hNo : st.objects.noResizeDue)
    (hNe : caller ≠ r) :
    storeCallRendezvous st endpointId caller r next rid msg core =
      (storeCallRendezvousReady st endpointId caller r (ThreadId.optCode next) rid
        core).mapTcbInPlace r (holdMessage msg) := by
  unfold storeCallRendezvous storeCallRendezvousReady
  rw [SeLe4n.ThreadId.ofOptCode_optCode]
  dsimp only
  have hNo1 := storePopHead_noResizeDue st endpointId r next hNo
  have hHold : (storePopHead st endpointId r next).updateTcb r (callReceiverTcb msg) =
      ((storePopHead st endpointId r next).updateTcb r receiverReady).mapTcbInPlace r
        (holdMessage msg) := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo1,
      SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo1, SystemState.mapTcbInPlace_mapTcbInPlace,
      holdMessage_receiverReady]
  have hNo2 := updateTcb_noResizeDue _ r receiverReady hNo1
  generalize (storePopHead st endpointId r next).updateTcb r receiverReady = s2 at hHold hNo2
  rw [hHold, determineTargetCore_msg, enqueueRunnableOnCore_msg _ _ _ _ _ _ _ hNo2]
  have hNo3 := enqueueRunnableOnCore_noResizeDue s2 (determineTargetCore s2 r) r hNo2
  generalize enqueueRunnableOnCore s2 (determineTargetCore s2 r) r = s3 at hNo3
  rw [updateTcb_msg _ _ _ _ _ _ _ hNo3 (fun h => absurd h hNe)]
  have hNo4 := updateTcb_noResizeDue s3 caller (callCallerTcb endpointId r) hNo3
  generalize s3.updateTcb caller (callCallerTcb endpointId r) = s4 at hNo4
  rw [modifyObject_msg _ _ _ _ _ _ hNo4 (fun o => by cases o <;> rfl)]
  have hNo5 := modifyObject_noResizeDue s4 rid.toObjId (replyWithCaller caller) hNo4
  generalize s4.modifyObject rid.toObjId (replyWithCaller caller) = s5 at hNo5
  rw [updateTcb_msg _ _ _ _ _ _ _ hNo5 (fun h => absurd h hNe)]
  have hNo6 := updateTcb_noResizeDue s5 caller (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) }) hNo5
  generalize s5.updateTcb caller (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) }) = s6 at hNo6
  rw [updateTcb_msg _ _ _ _ _ _ _ hNo6 ?_, removeRunnableOnCore_msg, linkReplyWaiter_msg]
  intros; rfl

theorem propagatePipChainCrossCore_noResizeDue (st : SystemState) (tid : SeLe4n.ThreadId)
    (ec : CoreId) (hNo : st.objects.noResizeDue) :
    (PriorityInheritance.propagatePipChainCrossCore st tid ec).1.objects.noResizeDue := by
  rw [PriorityInheritance.propagatePipChainCrossCore_eq_walks]
  exact propagatePipChainStateWalk_noResizeDue st tid _ hNo

/-- The fallback of a delivery: the message built and held, as the
specification holds it.  Kept out of line so the message record is built only
on this path, never shared with the frame's reads. -/
@[noinline] def holdDeliveredBody (X : SystemState) (r : SeLe4n.ThreadId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (granted : Bool) : SystemState :=
  X.mapTcbInPlace r (holdMessage
    { registers := Architecture.regMessageBody layout rf len, caps := #[], badge := badge,
      capsGranted := granted })

/-- **The call rendezvous, delivered**: the receiver woken without the message,
the priority walk, then the message's frame written into the receiver's saved
registers.  The message is built only where the receiver is, unexpectedly, not
ready (`writeDeliveredFrameIfReady`'s `otherwise`). -/
@[noinline] def performCallDelivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (nextCode : Nat) (rid : SeLe4n.ReplyId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (granted : Bool)
    (core : Concurrency.CoreId) : SystemState :=
  let X := (PriorityInheritance.propagatePipChainCrossCore
    (storeCallRendezvousReady st endpointId caller r nextCode rid core) r core).1
  writeDeliveredFrameIfReady X r (Architecture.regMessageFrame layout rf len badge)
    (fun _ => holdDeliveredBody X r layout rf len badge granted)

/-- **The staged call rendezvous is the delivered one** for a message of at most
four words. -/
theorem stageWokenDelivery_performCallRendezvous (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (granted : Bool)
    (core : Concurrency.CoreId) (hNo : st.objects.noResizeDue) (hNe : caller ≠ r)
    (hSz : Architecture.regMessageLength layout len ≤ 4) :
    Architecture.stageWokenDelivery
        (performCallRendezvous st endpointId caller r next rid
          { registers := Architecture.regMessageBody layout rf len, caps := #[], badge := badge,
            capsGranted := granted } core)
        (some r) 0 =
      performCallDelivered st endpointId caller r (ThreadId.optCode next) rid layout rf len
        badge granted core := by
  have hNoS := storeCallRendezvousReady_noResizeDue st endpointId caller r
    (ThreadId.optCode next) rid core hNo
  unfold performCallRendezvous performCallDelivered
  rw [storeCallRendezvous_eq_hold _ _ _ _ _ _ _ _ hNo hNe,
    propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoS, Architecture.stageWokenDelivery_some,
    stageDeliveredMessage_holdMessage _ _ _ (propagatePipChainCrossCore_noResizeDue _ _ _ hNoS)
      (by rw [Architecture.regMessageBody_size]; exact hSz),
    Architecture.returnFrameOfMessage_regMessageBody]
  rfl

/-- `storeReplyRendezvous` with the caller woken holding no message. -/
@[noinline] def storeReplyRendezvousReady (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) : SystemState :=
  let s1 := st.updateTcb c receiverReady
  let s2 := enqueueRunnableOnCore s1 (determineTargetCore s1 c) c
  let s3 := (s2.modifyObject rid.toObjId replyConsumedObject).updateTcb c
    (fun t => { t with replyObjectCode := 0 })
  s3.unlinkReplyWaiter c server

theorem storeReplyRendezvousReady_noResizeDue (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (hNo : st.objects.noResizeDue) :
    (storeReplyRendezvousReady st c server rid).objects.noResizeDue := by
  unfold storeReplyRendezvousReady
  dsimp only
  exact unlinkReplyWaiter_noResizeDue _ _ _ (updateTcb_noResizeDue _ _ _
    (modifyObject_noResizeDue _ _ _ (enqueueRunnableOnCore_noResizeDue _ _ _
      (updateTcb_noResizeDue _ _ _ hNo))))

theorem storeReplyRendezvous_eq_hold (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (hNo : st.objects.noResizeDue) :
    storeReplyRendezvous st c server rid msg =
      (storeReplyRendezvousReady st c server rid).mapTcbInPlace c (holdMessage msg) := by
  unfold storeReplyRendezvous storeReplyRendezvousReady
  dsimp only
  have hHold : st.updateTcb c (callReceiverTcb msg) =
      (st.updateTcb c receiverReady).mapTcbInPlace c (holdMessage msg) := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo,
      SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo, SystemState.mapTcbInPlace_mapTcbInPlace,
      holdMessage_receiverReady]
  have hNo1 := updateTcb_noResizeDue st c receiverReady hNo
  generalize st.updateTcb c receiverReady = s1 at hHold hNo1
  rw [hHold, determineTargetCore_msg, enqueueRunnableOnCore_msg _ _ _ _ _ _ _ hNo1]
  have hNo2 := enqueueRunnableOnCore_noResizeDue s1 (determineTargetCore s1 c) c hNo1
  generalize enqueueRunnableOnCore s1 (determineTargetCore s1 c) c = s2 at hNo2
  rw [modifyObject_msg _ _ _ _ _ _ hNo2 (fun o => by cases o <;> rfl)]
  have hNo3 := modifyObject_noResizeDue s2 rid.toObjId replyConsumedObject hNo2
  generalize s2.modifyObject rid.toObjId replyConsumedObject = s3 at hNo3
  rw [updateTcb_msg _ _ _ _ _ _ _ hNo3 ?_, unlinkReplyWaiter_msg]
  intros; rfl

/-- A TCB rewrite in its slot leaves every Reply and SchedContext as it was,
so the state before it is a donation-chain frame of the state after it. -/
theorem donationChainFrame_of_mapTcbInPlace_rev (st : SystemState) (t : SeLe4n.ThreadId)
    (g : TCB → TCB) : donationChainFrame (st.mapTcbInPlace t g) st where
  replyLinks oid := by
    rw [SystemState.objects_mapTcbInPlace]
    split
    · cases st.objects[oid]? with
      | none => rfl
      | some o => cases o <;> rfl
    · rfl
  stackHeads oid := by
    rw [SystemState.objects_mapTcbInPlace]
    split
    · cases st.objects[oid]? with
      | none => rfl
      | some o => cases o <;> rfl
    · rfl
  callerKept oid r' h hc := by
    refine ⟨r', ?_, hc⟩
    rw [SystemState.objects_mapTcbInPlace]
    split
    · rw [h]; rfl
    · exact h

/-- **The in-place reply keeps the donation chain**, its caller woken with no
message held: the reply that holds the message keeps it
(`storeReplyRendezvous_preserves_donationChainWellFormed`), and the message is
one TCB write on top of this state (`storeReplyRendezvous_eq_hold`), which
touches no Reply and no SchedContext. -/
theorem storeReplyRendezvousReady_preserves_donationChainWellFormed (st : SystemState)
    (c server : SeLe4n.ThreadId) (ct : TCB) (ep : SeLe4n.ObjId) (rid : SeLe4n.ReplyId)
    (core : Concurrency.CoreId)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep (some server))
    (hRO : ct.replyObject = some rid)
    (hG : replyWakesInPlace st c ct rid = true)
    (hObjInv : st.objects.invExt) (hNo : st.objects.noResizeDue)
    (hChain : donationChainWellFormed st) :
    donationChainWellFormed (storeReplyRendezvousReady st c server rid) := by
  have h := storeReplyRendezvous_preserves_donationChainWellFormed st c server ct ep rid
    { registers := #[] } core (by simp) (by simp) hT hIpc hRO hG hObjInv hChain
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo] at h
  exact donationChainWellFormed_of_frame (donationChainFrame_of_mapTcbInPlace_rev _ _ _) h

/-- **The reply, delivered**: the caller woken without the message, the
server's priority walk, then the reply's frame written into the caller's saved
registers. -/
@[noinline] def performReplyDelivered (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge)
    (core : Concurrency.CoreId) : SystemState :=
  let X := (PriorityInheritance.propagatePipChainCrossCore
    (storeReplyRendezvousReady st c server rid) server core).1
  writeDeliveredFrameIfReady X c (Architecture.regMessageFrame layout rf len badge)
    (fun _ => holdDeliveredBody X c layout rf len badge false)

/-- **The reply rendezvous is the delivered one** for a message of at most four
words. -/
theorem performReplyRendezvous_eq_delivered (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge)
    (core : Concurrency.CoreId) (hNo : st.objects.noResizeDue)
    (hSz : Architecture.regMessageLength layout len ≤ 4) :
    performReplyRendezvous st c server rid
        { registers := Architecture.regMessageBody layout rf len, caps := #[], badge := badge }
        core =
      performReplyDelivered st c server rid layout rf len badge core := by
  have hNoS := storeReplyRendezvousReady_noResizeDue st c server rid hNo
  unfold performReplyRendezvous performReplyDelivered
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo, propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoS,
    stageDeliveredMessage_holdMessage _ _ _ (propagatePipChainCrossCore_noResizeDue _ _ _ hNoS)
      (by rw [Architecture.regMessageBody_size]; exact hSz),
    Architecture.returnFrameOfMessage_regMessageBody]
  rfl

theorem callWakesInPlace_noResizeDue {st : SystemState} {endpointId : SeLe4n.ObjId}
    {caller r : SeLe4n.ThreadId} {rt : TCB} {rid : SeLe4n.ReplyId}
    (h : callWakesInPlace st endpointId caller r rt rid = true) : st.objects.noResizeDue := by
  simp only [callWakesInPlace, sendWakesInPlace, Bool.and_eq_true] at h
  exact RHTable.noResizeDue_of_findsInPlace h.1.1.1.1.1.1.1.1.1.1.1.1.2

theorem callWakesInPlace_ne {st : SystemState} {endpointId : SeLe4n.ObjId}
    {caller r : SeLe4n.ThreadId} {rt : TCB} {rid : SeLe4n.ReplyId}
    (h : callWakesInPlace st endpointId caller r rt rid = true) : caller ≠ r := by
  simp only [callWakesInPlace, Bool.and_eq_true] at h
  exact bne_iff_ne.mp h.1.1.1.1.1.1.1.2

/-- A call rendezvous carrying more than four words: held and staged as the
specification does.  Out of line, so the woken receiver it names is built only
on this path and never hoisted ahead of the length test (WS-ZA ZA4.7). -/
@[noinline] def callRendezvousStaged (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (nextCode : Nat) (rid : SeLe4n.ReplyId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (granted : Bool)
    (core : Concurrency.CoreId) : SystemState :=
  Architecture.stageWokenDelivery
    (performCallRendezvous st endpointId caller r (ThreadId.ofOptCode nextCode) rid
      { registers := Architecture.regMessageBody layout rf len, caps := #[], badge := badge,
        capsGranted := granted } core)
    (some r) 0

/-- The checked call arm's rendezvous: a message of at most four words is
delivered straight into the receiver's registers (`performCallDelivered`), a
longer one is held and staged as the specification does
(`callRendezvousStaged`). -/
@[inline] def callRendezvousDelivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (nextCode : Nat) (rid : SeLe4n.ReplyId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (granted : Bool)
    (core : Concurrency.CoreId) : SystemState :=
  if Architecture.regMessageLength layout len ≤ 4 then
    performCallDelivered st endpointId caller r nextCode rid layout rf len badge granted core
  else callRendezvousStaged st endpointId caller r nextCode rid layout rf len badge granted core

theorem callRendezvousDelivered_eq (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (rt : TCB) (rid : SeLe4n.ReplyId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (granted : Bool)
    (core : Concurrency.CoreId) (hG : callWakesInPlace st endpointId caller r rt rid = true) :
    callRendezvousDelivered st endpointId caller r rt.queueNextCode rid layout rf len badge
        granted core =
      Architecture.stageWokenDelivery
        (performCallRendezvous st endpointId caller r rt.queueNext rid
          { registers := Architecture.regMessageBody layout rf len, caps := #[], badge := badge,
            capsGranted := granted } core)
        (some r) 0 := by
  unfold callRendezvousDelivered
  split
  · next hSz =>
    rw [← TCB.optCode_queueNext]
    exact (stageWokenDelivery_performCallRendezvous _ _ _ _ _ _ _ _ _ _ _ _
      (callWakesInPlace_noResizeDue hG) (callWakesInPlace_ne hG) hSz).symm
  · unfold callRendezvousStaged; rfl

theorem replyWakesInPlace_noResizeDue {st : SystemState} {c : SeLe4n.ThreadId} {ct : TCB}
    {rid : SeLe4n.ReplyId} (h : replyWakesInPlace st c ct rid = true) : st.objects.noResizeDue := by
  simp only [replyWakesInPlace, Bool.and_eq_true] at h
  exact RHTable.noResizeDue_of_findsInPlace h.1.1.1.1.2

/-- The checked reply arm's rendezvous: a reply of at most four words is
delivered straight into the caller's registers (`performReplyDelivered`). -/
@[inline] def replyRendezvousDelivered (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge)
    (core : Concurrency.CoreId) : SystemState :=
  if Architecture.regMessageLength layout len ≤ 4 then
    performReplyDelivered st c server rid layout rf len badge core
  else performReplyRendezvous st c server rid
    { registers := Architecture.regMessageBody layout rf len, caps := #[], badge := badge } core

theorem replyRendezvousDelivered_eq (st : SystemState) (c server : SeLe4n.ThreadId) (ct : TCB)
    (rid : SeLe4n.ReplyId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge)
    (core : Concurrency.CoreId) (hG : replyWakesInPlace st c ct rid = true) :
    replyRendezvousDelivered st c server rid layout rf len badge core =
      performReplyRendezvous st c server rid
        { registers := Architecture.regMessageBody layout rf len, caps := #[], badge := badge }
        core := by
  unfold replyRendezvousDelivered
  split
  · next hSz => exact (performReplyRendezvous_eq_delivered _ _ _ _ _ _ _ _ _
      (replyWakesInPlace_noResizeDue hG) hSz).symm
  · rfl

/-! ### Send -/

/-- The send rendezvous's writes, the popped receiver's last write `g`: the
specification's `storeSendRendezvous` with `g := receiveCompleteTcb msg`. -/
@[inline] def storeSendRendezvousWith (st : SystemState) (endpointId : SeLe4n.ObjId)
    (head : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (g : TCB → TCB) : SystemState :=
  let s1 := st.modifyObject endpointId (sendRendezvousEndpoint (ThreadId.optCode next))
  let s2 := match next with
    | none => s1
    | some n => s1.updateTcb n tcbAsQueueHead
  (s2.updateTcb head tcbOffQueue).updateTcb head g

theorem storeSendRendezvous_eq_with (st : SystemState) (endpointId : SeLe4n.ObjId)
    (head : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (msg : IpcMessage) :
    storeSendRendezvous st endpointId head next msg =
      storeSendRendezvousWith st endpointId head next (receiveCompleteTcb msg) := rfl

theorem storeSendRendezvousWith_comp (st : SystemState) (endpointId : SeLe4n.ObjId)
    (head : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (f g : TCB → TCB)
    (hNo : st.objects.noResizeDue) :
    storeSendRendezvousWith st endpointId head next (f ∘ g) =
      (storeSendRendezvousWith st endpointId head next g).mapTcbInPlace head f := by
  unfold storeSendRendezvousWith
  dsimp only
  have h1 := modifyObject_noResizeDue st endpointId
    (sendRendezvousEndpoint (ThreadId.optCode next)) hNo
  generalize st.modifyObject endpointId (sendRendezvousEndpoint (ThreadId.optCode next)) = s1 at h1
  have h2 : (match next with
      | none => s1
      | some n => s1.updateTcb n tcbAsQueueHead).objects.noResizeDue := by
    cases next with
    | none => exact h1
    | some n => exact updateTcb_noResizeDue _ _ _ h1
  generalize (match next with
      | none => s1
      | some n => s1.updateTcb n tcbAsQueueHead) = s2 at h2
  have h3 := updateTcb_noResizeDue s2 head tcbOffQueue h2
  generalize s2.updateTcb head tcbOffQueue = s3 at h3
  rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ h3,
    SystemState.updateTcb_eq_mapTcbInPlace _ _ _ h3, SystemState.mapTcbInPlace_mapTcbInPlace]

theorem storeSendRendezvousWith_noResizeDue (st : SystemState) (endpointId : SeLe4n.ObjId)
    (head : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (g : TCB → TCB)
    (hNo : st.objects.noResizeDue) :
    (storeSendRendezvousWith st endpointId head next g).objects.noResizeDue := by
  unfold storeSendRendezvousWith
  dsimp only
  have h1 := modifyObject_noResizeDue st endpointId
    (sendRendezvousEndpoint (ThreadId.optCode next)) hNo
  apply updateTcb_noResizeDue _ _ _ (updateTcb_noResizeDue _ _ _ _)
  cases next with
  | none => exact h1
  | some n => exact updateTcb_noResizeDue _ _ _ h1

/-- A wake commutes with a message-slot write. -/
theorem wakeThread_msg (r : SeLe4n.ThreadId) (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
    (μ : Option IpcMessage → Option IpcMessage) (π : Nat → Nat)
    (st : SystemState) (t : SeLe4n.ThreadId) (core : CoreId) (hNo : st.objects.noResizeDue) :
    wakeThread (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) t core =
      ((wakeThread st t core).1.mapTcbInPlace r (TCB.withMessageSlots ρ μ π),
        (wakeThread st t core).2) := by
  unfold wakeThread
  dsimp only
  rw [determineTargetCore_msg, enqueueRunnableOnCore_msg _ _ _ _ _ _ _ hNo]
  rcases getTcb?_msg_cases r ρ μ π st t with h | ⟨_, h⟩ <;> rw [h]
  cases st.getTcb? t <;> rfl

/-- The receiver a send wakes, ready, holding no message and no stashed reply. -/
@[inline] def receiveReadyTcb (t : TCB) : TCB :=
  (TCB.setIpcState { t with pendingMessage := none, pendingReceiveReplyCode := 0 } .ready)

/-- The receiver made ready, its message slots as they were. -/
@[inline] def ipcReadyTcb (t : TCB) : TCB := (t.setIpcState .ready)

/-- A message delivered with the receiver's stashed reply dropped: the
specification's receive completion past the ready state. -/
abbrev receiveCompleteSlots (msg : IpcMessage) : TCB → TCB :=
  TCB.withMessageSlots id (fun _ => some msg) (fun _ => 0)

/-- The receiver's message slots emptied. -/
abbrev clearMessageSlots : TCB → TCB :=
  TCB.withMessageSlots id (fun _ => none) (fun _ => 0)

theorem receiveCompleteTcb_eq_slots (msg : IpcMessage) :
    receiveCompleteTcb msg = receiveCompleteSlots msg ∘ ipcReadyTcb := rfl

theorem receiveReadyTcb_eq_slots : receiveReadyTcb = clearMessageSlots ∘ ipcReadyTcb := rfl

theorem holdMessage_clearMessageSlots (msg : IpcMessage) :
    holdMessage msg ∘ clearMessageSlots = receiveCompleteSlots msg := rfl

/-- `storeSendRendezvous` with the receiver woken holding no message. -/
@[noinline] def storeSendRendezvousReady (st : SystemState) (endpointId : SeLe4n.ObjId)
    (head : SeLe4n.ThreadId) (nextCode : Nat) : SystemState :=
  storeSendRendezvousWith st endpointId head (ThreadId.ofOptCode nextCode) receiveReadyTcb

/-- **The send rendezvous, delivered**: the receiver woken without the message,
then the message's frame written into its saved registers.  The message is
built only where the receiver is, unexpectedly, not ready. -/
@[noinline] def performSendDelivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (r : SeLe4n.ThreadId) (nextCode : Nat)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (granted : Bool) (core : CoreId) : SystemState :=
  let X := (wakeThread (storeSendRendezvousReady st endpointId r nextCode) r core).1
  writeDeliveredFrameIfReady X r (Architecture.regMessageFrame layout rf len badge)
    (fun _ => holdDeliveredBody X r layout rf len badge granted)

theorem wakeThread_noResizeDue (st : SystemState) (t : SeLe4n.ThreadId) (core : CoreId)
    (hNo : st.objects.noResizeDue) : (wakeThread st t core).1.objects.noResizeDue :=
  enqueueRunnableOnCore_noResizeDue _ _ _ hNo

/-! ### A signal waking a waiter, delivered

WS-ZA ZA4.7: a signal that wakes a notification's head waiter holds the badge
message in the waiter's TCB, and the signal arm stages it straight into the
waiter's registers.  The compiled arm writes the frame instead of holding the
message (`signalWoken_eq_delivered`), so the badge message is built only on the
unreachable path where the woken waiter is not ready. -/

/-- `storeSignalWoken` with the waiter's write given as `g`. -/
@[inline] def storeSignalWokenWith (st : SystemState) (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (g : TCB → TCB) : SystemState :=
  detachNtfnHead ((st.modifyObject notificationId (signalPoppedObject next)).updateTcb waiter g)
    waiter next

theorem storeSignalWoken_eq_with (st : SystemState) (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (msg : IpcMessage) :
    storeSignalWoken st notificationId waiter next msg =
      storeSignalWokenWith st notificationId waiter next (callReceiverTcb msg) := rfl

theorem detachNtfnHead_noResizeDue (st : SystemState) (head : SeLe4n.ThreadId)
    (next : Option SeLe4n.ThreadId) (hNo : st.objects.noResizeDue) :
    (detachNtfnHead st head next).objects.noResizeDue := by
  unfold detachNtfnHead unlinkNtfnNeighbours clearNtfnLinks
  dsimp only
  have h1 := updateTcb_noResizeDue st head (fun t => { t with
    ntfnPrevCode := SeLe4n.ThreadId.optCode none,
    ntfnNextCode := SeLe4n.ThreadId.optCode none }) hNo
  cases next with
  | none => exact h1
  | some n => exact updateTcb_noResizeDue _ _ _ h1

/-- A wake's link writes commute with a message-slot write. -/
theorem detachNtfnHead_msg (r : SeLe4n.ThreadId) (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
    (μ : Option IpcMessage → Option IpcMessage) (π : Nat → Nat)
    (st : SystemState) (head : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId)
    (hNo : st.objects.noResizeDue) :
    detachNtfnHead (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) head next =
      (detachNtfnHead st head next).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  unfold detachNtfnHead unlinkNtfnNeighbours clearNtfnLinks
  dsimp only
  rw [updateTcb_msg _ _ _ _ _ _ _ hNo ?hc]
  case hc => intros; rfl
  have h1 := updateTcb_noResizeDue st head (fun t => { t with
    ntfnPrevCode := SeLe4n.ThreadId.optCode none,
    ntfnNextCode := SeLe4n.ThreadId.optCode none }) hNo
  cases next with
  | none => rfl
  | some n =>
    dsimp only
    rw [updateTcb_msg _ _ _ _ _ _ _ h1 ?hc2]
    case hc2 => intros; rfl

theorem storeSignalWokenWith_noResizeDue (st : SystemState) (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (g : TCB → TCB)
    (hNo : st.objects.noResizeDue) :
    (storeSignalWokenWith st notificationId waiter next g).objects.noResizeDue :=
  detachNtfnHead_noResizeDue _ _ _ (updateTcb_noResizeDue _ waiter g
    (modifyObject_noResizeDue _ notificationId (signalPoppedObject next) hNo))

/-- **The wake holds its message in one write**: the waiter woken with the
message is the waiter woken without it, the message written in afterwards. -/
theorem storeSignalWoken_eq_hold (st : SystemState) (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (msg : IpcMessage)
    (hNo : st.objects.noResizeDue) :
    storeSignalWoken st notificationId waiter next msg =
      (storeSignalWokenWith st notificationId waiter next receiverReady).mapTcbInPlace waiter
        (holdMessage msg) := by
  have hNo1 := modifyObject_noResizeDue st notificationId (signalPoppedObject next) hNo
  rw [storeSignalWoken_eq_with]
  unfold storeSignalWokenWith
  generalize st.modifyObject notificationId (signalPoppedObject next) = s1 at hNo1
  have hHold : s1.updateTcb waiter (callReceiverTcb msg) =
      (s1.updateTcb waiter receiverReady).mapTcbInPlace waiter (holdMessage msg) := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo1,
      SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo1, SystemState.mapTcbInPlace_mapTcbInPlace,
      holdMessage_receiverReady]
  rw [hHold, detachNtfnHead_msg _ _ _ _ _ _ _ (updateTcb_noResizeDue s1 waiter receiverReady hNo1)]

/-- A signal's badge message stages the badge-only frame: the badge in `x0`, a
zero message-info word and no message words. -/
theorem returnFrameOfMessage_badge (badge : SeLe4n.Badge) :
    Architecture.returnFrameOfMessage { IpcMessage.empty with badge := some badge } 0 0 =
      Architecture.returnFrameOfBadge badge := by
  simp only [Architecture.returnFrameOfMessage, Architecture.returnMessageInfo,
    Architecture.returnFrameOfBadge, IpcMessage.empty, Option.map_some, Option.getD_some]
  rfl

/-- The fallback of a signal's delivery: the badge message built and held, as
the specification holds it.  Kept out of line so the message record is built
only on this path. -/
@[noinline] def holdSignalBody (X : SystemState) (waiter : SeLe4n.ThreadId)
    (badge : SeLe4n.Badge) : SystemState :=
  X.mapTcbInPlace waiter (holdMessage { IpcMessage.empty with badge := some badge })

/-- **A signal's wake, delivered**: the waiter woken without the badge message,
then the badge frame written into its saved registers.  The message is built
only where the waiter is, unexpectedly, not ready. -/
@[noinline] def performSignalWokenDelivered (st : SystemState) (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) (nextCode : Nat) (badge : SeLe4n.Badge) (core : CoreId) :
    SystemState :=
  let X := (wakeThread (storeSignalWokenWith st notificationId waiter
    (ThreadId.ofOptCode nextCode) receiverReady) waiter core).1
  writeDeliveredFrameIfReady X waiter (Architecture.returnFrameOfBadge badge)
    (fun _ => holdSignalBody X waiter badge)

/-- WS-ZA ZA4.7: **the staged signal wake is the delivered one.** -/
theorem signalWoken_eq_delivered (st : SystemState) (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (badge : SeLe4n.Badge)
    (core : CoreId) (hNo : st.objects.noResizeDue) :
    Architecture.stageWokenDelivery
        (wakeThread (storeSignalWoken st notificationId waiter next
          { IpcMessage.empty with badge := some badge }) waiter core).1
        (some waiter) 0 =
      performSignalWokenDelivered st notificationId waiter (ThreadId.optCode next) badge core := by
  have hNo0 := storeSignalWokenWith_noResizeDue st notificationId waiter next receiverReady hNo
  unfold performSignalWokenDelivered holdSignalBody
  rw [SeLe4n.ThreadId.ofOptCode_optCode, storeSignalWoken_eq_hold _ _ _ _ _ hNo,
    wakeThread_msg _ _ _ _ _ _ _ hNo0, Architecture.stageWokenDelivery_some,
    stageDeliveredMessage_holdMessage _ _ _ (wakeThread_noResizeDue _ _ _ hNo0) (by simp [IpcMessage.empty]),
    returnFrameOfMessage_badge]

end SeLe4n.Kernel
