/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.DeliveryCommute

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
  TCB.withMessageSlots id (fun _ => some msg)

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
  have h1 := modifyObject_noResizeDue st endpointId (sendRendezvousEndpoint next) hNo
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
    (hF : ∀ o, F (KernelObject.mapTcb (TCB.withMessageSlots ρ μ) o) =
      KernelObject.mapTcb (TCB.withMessageSlots ρ μ) (F o)) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ)).modifyObject x F =
      (st.modifyObject x F).mapTcbInPlace r (TCB.withMessageSlots ρ μ) := by
  rw [SystemState.modifyObject_eq_mapValueAt _ _ _ hNo,
    SystemState.modifyObject_eq_mapValueAt (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ)) _ _ hNo]
  exact SystemState.mapTcbInPlace_swap_objects st r _ x F (fun _ => hF)

/-- The receiver a call or a reply wakes, ready, with no message held. -/
@[inline] def receiverReady (t : TCB) : TCB :=
  { t with ipcState := .ready, pendingMessage := none }

theorem holdMessage_receiverReady (msg : IpcMessage) :
    holdMessage msg ∘ receiverReady = callReceiverTcb msg := rfl

/-- `storeCallRendezvous` with the receiver woken holding no message. -/
@[noinline] def storeCallRendezvousReady (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (core : Concurrency.CoreId) : SystemState :=
  let s2 := (storePopHead st endpointId r next).updateTcb r receiverReady
  let s3 := enqueueRunnableOnCore s2 (determineTargetCore s2 r) r
  let s5 := (s3.updateTcb caller (callCallerTcb endpointId r)).modifyObject rid.toObjId
    (replyWithCaller caller)
  let s7 := (s5.updateTcb caller (fun t => { t with replyObject := some rid })).updateTcb r
    (fun t => { t with pendingReceiveReply := none })
  (removeRunnableOnCore s7 caller core).linkReplyWaiter caller r

theorem storeCallRendezvousReady_noResizeDue (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (core : Concurrency.CoreId) (hNo : st.objects.noResizeDue) :
    (storeCallRendezvousReady st endpointId caller r next rid core).objects.noResizeDue := by
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
      (storeCallRendezvousReady st endpointId caller r next rid core).mapTcbInPlace r
        (holdMessage msg) := by
  unfold storeCallRendezvous storeCallRendezvousReady
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
  rw [hHold, determineTargetCore_msg, enqueueRunnableOnCore_msg _ _ _ _ _ _ hNo2]
  have hNo3 := enqueueRunnableOnCore_noResizeDue s2 (determineTargetCore s2 r) r hNo2
  generalize enqueueRunnableOnCore s2 (determineTargetCore s2 r) r = s3 at hNo3
  rw [updateTcb_msg _ _ _ _ _ _ hNo3 (fun h => absurd h hNe)]
  have hNo4 := updateTcb_noResizeDue s3 caller (callCallerTcb endpointId r) hNo3
  generalize s3.updateTcb caller (callCallerTcb endpointId r) = s4 at hNo4
  rw [modifyObject_msg _ _ _ _ _ _ hNo4 (fun o => by cases o <;> rfl)]
  have hNo5 := modifyObject_noResizeDue s4 rid.toObjId (replyWithCaller caller) hNo4
  generalize s4.modifyObject rid.toObjId (replyWithCaller caller) = s5 at hNo5
  rw [updateTcb_msg _ _ _ _ _ _ hNo5 (fun h => absurd h hNe)]
  have hNo6 := updateTcb_noResizeDue s5 caller (fun t => { t with replyObject := some rid }) hNo5
  generalize s5.updateTcb caller (fun t => { t with replyObject := some rid }) = s6 at hNo6
  rw [updateTcb_msg _ _ _ _ _ _ hNo6 ?_, removeRunnableOnCore_msg, linkReplyWaiter_msg]
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
    (body : Array SeLe4n.RegValue) (badge : Option SeLe4n.Badge) (granted : Bool) :
    SystemState :=
  X.mapTcbInPlace r
    (holdMessage { registers := body, caps := #[], badge := badge, capsGranted := granted })

/-- **The call rendezvous, delivered**: the receiver woken without the message,
the priority walk, then the message's frame written into the receiver's saved
registers.  The message is built only where the receiver is, unexpectedly, not
ready (`writeDeliveredFrameIfReady`'s `otherwise`). -/
@[noinline] def performCallDelivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (body : Array SeLe4n.RegValue) (badge : Option SeLe4n.Badge) (granted : Bool)
    (core : Concurrency.CoreId) : SystemState :=
  let X := (PriorityInheritance.propagatePipChainCrossCore
    (storeCallRendezvousReady st endpointId caller r next rid core) r core).1
  writeDeliveredFrameIfReady X r
    (Architecture.returnFrameOfMessage
      { registers := body, caps := #[], badge := badge, capsGranted := granted } 0 0)
    (fun _ => holdDeliveredBody X r body badge granted)

/-- **The staged call rendezvous is the delivered one** for a message of at most
four words. -/
theorem stageWokenDelivery_performCallRendezvous (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (body : Array SeLe4n.RegValue) (badge : Option SeLe4n.Badge) (granted : Bool)
    (core : Concurrency.CoreId) (hNo : st.objects.noResizeDue) (hNe : caller ≠ r)
    (hSz : body.size ≤ 4) :
    Architecture.stageWokenDelivery
        (performCallRendezvous st endpointId caller r next rid
          { registers := body, caps := #[], badge := badge, capsGranted := granted } core)
        (some r) 0 =
      performCallDelivered st endpointId caller r next rid body badge granted core := by
  have hNoS := storeCallRendezvousReady_noResizeDue st endpointId caller r next rid core hNo
  unfold performCallRendezvous performCallDelivered
  rw [storeCallRendezvous_eq_hold _ _ _ _ _ _ _ _ hNo hNe,
    propagatePipChainCrossCore_msg _ _ _ _ _ _ hNoS, Architecture.stageWokenDelivery_some,
    stageDeliveredMessage_holdMessage _ _ _ (propagatePipChainCrossCore_noResizeDue _ _ _ hNoS) hSz]
  rfl

/-- `storeReplyRendezvous` with the caller woken holding no message. -/
@[noinline] def storeReplyRendezvousReady (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) : SystemState :=
  let s1 := st.updateTcb c receiverReady
  let s2 := enqueueRunnableOnCore s1 (determineTargetCore s1 c) c
  let s3 := (s2.modifyObject rid.toObjId replyConsumedObject).updateTcb c
    (fun t => { t with replyObject := none })
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
  rw [hHold, determineTargetCore_msg, enqueueRunnableOnCore_msg _ _ _ _ _ _ hNo1]
  have hNo2 := enqueueRunnableOnCore_noResizeDue s1 (determineTargetCore s1 c) c hNo1
  generalize enqueueRunnableOnCore s1 (determineTargetCore s1 c) c = s2 at hNo2
  rw [modifyObject_msg _ _ _ _ _ _ hNo2 (fun o => by cases o <;> rfl)]
  have hNo3 := modifyObject_noResizeDue s2 rid.toObjId replyConsumedObject hNo2
  generalize s2.modifyObject rid.toObjId replyConsumedObject = s3 at hNo3
  rw [updateTcb_msg _ _ _ _ _ _ hNo3 ?_, unlinkReplyWaiter_msg]
  intros; rfl

/-- **The reply, delivered**: the caller woken without the message, the
server's priority walk, then the reply's frame written into the caller's saved
registers. -/
@[noinline] def performReplyDelivered (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (body : Array SeLe4n.RegValue) (badge : Option SeLe4n.Badge)
    (core : Concurrency.CoreId) : SystemState :=
  let X := (PriorityInheritance.propagatePipChainCrossCore
    (storeReplyRendezvousReady st c server rid) server core).1
  writeDeliveredFrameIfReady X c
    (Architecture.returnFrameOfMessage { registers := body, caps := #[], badge := badge } 0 0)
    (fun _ => holdDeliveredBody X c body badge false)

/-- **The reply rendezvous is the delivered one** for a message of at most four
words. -/
theorem performReplyRendezvous_eq_delivered (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (body : Array SeLe4n.RegValue) (badge : Option SeLe4n.Badge)
    (core : Concurrency.CoreId) (hNo : st.objects.noResizeDue) (hSz : body.size ≤ 4) :
    performReplyRendezvous st c server rid { registers := body, caps := #[], badge := badge } core =
      performReplyDelivered st c server rid body badge core := by
  have hNoS := storeReplyRendezvousReady_noResizeDue st c server rid hNo
  unfold performReplyRendezvous performReplyDelivered
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo, propagatePipChainCrossCore_msg _ _ _ _ _ _ hNoS,
    stageDeliveredMessage_holdMessage _ _ _ (propagatePipChainCrossCore_noResizeDue _ _ _ hNoS) hSz]
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

/-- The checked call arm's rendezvous: a message of at most four words is
delivered straight into the receiver's registers (`performCallDelivered`), a
longer one is held and staged as the specification does. -/
@[inline] def callRendezvousDelivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (body : Array SeLe4n.RegValue) (badge : Option SeLe4n.Badge) (granted : Bool)
    (core : Concurrency.CoreId) : SystemState :=
  if body.size ≤ 4 then performCallDelivered st endpointId caller r next rid body badge granted core
  else Architecture.stageWokenDelivery
    (performCallRendezvous st endpointId caller r next rid
      { registers := body, caps := #[], badge := badge, capsGranted := granted } core) (some r) 0

theorem callRendezvousDelivered_eq (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (rt : TCB) (rid : SeLe4n.ReplyId)
    (body : Array SeLe4n.RegValue) (badge : Option SeLe4n.Badge) (granted : Bool)
    (core : Concurrency.CoreId) (hG : callWakesInPlace st endpointId caller r rt rid = true) :
    callRendezvousDelivered st endpointId caller r rt.queueNext rid body badge granted core =
      Architecture.stageWokenDelivery
        (performCallRendezvous st endpointId caller r rt.queueNext rid
          { registers := body, caps := #[], badge := badge, capsGranted := granted } core)
        (some r) 0 := by
  unfold callRendezvousDelivered
  split
  · next hSz => exact (stageWokenDelivery_performCallRendezvous _ _ _ _ _ _ _ _ _ _
      (callWakesInPlace_noResizeDue hG) (callWakesInPlace_ne hG) hSz).symm
  · rfl

theorem replyWakesInPlace_noResizeDue {st : SystemState} {c : SeLe4n.ThreadId} {ct : TCB}
    {rid : SeLe4n.ReplyId} (h : replyWakesInPlace st c ct rid = true) : st.objects.noResizeDue := by
  simp only [replyWakesInPlace, Bool.and_eq_true] at h
  exact RHTable.noResizeDue_of_findsInPlace h.1.1.1.1.2

/-- The checked reply arm's rendezvous: a reply of at most four words is
delivered straight into the caller's registers (`performReplyDelivered`). -/
@[inline] def replyRendezvousDelivered (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (body : Array SeLe4n.RegValue) (badge : Option SeLe4n.Badge)
    (core : Concurrency.CoreId) : SystemState :=
  if body.size ≤ 4 then performReplyDelivered st c server rid body badge core
  else performReplyRendezvous st c server rid { registers := body, caps := #[], badge := badge } core

theorem replyRendezvousDelivered_eq (st : SystemState) (c server : SeLe4n.ThreadId) (ct : TCB)
    (rid : SeLe4n.ReplyId) (body : Array SeLe4n.RegValue) (badge : Option SeLe4n.Badge)
    (core : Concurrency.CoreId) (hG : replyWakesInPlace st c ct rid = true) :
    replyRendezvousDelivered st c server rid body badge core =
      performReplyRendezvous st c server rid { registers := body, caps := #[], badge := badge } core := by
  unfold replyRendezvousDelivered
  split
  · next hSz => exact (performReplyRendezvous_eq_delivered _ _ _ _ _ _ _
      (replyWakesInPlace_noResizeDue hG) hSz).symm
  · rfl

end SeLe4n.Kernel
