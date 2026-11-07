-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.IpcNotification

/-!
# The fault delivery keeps the records

WS-ZA ZA6.37.  A fault is delivered as a call to the thread's handler, which
parks the thread on the call or on the reply, or the thread is suspended
`.Inactive`; the fault is recorded last, on a thread already parked.  So the
record lands parked, and every other thread is moved as the call moves it.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- A thread that is parked whenever it is present, read on a state. -/
def FaultParkedAt (st : SystemState) (t : SeLe4n.ThreadId) : Prop :=
  ∀ x, st.getTcb? t = some x → x.faultParked

namespace FaultParkedAt

/-- A frame keeps a thread parked. -/
theorem frame {st st' : SystemState} (F : RecordsFrame st st') {t : SeLe4n.ThreadId}
    (h : FaultParkedAt st t) : FaultParkedAt st' t := fun x hx => by
  obtain ⟨y, hy, hv⟩ := F.getTcb?_view hx
  have := h y hy
  simp only [TCB.recordView, TcbRecordView.mk.injEq] at hv
  unfold TCB.faultParked at this ⊢
  rw [← hv.2.1, ← hv.2.2.1]; exact this

/-- A write of run or reply-waiter links alone keeps a thread parked. -/
theorem runLinks {st st' : SystemState} (h : SystemState.objectsAgreeOffRunLinks st' st)
    {t : SeLe4n.ThreadId} (hP : FaultParkedAt st t) : FaultParkedAt st' t := fun x hx => by
  have hi := TCB.map_proj_eq_of_map_withoutRunLinks_eq TCB.ipcState (h.getTcb? t)
  have hs := TCB.map_proj_eq_of_map_withoutRunLinks_eq TCB.threadState (h.getTcb? t)
  rw [hx] at hi hs
  cases hy : st.getTcb? t with
  | none => rw [hy] at hi; cases hi
  | some y =>
    rw [hy] at hi hs
    simp only [Option.map_some, Option.some.injEq] at hi hs
    have := hP y hy
    unfold TCB.faultParked at this ⊢
    rw [hi, hs]; exact this

/-- A checked IPC-state store into a parked state parks the thread. -/
theorem of_store {st st' : SystemState} {t : SeLe4n.ThreadId} {s : ThreadIpcState}
    {m : Option IpcMessage} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.storeTcbIpcStateAndMessage st t s m = .ok st')
    (hs : ipcParked s) : FaultParkedAt st' t := fun y hy => by
  obtain ⟨z, -, hz⟩ := modifyTcb_getTcb?_self hInv h
  rw [hz] at hy; cases hy; exact .inr (by simpa using hs)

end FaultParkedAt

-- ============================================================================
-- §1  The call parks its caller
-- ============================================================================

/-- **The per-core call, when it succeeds, parks its caller**: on the reply when
it meets a receiver, on the call when it meets nobody. -/
theorem endpointCallOnCore_callerParked {endpointId : SeLe4n.ObjId} {caller : SeLe4n.ThreadId}
    {payload : SendPayload} {c : CoreId} {st : SystemState} (hInv : st.objects.invExt)
    (hQ : queueHeadBlockedConsistent st) :
    ∀ v, (_root_.SeLe4n.Kernel.endpointCallOnCore endpointId caller payload c st).2 = .ok v →
      FaultParkedAt (_root_.SeLe4n.Kernel.endpointCallOnCore endpointId caller payload c st).1
        caller := by
  unfold _root_.SeLe4n.Kernel.endpointCallOnCore
  split
  · rename_i ep hEp
    have hEpO := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp
    split
    · rename_i hd hHead
      split
      · intro _ h; cases h
      · rename_i receiver _tcb st1 hPop
        have hRh : receiver = hd := endpointQueuePopHead_popped_eq_head _ true _ _ ep _ _ _
          hEpO (by simpa using hHead) hPop
        subst hRh
        have F1 := RecordsFrame.endpointQueuePopHead hInv hPop
        split
        · intro _ h; cases h
        · rename_i st2 hRdy
          have S2 := RecordsStep.storeTcbIpcStateAndMessage F1.invExt hRdy
            (fun x hx => .inl (F1.notParked (receiveHead_notParked hQ hEpO hHead) x hx))
          obtain ⟨x, -, hx⟩ := modifyTcb_getTcb?_self F1.invExt hRdy
          have F3 := RecordsFrame.wakeThread st2 receiver c S2.invExt (fun y hy => by
            rw [hx] at hy; cases hy; simp)
          split
          · intro _ h; cases h
          · rename_i st4 hBlk
            have S4 := RecordsStep.storeTcbIpcStateAndMessage F3.invExt hBlk
              (fun _ _ => .inr (by simp))
            have P4 := FaultParkedAt.of_store F3.invExt hBlk (by simp)
            split
            · intro _ h; cases h
            · rename_i st5 hLink
              have F5 := RecordsFrame.linkServerStashedReply S4.invExt hLink
              have F6 := RecordsFrame.removeRunnableOnCore st5 caller c F5.invExt
              intro _ _
              exact ((P4.frame F5).frame F6).runLinks
                (SystemState.linkReplyWaiter_objectsAgreeOffRunLinks _ _ _)
    · split
      · intro _ h; cases h
      · rename_i st1 hEnq
        split
        · intro _ h; cases h
        · rename_i st2 hBlk
          have F1 := RecordsFrame.endpointQueueEnqueue hInv hEnq
          have S2 := RecordsStep.storeTcbIpcStateAndMessage F1.invExt hBlk
            (fun _ _ => .inr (by simp))
          have F3 := RecordsFrame.removeRunnableOnCore st2 caller c S2.invExt
          intro _ _
          exact ((FaultParkedAt.of_store F1.invExt hBlk (by simp)).frame F3).frame
            (RecordsFrame.recordSendCap _ caller payload.badge payload.grant F3.invExt)
  · split <;> (intro _ h; cases h)

theorem endpointCallWithCapsOnCore_callerParked {endpointId : SeLe4n.ObjId}
    {caller : SeLe4n.ThreadId} {payload : SendPayload} {receiverSlotBase : SeLe4n.Slot}
    {c : CoreId} {st : SystemState} (hInv : st.objects.invExt) (hQ : queueHeadBlockedConsistent st) :
    ∀ v, (_root_.SeLe4n.Kernel.endpointCallWithCapsOnCore endpointId caller payload
        receiverSlotBase c st).2 = .ok v →
      FaultParkedAt (_root_.SeLe4n.Kernel.endpointCallWithCapsOnCore endpointId caller payload
        receiverSlotBase c st).1 caller := by
  unfold _root_.SeLe4n.Kernel.endpointCallWithCapsOnCore
  have S := RecordsStep.endpointCallOnCore (endpointId := endpointId) (caller := caller)
    (payload := payload) (c := c) hInv hQ
  have P := endpointCallOnCore_callerParked (endpointId := endpointId) (caller := caller)
    (payload := payload) (c := c) hInv hQ
  generalize _root_.SeLe4n.Kernel.endpointCallOnCore endpointId caller payload c st = r at S P
  obtain ⟨st1, res⟩ := r
  dsimp only at S P ⊢
  cases res with
  | error _ => intro _ h; cases h
  | ok sgi =>
    dsimp only
    have P1 := P sgi rfl
    repeat' split
    all_goals first
      | (intro _ _; exact P1)
      | (rename_i hU; intro _ _
         exact P1.frame (RecordsFrame.receiveTransferCaps S.invExt hU))
      | (intro _ h; cases h)

theorem endpointCallCrossCoreDispatch_callerParked {endpointId : SeLe4n.ObjId}
    {caller : SeLe4n.ThreadId} {payload : SendPayload} {receiverSlotBase : SeLe4n.Slot}
    {c : CoreId} {st : SystemState} (hInv : st.objects.invExt) (hQ : queueHeadBlockedConsistent st) :
    ∀ v, (_root_.SeLe4n.Kernel.endpointCallCrossCoreDispatch endpointId caller payload
        receiverSlotBase c st).2 = .ok v →
      FaultParkedAt (_root_.SeLe4n.Kernel.endpointCallCrossCoreDispatch endpointId caller payload
        receiverSlotBase c st).1 caller := by
  unfold _root_.SeLe4n.Kernel.endpointCallCrossCoreDispatch
  have S := RecordsStep.endpointCallWithCapsOnCore (endpointId := endpointId) (caller := caller)
    (payload := payload) (receiverSlotBase := receiverSlotBase) (c := c) hInv hQ
  have P := endpointCallWithCapsOnCore_callerParked (endpointId := endpointId) (caller := caller)
    (payload := payload) (receiverSlotBase := receiverSlotBase) (c := c) hInv hQ
  generalize _root_.SeLe4n.Kernel.endpointCallWithCapsOnCore endpointId caller payload
    receiverSlotBase c st = r at S P
  obtain ⟨st1, res⟩ := r
  dsimp only at S P ⊢
  cases res with
  | error _ => intro _ h; cases h
  | ok p =>
    obtain ⟨summary, sgi⟩ := p
    dsimp only
    have P1 := P _ rfl
    repeat' split
    all_goals first
      | (intro _ _; exact P1)
      | (rename_i hD; intro _ _
         have F := RecordsFrame.applyCallDonationOnCore S.invExt hD
         exact (P1.frame F).frame (RecordsFrame.propagatePipChainCrossCore _ _ _ _ F.invExt))
      | (intro _ h; cases h)

-- ============================================================================
-- §2  The suspend, the record, the delivery
-- ============================================================================

namespace RecordsStep

/-- **The fault recorded on a parked thread.** -/
theorem recordPendingFault {st : SystemState} {t : SeLe4n.ThreadId} (tf : ThreadFault)
    (hInv : st.objects.invExt) (hP : FaultParkedAt st t) :
    RecordsStep st (_root_.SeLe4n.Kernel.recordPendingFault st t tf) :=
  updateTcb st t hInv fun x hx => TcbStaysParked.of_parked (hP x hx)

/-- **The fail-closed suspend** parks the thread `.Inactive`. -/
theorem faultSuspendOnCore (st : SystemState) (t : SeLe4n.ThreadId) (c : CoreId)
    (hInv : st.objects.invExt) : RecordsStep st (_root_.SeLe4n.Kernel.faultSuspendOnCore st t c) :=
  (of_frame (RecordsFrame.removeRunnableOnCore st t c hInv)).trans
    (updateTcb _ t (RecordsFrame.removeRunnableOnCore st t c hInv).invExt
      fun _ _ => TcbStaysParked.of_parked (.inl rfl))

end RecordsStep

theorem FaultParkedAt.faultSuspendOnCore (st : SystemState) (t : SeLe4n.ThreadId) (c : CoreId)
    (hInv : st.objects.invExt) : FaultParkedAt (_root_.SeLe4n.Kernel.faultSuspendOnCore st t c) t :=
  fun y hy => by
    unfold _root_.SeLe4n.Kernel.faultSuspendOnCore at hy
    rw [SystemState.updateTcb_getTcb?_self _ _ _
      (RecordsFrame.removeRunnableOnCore st t c hInv).invExt] at hy
    cases h : (_root_.SeLe4n.Kernel.removeRunnableOnCore st t c).getTcb? t with
    | none => rw [h] at hy; cases hy
    | some x => rw [h] at hy; cases hy; exact .inl rfl

namespace RecordsStep

/-- The suspend and the record. -/
theorem faultSuspendRecord (st : SystemState) (t : SeLe4n.ThreadId) (c : CoreId)
    (tf : ThreadFault) (hInv : st.objects.invExt) :
    RecordsStep st (_root_.SeLe4n.Kernel.recordPendingFault
      (_root_.SeLe4n.Kernel.faultSuspendOnCore st t c) t tf) :=
  (faultSuspendOnCore st t c hInv).trans
    (recordPendingFault tf (faultSuspendOnCore st t c hInv).invExt
      (FaultParkedAt.faultSuspendOnCore st t c hInv))

/-- **The fault delivery keeps the address-space records and every fault record
parked**: the handler call parks the thread, or the suspend does, before the
record lands. -/
theorem faultDeliverOnCore {st : SystemState} {t : SeLe4n.ThreadId} {f : Fault}
    {fctx : FaultContext} {c : CoreId} (hInv : st.objects.invExt)
    (hQ : queueHeadBlockedConsistent st) :
    RecordsStep st (_root_.SeLe4n.Kernel.faultDeliverOnCore st t f fctx c).1 := by
  have sus := faultSuspendRecord st t c { fault := f, context := fctx } hInv
  unfold _root_.SeLe4n.Kernel.faultDeliverOnCore
  split
  · exact sus
  · rename_i tgt _
    have S := endpointCallCrossCoreDispatch (endpointId := tgt.endpoint) (caller := t)
      (payload := .fault f fctx tgt.cap.badge) (receiverSlotBase := SeLe4n.Slot.ofNat 0)
      (c := c) hInv hQ
    have P := endpointCallCrossCoreDispatch_callerParked (endpointId := tgt.endpoint)
      (caller := t) (payload := .fault f fctx tgt.cap.badge)
      (receiverSlotBase := SeLe4n.Slot.ofNat 0) (c := c) hInv hQ
    generalize _root_.SeLe4n.Kernel.endpointCallCrossCoreDispatch tgt.endpoint t
      (.fault f fctx tgt.cap.badge) (SeLe4n.Slot.ofNat 0) c st = r at S P ⊢
    obtain ⟨st1, res⟩ := r
    dsimp only at S P ⊢
    cases res with
    | error _ => exact sus
    | ok v =>
      dsimp only
      refine (S.trans (of_frame (RecordsFrame.stageWokenDelivery st1 _ _ S.invExt))).trans
        (recordPendingFault _ ?_ ?_)
      · exact (RecordsFrame.stageWokenDelivery _ _ _ S.invExt).invExt
      · exact (P v rfl).frame (RecordsFrame.stageWokenDelivery _ _ _ S.invExt)

/-- The flow-checked fault delivery: the delivery, or the suspend a denied flow
takes. -/
theorem faultDeliverOnCoreChecked {ctx : LabelingContext} {st : SystemState} {t : SeLe4n.ThreadId}
    {f : Fault} {fctx : FaultContext} {c : CoreId} (hInv : st.objects.invExt)
    (hQ : queueHeadBlockedConsistent st) :
    RecordsStep st (_root_.SeLe4n.Kernel.faultDeliverOnCoreChecked ctx st t f fctx c).1 := by
  have sus := faultSuspendRecord st t c { fault := f, context := fctx } hInv
  unfold _root_.SeLe4n.Kernel.faultDeliverOnCoreChecked
  split
  · exact sus
  · split
    · exact faultDeliverOnCore hInv hQ
    · exact sus

/-- The fault-register spill keeps every record view. -/
theorem writeFaultRegistersToTcb (st : SystemState) (t : SeLe4n.ThreadId)
    (w : FaultRegisterWindow) (hInv : st.objects.invExt) :
    RecordsStep st (_root_.SeLe4n.Kernel.writeFaultRegistersToTcb st t w) :=
  updateTcb st t hInv fun _ _ => TcbStaysParked.of_fields rfl rfl rfl

end RecordsStep

end SeLe4n.Kernel
