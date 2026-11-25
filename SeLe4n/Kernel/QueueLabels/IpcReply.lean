-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.QueueLabels.Fault

/-! # The reply arms: frames

WS-SX SX11.2.  A reply makes its target `.ready` and edits reply objects and
the run queue, so it moves no thread onto an endpoint; the fault reply's
outcome writes the thread's registers and fault record, not its IPC state.
The proofs follow the records' own (`KernelRecords/IpcReply.lean`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace QueueLabelsFrame

/-- **The per-core reply leg** makes its target `.ready`. -/
theorem endpointReplyOnCore {replier target : SeLe4n.ThreadId} {msg : IpcMessage} {c : CoreId}
    {st : SystemState} (hInv : st.objects.invExt) :
    QueueLabelsFrame st
      (_root_.SeLe4n.Kernel.endpointReplyOnCore replier target msg c st).1 := by
  have hRefl : QueueLabelsFrame st st := refl hInv
  unfold _root_.SeLe4n.Kernel.endpointReplyOnCore
  split
  · exact hRefl
  split
  · exact hRefl
  · rename_i tcb hL
    have hO := lookupTcb_some_objects _ _ _ hL
    split
    · split
      · exact hRefl
      · rename_i st1 hS
        unfold storeTcbIpcStateAndMessage_fromTcb at hS
        revert hS
        cases hSt : SeLe4n.Model.storeObject target.toObjId
            (.tcb (TCB.setIpcState { tcb with pendingMessage := some msg } .ready)) st with
        | error _ => intro h; cases h
        | ok p =>
          obtain ⟨⟨⟩, s⟩ := p
          intro h
          have he := Except.ok.inj h
          subst he
          have A1 := storeObject_tcb hInv hO hSt (TcbWaitsKept.of_noWait (by simp))
          have F2 := RecordsFrame.wakeThread s target c A1.invExt (fun y hy => by
            rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr
              (storeObject_objects_eq st s _ _ hInv hSt)] at hy
            cases hy; simp)
          have A2 := A1.trans (of_frame F2)
          split
          · exact A2.trans (unlinkReplyWaiterOpt _ _ _ F2.invExt)
          · split
            · rename_i st2 hR
              have F3 := RecordsFrame.removeCallerReplyFrame F2.invExt hR
              exact (A2.trans (of_frame F3)).trans (unlinkReplyWaiterOpt _ _ _ F3.invExt)
            · exact hRefl
    · exact hRefl

theorem endpointReplyCrossCoreDispatch {replier target : SeLe4n.ThreadId} {msg : IpcMessage}
    {c : CoreId} {st : SystemState} (hInv : st.objects.invExt) :
    QueueLabelsFrame st
      (_root_.SeLe4n.Kernel.endpointReplyCrossCoreDispatch replier target msg c st).1 := by
  have hRefl : QueueLabelsFrame st st := refl hInv
  unfold _root_.SeLe4n.Kernel.endpointReplyCrossCoreDispatch
  have A := endpointReplyOnCore (replier := replier) (target := target) (msg := msg) (c := c) hInv
  generalize _root_.SeLe4n.Kernel.endpointReplyOnCore replier target msg c st = r at A
  obtain ⟨st1, res⟩ := r
  dsimp only at A ⊢
  cases res with
  | error _ => exact hRefl
  | ok sgi =>
    dsimp only
    repeat' split
    all_goals first
      | exact hRefl
      | exact A
      | exact A.trans (of_frame (RecordsFrame.propagatePipChainCrossCore _ _ _ _ A.invExt))
      | (rename_i hD
         have F := RecordsFrame.applyReplyDonationOnCore A.invExt hD
         exact A.trans (of_frame (F.trans
           (RecordsFrame.propagatePipChainCrossCore _ _ _ _ F.invExt))))
      | (rename_i hD
         exact A.trans (of_frame (RecordsFrame.applyReplyDonationOnCore A.invExt hD)))

theorem endpointReplyCrossCoreDispatchChecked {ctx : LabelingContext}
    {replier target : SeLe4n.ThreadId} {msg : IpcMessage} {c : CoreId} {st : SystemState}
    (hInv : st.objects.invExt) :
    QueueLabelsFrame st
      (_root_.SeLe4n.Kernel.endpointReplyCrossCoreDispatchChecked ctx replier target msg c st).1 := by
  unfold _root_.SeLe4n.Kernel.endpointReplyCrossCoreDispatchChecked
  split
  · exact endpointReplyCrossCoreDispatch hInv
  · exact refl hInv

/-- The decoded fault outcome applied: a restart or an abandon, neither writing
the thread's IPC state. -/
theorem faultReplyApplyOnCore (st : SystemState) (t : SeLe4n.ThreadId)
    (outcome : Architecture.FaultReplyOutcome) (hInv : st.objects.invExt) :
    QueueLabelsFrame st (_root_.SeLe4n.Kernel.faultReplyApplyOnCore st t outcome) := by
  unfold _root_.SeLe4n.Kernel.faultReplyApplyOnCore
  split
  · unfold applyFaultRestart
    exact updateTcb st t hInv fun _ => TcbWaitsKept.of_ipc rfl
  · unfold faultAbandonOnCore
    exact (of_frame (RecordsFrame.removeRunnableOnCore st t (faultAbandonCore st t) hInv)).andThen
      fun h => updateTcb _ t (f := fun tcb => { tcb.setPendingFault none with threadState := .Inactive })
        h fun _ => TcbWaitsKept.of_ipc rfl

/-- **The fault reply**: the reply chain, then the outcome. -/
theorem faultReplyOnCore {replier faulted : SeLe4n.ThreadId} {mi : MessageInfo}
    {regs : Array SeLe4n.RegValue} {c : CoreId} {st : SystemState} (hInv : st.objects.invExt) :
    QueueLabelsFrame st (_root_.SeLe4n.Kernel.faultReplyOnCore replier faulted mi regs c st).1 := by
  unfold _root_.SeLe4n.Kernel.faultReplyOnCore
  split
  · exact refl hInv
  · split
    · exact refl hInv
    · dsimp only
      have A := endpointReplyCrossCoreDispatch (replier := replier) (target := faulted)
        (msg := IpcMessage.empty) (c := c) hInv
      generalize _root_.SeLe4n.Kernel.endpointReplyCrossCoreDispatch replier faulted
        IpcMessage.empty c st = r at A
      obtain ⟨st1, res⟩ := r
      dsimp only at A ⊢
      cases res with
      | error _ => exact refl hInv
      | ok sgi =>
        dsimp only
        exact A.trans (faultReplyApplyOnCore st1 faulted _ A.invExt)

/-- **The checked reply transfer**: the fault reply, or the checked reply leg,
its capability transfer and its message stage. -/
theorem replyTransferOnCoreChecked {ctx : LabelingContext} {replier callerTid : SeLe4n.ThreadId}
    {mi : MessageInfo} {regs : Array SeLe4n.RegValue} {msg : IpcMessage} {grant : Bool}
    {c : CoreId} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.replyTransferOnCoreChecked ctx replier callerTid mi regs msg grant c
      st = .ok ((), st')) : QueueLabelsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.replyTransferOnCoreChecked at h
  split at h
  · have S := faultReplyOnCore (replier := replier) (faulted := callerTid) (mi := mi)
      (regs := regs) (c := c) hInv
    generalize _root_.SeLe4n.Kernel.faultReplyOnCore replier callerTid mi regs c st = r at S h
    obtain ⟨st1, res⟩ := r
    cases res with
    | error _ => cases h
    | ok _ => cases h; exact S
  · have S := endpointReplyCrossCoreDispatchChecked (ctx := ctx) (replier := replier)
      (target := callerTid) (msg := msg) (c := c) hInv
    generalize _root_.SeLe4n.Kernel.endpointReplyCrossCoreDispatchChecked ctx replier callerTid
      msg c st = r at S h
    obtain ⟨st1, res⟩ := r
    cases res with
    | error _ => cases h
    | ok _ =>
      simp only [] at h
      cases hX : _root_.SeLe4n.Kernel.replyTransferCaps st replier callerTid grant st1 with
      | error _ => rw [hX] at h; cases h
      | ok p =>
        obtain ⟨summary, stX⟩ := p
        rw [hX] at h
        cases h
        have SX := S.trans (of_frame (RecordsFrame.receiveTransferCaps S.invExt hX))
        exact SX.trans (of_frame (RecordsFrame.stageDeliveredMessage _ _ _ SX.invExt))

end QueueLabelsFrame

end SeLe4n.Kernel
