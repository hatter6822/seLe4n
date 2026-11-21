-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.API
import SeLe4n.Kernel.KernelRecords.Capability
import SeLe4n.Kernel.KernelRecords.Audit
import SeLe4n.Kernel.KernelRecords.Tails
import SeLe4n.Kernel.KernelRecords.SchedulingArms
import SeLe4n.Kernel.KernelRecords.Delete
import SeLe4n.Kernel.KernelRecords.VSpace
import SeLe4n.Kernel.KernelRecords.SetSpace
import SeLe4n.Kernel.KernelRecords.Retype
import SeLe4n.Kernel.KernelRecords.LifecycleWaiters
import SeLe4n.Kernel.KernelRecords.IpcStages
import SeLe4n.Kernel.KernelRecords.IpcReplyRecv
import SeLe4n.Kernel.KernelRecords.Timer
import SeLe4n.Kernel.IPC.Invariant.ReplyHolderCancelHeads

/-! # The dispatchers keep the records

WS-ZA ZA6.37.  The capability-only dispatch keeps the records on every arm: each
arm is a records stage (`Kernel/KernelRecords/*.lean`), and the capability
resolution and the argument decodes read.  Three facts are read off the state
the dispatcher is handed, as the mapping traversal reads its own
(`MappingArmPremises`) and the IPC traversal its reachable bundle: the deletes,
the thread-space set and the handler bind and clear carry the reply-waiter
queues by the reachable bundle (`reachableDeleteBundle`), and the resume restores
an `.Inactive` thread, which is quiescent in IPC (`threadIpcFieldsQuiescent`, the
`targetThreadQuiescent` field of the dispatch's premises, stated here of every
`.Inactive` thread so it is a fact about the state, not about the call).  The arm runs on the state the dispatcher is handed, since its
lookups and decodes write nothing.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open Architecture.RegisterDecode
open Architecture.SyscallArgDecode

/-- **The bind keeps the records**: neither word is in a record view. -/
theorem RecordsFrame.schedContextBindNotification {vScId : SeLe4n.ValidObjId}
    {n : SeLe4n.ObjId} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.schedContextBindNotification vScId n st = .ok ((), st')) :
    RecordsFrame st st' := by
  obtain ⟨hA, rfl⟩ := schedContextBindNotification_ok_admitted h
  obtain ⟨_, _, hS, -, hN, -⟩ := schedContextBindNotificationAdmitted_facts hA
  obtain ⟨h1, hEq⟩ := bindNotificationSchedLink_eq hS hN hInv
  rw [hEq]
  have F := RecordsFrame.updateSchedContext st (SeLe4n.SchedContextId.ofObjId vScId.val)
    (fun sc => { sc with notificationCode := n.val + 1 }) hInv
  exact F.trans (RecordsFrame.insert F.invExt (by rw [h1]; rfl))


/-- **`SchedContext_Unbind` keeps the records**: the thread unbind's frame,
then the notification unbind's and the reply-stack unlink's. -/
theorem RecordsFrame.schedContextUnbindAllOnCore {vScId : SeLe4n.ValidObjId}
    {ec : Concurrency.CoreId} {st st' : SystemState}
    {sgi? : Option (Concurrency.CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (h : SchedContextOps.schedContextUnbindAllOnCore vScId ec st = .ok (st', sgi?)) :
    RecordsFrame st st' := by
  obtain ⟨stU, hU | ⟨-, hU, -⟩, rfl⟩ := SchedContextOps.schedContextUnbindAllOnCore_ok h
  · obtain ⟨rfl, -⟩ := hU
    have F := RecordsFrame.unbindSchedContextNotification _
      (SeLe4n.SchedContextId.ofObjId vScId.val) hInv
    exact F.trans (RecordsFrame.schedContextUnbindReply _ _ F.invExt)
  · have F := RecordsFrame.schedContextUnbindOnCore hInv hU
    have F2 := F.trans (RecordsFrame.unbindSchedContextNotification _
      (SeLe4n.SchedContextId.ofObjId vScId.val) F.invExt)
    exact F2.trans (RecordsFrame.schedContextUnbindReply _ _ F2.invExt)

/-- **`SchedContext_UnbindObject` keeps the records**: on a thread, the thread
unbind's frame; on a notification, the notification unbind's. -/
theorem RecordsFrame.schedContextUnbindThreadObjectOnCore {vScId : SeLe4n.ValidObjId}
    {tid : SeLe4n.ThreadId} {ec : Concurrency.CoreId} {st st' : SystemState}
    {sgi? : Option (Concurrency.CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (h : SchedContextOps.schedContextUnbindThreadObjectOnCore vScId tid ec st = .ok (st', sgi?)) :
    RecordsFrame st st' :=
  RecordsFrame.schedContextUnbindOnCore hInv
    (SchedContextOps.schedContextUnbindThreadObjectOnCore_ok h)

theorem RecordsFrame.schedContextUnbindNotificationObject {vScId : SeLe4n.ValidObjId}
    {n : SeLe4n.ObjId} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : SchedContextOps.schedContextUnbindNotificationObject vScId n st = .ok ((), st')) :
    RecordsFrame st st' := by
  obtain ⟨-, rfl⟩ := SchedContextOps.schedContextUnbindNotificationObject_ok h
  exact RecordsFrame.unbindSchedContextNotification _ _ hInv

/-- A stage onto a transition's state is a stage onto the state it returns. -/
theorem RecordsStage.of_fst_eq {α : Type} {st st' : SystemState} {p : SystemState × α} {r : α}
    (s : RecordsStage st p.1) (h : p = (st', r)) : RecordsStage st st' := by
  subst h; exact s

/-- What the capability arms read off the dispatcher's state beyond the records:
the reachable bundle the deletes carry, and every `.Inactive` thread's IPC
quiescence, which the resume reads of its target. -/
structure RecordsArmPremises (st : SystemState) : Prop where
  deletes : reachableDeleteBundle st
  inactiveQuiescent : ∀ t tcb, st.getTcb? t = some tcb → tcb.threadState = .Inactive →
    threadIpcFieldsQuiescent st t

/-- **A reply holder's cancel keeps the records** (WS-SX SX4): the suspend's IPC
cancel and its revert, as the suspend runs them, then the `Inactive` write,
which leaves the holder parked. -/
theorem RecordsStage.cancelReplyHolder (st : SystemState) (holder : SeLe4n.ThreadId)
    (ec : Concurrency.CoreId) : RecordsStage st (SeLe4n.Kernel.cancelReplyHolder st holder ec) := fun h => by
  have hI := KernelRecords.objects_invExt h
  rcases cancelReplyHolder_cases st holder ec with e | ⟨tcb, hL, -, e⟩
  · rw [e]; exact h
  rw [e]
  have hT : st.getTcb? holder = some tcb :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr (lookupTcb_some_objects st holder tcb hL)
  have S1 := RecordsStep.cancelIpcKeepingContexts st holder tcb hI
  have W1 := cancelIpcKeepingContexts_waitersStage st holder tcb hT
  have S2 : RecordsStep st (Lifecycle.Suspend.suspendCancelRevert st holder tcb ec) ∧
      WaitersStage st (Lifecycle.Suspend.suspendCancelRevert st holder tcb ec) := by
    unfold Lifecycle.Suspend.suspendCancelRevert; dsimp only; split
    · exact ⟨S1.trans (RecordsStep.of_frame
          (RecordsFrame.propagatePipChainCrossCore _ _ _ _ S1.invExt)),
        W1.trans (WaitersStage.of_frame fun hI' => RecordsFrame.propagatePipChainCrossCore _ _ _ _ hI')⟩
    · exact ⟨S1, W1⟩
  have S3 := S2.1.trans (RecordsStep.updateTcb _ holder S2.1.invExt
    (f := fun t => { t with threadState := .Inactive })
    fun _ _ => TcbStaysParked.of_parked (.inl rfl))
  have W3 := S2.2.trans (WaitersStage.updateTcb _ holder (f := fun t => { t with threadState := .Inactive })
    fun _ => rfl)
  exact RecordsStage.of_step S3 (fun hC => (W3 hI hC).2) h

/-- A reply holder's cancel leaves every other thread `.ready` in IPC. -/
theorem CallerReady.cancelReplyHolder {st : SystemState} {tid holder : SeLe4n.ThreadId}
    {ec : Concurrency.CoreId} (hInv : st.objects.invExt) (hNe : tid ≠ holder)
    (h : CallerReady st tid) : CallerReady (SeLe4n.Kernel.cancelReplyHolder st holder ec) tid := by
  obtain ⟨t, hT, hR⟩ := h
  have e := cancelReplyHolder_ipcStateKeptExcept st holder ec hInv tid hNe
  rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hT] at e
  cases h' : (SeLe4n.Kernel.cancelReplyHolder st holder ec).getTcb? tid with
  | none => rw [h'] at e; cases e
  | some t' =>
    rw [h'] at e
    exact ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mp h', (Option.some.inj e).trans hR⟩

/-- The retire before a resume keeps the thread's state and its IPC state. -/
theorem retirePendingFaultForResume_threadState {st : SystemState} {t : SeLe4n.ThreadId} {y : TCB}
    (hInv : st.objects.invExt) (hy : (retirePendingFaultForResume st t).getTcb? t = some y) :
    ∃ x, st.getTcb? t = some x ∧ x.threadState = y.threadState ∧ x.ipcState = y.ipcState := by
  cases hT : st.getTcb? t with
  | none => simp only [retirePendingFaultForResume, hT] at hy; cases hy
  | some x =>
    refine ⟨x, rfl, ?_⟩
    cases hF : x.pendingFault with
    | none => simp only [retirePendingFaultForResume, hT, hF] at hy; cases hy; exact ⟨rfl, rfl⟩
    | some tf =>
      simp only [retirePendingFaultForResume, hT, hF] at hy
      split at hy
      · rw [discardPendingFault_getTcb?_self st t x hT hInv] at hy; cases hy; exact ⟨rfl, rfl⟩
      · rw [applyFaultRestart_pc st t _ x hT hInv] at hy; cases hy; exact ⟨rfl, rfl⟩

/-- **A suspend leaves its target ready in IPC**: the IPC cancel restores it, and
every later step keeps its IPC state — the PIP revert, the deschedule, the
release removal, the yield-link cancel and the scheduling point keep every
record view, and the two writes to the target touch other fields. -/
theorem suspendThreadOnCore_target_ipcReady {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId} {c : Concurrency.CoreId}
    {sgi? : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt)
    (hActive : ∀ t, st.getTcb? vtid.val = some t → t.threadState ≠ .Inactive)
    (hStep : Lifecycle.Suspend.suspendThreadOnCore st vtid c = .ok (st', sgi?)) :
    ∀ x, st'.getTcb? vtid.val = some x → x.ipcState = .ready := by
  have back : ∀ {a b : SystemState}, RecordsFrame a b →
      (∀ x, a.getTcb? vtid.val = some x → x.ipcState = .ready) →
      ∀ y, b.getTcb? vtid.val = some y → y.ipcState = .ready := fun F h y hy => by
    obtain ⟨x, hx, hv⟩ := F.getTcb?_view hy
    rw [← h x hx]; exact (congrArg TcbRecordView.ipc hv).symm
  simp only [Lifecycle.Suspend.suspendThreadOnCore] at hStep
  split at hStep
  case h_2 => exact absurd hStep (by simp)
  case h_1 tcb hT =>
    split at hStep
    case isTrue hA => exact absurd (by simpa using hA) (hActive tcb hT)
    case isFalse hA =>
      have hI1 := Lifecycle.Suspend.cancelIpcKeepingContexts_preserves_objects_invExt st
        vtid.val tcb hInv
      have R1 : ∀ x, (Lifecycle.Suspend.cancelIpcKeepingContexts st vtid.val tcb).getTcb?
          vtid.val = some x → x.ipcState = .ready := by
        have hI0 := Lifecycle.Suspend.cutCancelledCallerHead_preserves_objects_invExt st tcb hInv
        have hIp := cutCancelledCallerHead_getTcb?_map st tcb TCB.ipcState
          (fun _ => rfl) hInv vtid.val
        rw [hT] at hIp
        obtain ⟨x0, hx0, hx0I⟩ := Option.map_eq_some_iff.mp hIp
        have hNR : ¬ vtid.val.isReserved := by
          rcases vtid with ⟨⟨n⟩, hv⟩
          simp only [SeLe4n.ThreadId.isReserved, decide_eq_true_eq]
          intro h; subst h; exact hv rfl
        intro x hx
        exact cancelIpcBlocking_victim_ready_of_ipcState _ vtid.val tcb x0 hI0
          ((SystemState.getTcb?_eq_some_iff _ _ _).mp hx0) hNR hx0I x
          ((SystemState.getTcb?_eq_some_iff _ _ _).mp hx)
      have F2 : RecordsFrame (Lifecycle.Suspend.cancelIpcKeepingContexts st vtid.val tcb)
          (match PriorityInheritance.blockingServer st vtid.val with
           | some serverId => (PriorityInheritance.propagatePipChainCrossCore
               (Lifecycle.Suspend.cancelIpcKeepingContexts st vtid.val tcb) serverId c).1
           | none => Lifecycle.Suspend.cancelIpcKeepingContexts st vtid.val tcb) := by
        cases PriorityInheritance.blockingServer st vtid.val with
        | none => exact RecordsFrame.refl hI1
        | some serverId => exact RecordsFrame.propagatePipChainCrossCore _ _ _ _ hI1
      have F3 := F2.trans (RecordsFrame.descheduleAt _ vtid.val (placedCoreOf? st vtid.val)
        F2.invExt)
      have F4 := F3.trans (show RecordsFrame _ (Lifecycle.Suspend.clearPendingStateValid _ vtid) by
        unfold Lifecycle.Suspend.clearPendingStateValid Lifecycle.Suspend.clearPendingState
        exact RecordsFrame.updateTcb _ _ F3.invExt fun _ => rfl)
      have R4 := back F4 R1
      have upd : ∀ {a b : SystemState} {f : TCB → TCB}, RecordsFrame (a.updateTcb vtid.val f) b →
          a.objects.invExt → (∀ t, (f t).ipcState = t.ipcState) →
          (∀ x, a.getTcb? vtid.val = some x → x.ipcState = .ready) →
          ∀ y, b.getTcb? vtid.val = some y → y.ipcState = .ready := fun F hI hf hR => by
        refine back F fun y hy => ?_
        rw [SystemState.updateTcb_getTcb?_self _ _ _ hI] at hy
        obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hy
        rw [hf]; exact hR x hx
      have hI5 := SystemState.updateTcb_preserves_objects_invExt _ vtid.val
        (fun t => { t with threadState := .Inactive }) F4.invExt
      have F6 := (RecordsFrame.releaseRemoveThread _ vtid.val hI5).trans
        (RecordsFrame.cancelYieldTo _ vtid.val (RecordsFrame.releaseRemoveThread _ vtid.val hI5).invExt)
      exact upd (F6.trans (RecordsStep.suspendRescheduleOnCore F6.invExt hStep)) F4.invExt
        (fun _ => rfl) R4

/-- A resume that commits found its target `.Inactive`, so quiescent in IPC. -/
theorem inactiveQuiescent_of_resume {st : SystemState} {vtid : SeLe4n.ValidThreadId} {c : Concurrency.CoreId}
    {r : SystemState × Option (Concurrency.CoreId × Concurrency.SgiKind)}
    (P : RecordsArmPremises st) (hInv : st.objects.invExt)
    (h : Lifecycle.Suspend.resumeThreadOnCore (retirePendingFaultForResume st vtid.val) vtid c
      = .ok r) : threadIpcFieldsQuiescent st vtid.val := by
  unfold Lifecycle.Suspend.resumeThreadOnCore at h
  dsimp only at h
  split at h
  · rename_i y hy
    split at h
    · cases h
    · rename_i hIn
      obtain ⟨x, hx, hS, -⟩ := retirePendingFaultForResume_threadState hInv hy
      exact P.inactiveQuiescent _ x hx (by rw [hS]; simpa using hIn)
  · cases h

/-- **The capability-only dispatch keeps the records on every arm**: the deletes,
the space set and the handler arms from the reachable bundle they read, the
resume from the target's quiescence, every other arm from the records alone. -/
theorem dispatchCapabilityOnly_recordsStage
    (decoded : SyscallDecodeResult) (cap : Capability) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (k : Kernel Unit) (st st' : SystemState)
    (hArm : dispatchCapabilityOnly decoded cap tid executingCore = some k)
    (P : RecordsArmPremises st) (hStep : k st = .ok ((), st')) :
    RecordsStage st st' := by
  unfold dispatchCapabilityOnly at hArm
  cases hSy : decoded.syscallId <;> simp only [hSy] at hArm <;> try cases hArm
  case cspaceDelete =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object cnodeId =>
      try dsimp only [] at hStep
      cases hDec : decodeCSpaceDeleteArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          exact fun h => (cspaceDeleteSlotZombie_deleteRecordsCarried ⟨h, P.deletes⟩ hStep).1
    all_goals try cases hStep
  case cspaceRevoke =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object cnodeId =>
      try dsimp only [] at hStep
      cases hDec : decodeCSpaceDeleteArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          exact fun h => (cspaceRevokeCdtFinalising_deleteRecordsCarried ⟨h, P.deletes⟩ hStep).1
    all_goals try cases hStep
  case mintReplyCap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object cnodeId =>
      try dsimp only [] at hStep
      cases hDec : decodeMintReplyCapArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          exact .of_frameK fun hI => RecordsFrame.mintReplyCapWithCdt hI hStep
    all_goals try cases hStep
  case untypedRetype =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object _ =>
      exact RecordsStage.untypedRetypeFromCap hStep
    all_goals try cases hStep
  case vspaceMap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      cases hDec : decodePageMapArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok words =>
          simp only [hDec] at hStep
          cases hX : callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0 with
          | none => simp only [hX] at hStep; cases hStep
          | some rootCPtr =>
            simp only [hX] at hStep
            cases hOps : resolvePageMapOperands tid decoded.capAddr rootCPtr words st with
            | error e => simp only [hOps] at hStep; cases hStep
            | ok p =>
              obtain ⟨_, args⟩ := p
              simp only [hOps] at hStep
              exact RecordsStage.vspaceMapOrRemapFromFrameCap hStep
    all_goals try cases hStep
  case vspaceUnmap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      cases hR : resolveCallerCapSlot tid decoded.capAddr (syscallRequiredRight .vspaceUnmap) st with
      | error e => simp only [hR] at hStep; cases hStep
      | ok r =>
          obtain ⟨slot, _, _⟩ := r
          simp only [hR] at hStep
          exact RecordsStage.vspaceUnmapFrameCap hStep
    all_goals try cases hStep
  case vspaceUnifyInstruction =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      cases hDec : decodeVSpaceUnifyInstructionArgs decoded st.machine.maxASID with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          · exact .of_frameK fun hI => RecordsFrame.vspaceUnifyInstructionPage hI hStep
    all_goals try cases hStep
  case serviceRevoke =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case serviceRegistry _ =>
      replace hStep := serviceEndpointArm_ok hStep
      obtain ⟨_, oid, -, hStep⟩ := hStep
      try dsimp only [] at hStep
      obtain ⟨_, hRev⟩ := revokeServiceByRecordedRegistration_revokeService hStep
      exact .of_frameK fun hI => RecordsFrame.revokeService hI hRev
    all_goals try cases hStep
  case serviceQuery =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case serviceRegistry _ =>
      replace hStep := serviceEndpointArm_ok hStep
      obtain ⟨_, epId, -, hStep⟩ := hStep
      try dsimp only [] at hStep
      cases hLkS : lookupServiceByRecordedRegistration epId st with
      | error e => simp only [hLkS] at hStep; cases hStep
      | ok pair =>
          obtain ⟨reg, st1⟩ := pair
          simp only [hLkS] at hStep
          have hStEq : st1 = st := lookupServiceByRecordedRegistration_preserves_state epId st reg st1 hLkS
          subst hStEq
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
          subst hStep
          exact .of_frameK fun hI => RecordsFrame.writeCallReturnWord _ _ _ hI
    all_goals try cases hStep
  case schedContextConfigure =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case schedControl core =>
      try dsimp only [] at hStep
      rcases hXc : callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0 with _ | scCPtr
      · simp only [hXc] at hStep; cases hStep
      simp only [hXc] at hStep
      cases hVal : resolveSchedControlConfigureTarget tid core scCPtr decoded.msgInfo.length st with
      | error e => simp only [hVal] at hStep; cases hStep
      | ok vScId =>
          simp only [hVal] at hStep
          cases hDec : decodeSchedContextConfigureArgsChecked decoded with
          | error e => simp only [hDec] at hStep; cases hStep
          | ok args =>
              simp only [hDec] at hStep
              split at hStep
              · exact .of_frameK fun hI => RecordsFrame.schedControlConfigure hI hStep
              · cases hStep
    all_goals try cases hStep
  case schedContextBind =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hN : resolveSchedContextBindNotificationCode tid
          (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st with
      | succ k =>
          simp only [hN] at hStep
          cases hVal : validateObjIdArg scId with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vScId =>
              simp only [hVal] at hStep
              exact .of_frameK fun hI => RecordsFrame.schedContextBindNotification hI hStep
      | zero =>
          simp only [hN] at hStep
          cases hRes : resolveSchedContextBindThread tid (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st with
          | error e => simp only [hRes] at hStep; cases hStep
          | ok vThreadId =>
              simp only [hRes] at hStep
              cases hVal : validateObjIdArg scId with
              | error e => simp only [hVal] at hStep; cases hStep
              | ok vScId =>
                  simp only [hVal] at hStep
                  exact .of_frameK fun hI => RecordsFrame.schedContextBind hI hStep
    all_goals try cases hStep
  case schedContextUnbind =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hDec : decodeSchedContextUnbindArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateObjIdArg scId with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vScId =>
              simp only [hVal] at hStep
              cases hUn : SchedContextOps.schedContextUnbindAllOnCore vScId
                  executingCore st with
              | error e => simp only [hUn] at hStep; cases hStep
              | ok pair =>
                  obtain ⟨stU, sgiU⟩ := pair
                  simp only [hUn] at hStep
                  cases hStep
                  exact .of_frameK fun hI => RecordsFrame.schedContextUnbindAllOnCore hI hUn
    all_goals try cases hStep
  case schedContextUnbindObject =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hN : resolveSchedContextBindNotificationCode tid
          (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st with
      | succ k =>
          simp only [hN] at hStep
          cases hVal : validateObjIdArg scId with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vScId =>
              simp only [hVal] at hStep
              exact .of_frameK fun hI => RecordsFrame.schedContextUnbindNotificationObject hI hStep
      | zero =>
          simp only [hN] at hStep
          cases hRes : resolveSchedContextBindThread tid (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st with
          | error e => simp only [hRes] at hStep; cases hStep
          | ok vThreadId =>
              simp only [hRes] at hStep
              cases hVal : validateObjIdArg scId with
              | error e => simp only [hVal] at hStep; cases hStep
              | ok vScId =>
                  simp only [hVal] at hStep
                  cases hUn : SchedContextOps.schedContextUnbindThreadObjectOnCore vScId
                      vThreadId.val executingCore st with
                  | error e => simp only [hUn] at hStep; cases hStep
                  | ok pair =>
                      obtain ⟨stU, sgiU⟩ := pair
                      simp only [hUn] at hStep
                      cases hStep
                      exact .of_frameK fun hI => RecordsFrame.schedContextUnbindThreadObjectOnCore hI hUn
    all_goals try cases hStep
  case schedContextConsumed =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hVal : validateObjIdArg scId with
      | error e => simp only [hVal] at hStep; cases hStep
      | ok vScId =>
          simp only [hVal] at hStep
          cases hC : schedContextConsumedOnCore (SeLe4n.SchedContextId.ofObjId vScId.val)
              executingCore st with
          | error e => simp only [hC] at hStep; cases hStep
          | ok stC =>
              simp only [hC] at hStep
              cases hStep
              exact .of_frameK fun hI => RecordsFrame.schedContextConsumedOnCore hI hC
    all_goals try cases hStep
  case schedContextYieldTo =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hVal : validateObjIdArg scId with
      | error e => simp only [hVal] at hStep; cases hStep
      | ok vScId =>
          simp only [hVal] at hStep
          cases hC : SchedContextOps.schedContextYieldToOnCore
              (SeLe4n.SchedContextId.ofObjId vScId.val) executingCore st with
          | error e => simp only [hC] at hStep; cases hStep
          | ok stC =>
              simp only [hC] at hStep
              cases hStep
              exact .of_frameK fun hI => RecordsFrame.schedContextYieldToOnCore hI hC
    all_goals try cases hStep
  case irqHandlerAck =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqHandler line =>
      rw [Architecture.irqHandlerAck_ok hStep]
      exact .of_frameK fun hI => RecordsFrame.of_objects_eq hI rfl rfl
    all_goals try cases hStep
  case irqControlGet =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqControl => exact .of_frameK fun hI => RecordsFrame.irqControlGetFromCap hI hStep
    all_goals try cases hStep
  case irqHandlerSetNotification =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqHandler line =>
      obtain ⟨_, _, _, hS⟩ := irqHandlerSetNotificationFromCap_ok tid executingCore line _ st st' hStep
      exact fun h => irqHandlerSetNotification_kernelRecordsSound ⟨h, P.deletes⟩ hS
    all_goals try cases hStep
  case irqHandlerClear =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqHandler line => exact fun h => irqHandlerClear_kernelRecordsSound ⟨h, P.deletes⟩ hStep
    all_goals try cases hStep
  case tcbBindNotification =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object tcbObjId =>
      try dsimp only [] at hStep
      cases hDec : tcbBindNotificationArgsOf st tid decoded.msgInfo.extraCaps with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hCaller : st.getTcb? tid with
          | none => simp only [hCaller] at hStep; cases hStep
          | some callerTcb =>
              simp only [hCaller] at hStep
              try dsimp only [] at hStep
              cases hCap2 : resolveBindNotificationCap { callerId := tid, cspaceRootCap := callerTcb.spaceCells[0], capAddr := args.notificationCPtr, requiredRight := .read } st with
              | error e => simp only [hCap2] at hStep; cases hStep
              | ok notifId =>
                  simp only [hCap2] at hStep
                  exact .of_frameK fun hI => RecordsFrame.bindNotification hI hStep
    all_goals try cases hStep
  case tcbUnbindNotification =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object tcbObjId =>
      try dsimp only [] at hStep
      cases hUn : unbindNotification (SeLe4n.ThreadId.ofNat tcbObjId.toNat) st with
      | error e => simp only [hUn] at hStep; cases hStep
      | ok pair =>
          obtain ⟨u, stU⟩ := pair; cases u
          simp only [hUn] at hStep
          cases hStep
          exact .of_frameK fun hI => RecordsFrame.unbindNotification hI hUn
    all_goals try cases hStep
  case tcbSuspend =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeSuspendArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vtid =>
              simp only [hVal] at hStep
              cases hSus : Lifecycle.Suspend.suspendThreadOnCore st vtid
                  executingCore with
              | error e => simp only [hSus] at hStep; cases hStep
              | ok pair =>
                  obtain ⟨stU, sgiU⟩ := pair
                  simp only [hSus] at hStep
                  cases hStep
                  exact RecordsStage.suspendThreadOnCore hSus
    all_goals try cases hStep
  case tcbResume =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeResumeArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
      | error e => simp only [hVal] at hStep; cases hStep
      | ok vtid =>
          simp only [hVal] at hStep
          cases hRes : Lifecycle.Suspend.restartThreadOnCore st vtid executingCore with
          | error e => simp only [hRes] at hStep; cases hStep
          | ok pair =>
              obtain ⟨stU, sgiU⟩ := pair
              simp only [hRes] at hStep
              cases hStep
              rcases Lifecycle.Suspend.restartThreadOnCore_cases hRes with
                hRes | ⟨st1, _, hSus, hRes⟩ | ⟨rfl, _⟩
              rotate_left
              · intro h
                by_cases hAct : ∀ t, st.getTcb? vtid.val = some t → t.threadState ≠ .Inactive
                · have hI1 := KernelRecords.objects_invExt
                    (RecordsStage.suspendThreadOnCore hSus h)
                  exact RecordsStage.resumeThreadOnCore
                    (fun y hy => by
                      obtain ⟨x, hx, -, hS⟩ := retirePendingFaultForResume_threadState hI1 hy
                      rw [← hS]
                      exact suspendThreadOnCore_target_ipcReady
                        (KernelRecords.objects_invExt h) hAct hSus x hx) hRes
                    (RecordsStage.retirePendingFaultForResume st1 vtid.val
                      (RecordsStage.suspendThreadOnCore hSus h))
                · -- An `Inactive` target's suspend writes nothing, so the resume
                  -- runs on the state the restart was handed.
                  obtain ⟨t, ht, hti⟩ : ∃ t, st.getTcb? vtid.val = some t ∧
                      t.threadState = .Inactive := by
                    cases hT0 : st.getTcb? vtid.val with
                    | none => exact absurd (fun t ht => by rw [hT0] at ht; cases ht) hAct
                    | some t =>
                      refine ⟨t, rfl, Classical.byContradiction fun hne => hAct ?_⟩
                      intro t' ht'
                      rw [hT0] at ht'
                      cases ht'
                      exact hne
                  rw [Lifecycle.Suspend.suspendThreadOnCore_of_inactive st vtid executingCore t ht hti]
                    at hSus
                  cases hSus
                  exact RecordsStage.resumeThreadOnCore
                    (threadIpcFieldsQuiescent_retirePendingFaultForResume st _
                      (KernelRecords.objects_invExt h)
                      (inactiveQuiescent_of_resume P (KernelRecords.objects_invExt h) hRes)).ready hRes
                    (RecordsStage.retirePendingFaultForResume st vtid.val h)
              · exact RecordsStage.refl _
              exact fun h => RecordsStage.resumeThreadOnCore
                (threadIpcFieldsQuiescent_retirePendingFaultForResume st _
                  (KernelRecords.objects_invExt h)
                  (inactiveQuiescent_of_resume P (KernelRecords.objects_invExt h) hRes)).ready hRes
                (RecordsStage.retirePendingFaultForResume st vtid.val h)
    all_goals try cases hStep
  case tcbSetPriority =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeSetPriorityArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hValC : resolvePriorityAuthority st tid
              (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0) with
          | error e => simp only [hValC] at hStep; cases hStep
          | ok vCallerTid =>
              simp only [hValC] at hStep
              cases hValT : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
              | error e => simp only [hValT] at hStep; cases hStep
              | ok vTargetTid =>
                  simp only [hValT] at hStep
                  cases hSet : SchedContext.PriorityManagement.setPriorityOnCore st
                      vCallerTid vTargetTid (Priority.ofNat args.newPriority)
                      executingCore with
                  | error e => simp only [hSet] at hStep; cases hStep
                  | ok pair =>
                      obtain ⟨stU, sgiU⟩ := pair
                      simp only [hSet] at hStep
                      cases hStep
                      exact .of_frameK fun hI => RecordsFrame.setPriorityOnCore hI hSet
    all_goals try cases hStep
  case tcbSetMCPriority =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeSetMCPriorityArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hValC : resolvePriorityAuthority st tid
              (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0) with
          | error e => simp only [hValC] at hStep; cases hStep
          | ok vCallerTid =>
              simp only [hValC] at hStep
              cases hValT : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
              | error e => simp only [hValT] at hStep; cases hStep
              | ok vTargetTid =>
                  simp only [hValT] at hStep
                  cases hSet : SchedContext.PriorityManagement.setMCPriorityOnCore st
                      vCallerTid vTargetTid (Priority.ofNat args.newMCP)
                      executingCore with
                  | error e => simp only [hSet] at hStep; cases hStep
                  | ok pair =>
                      obtain ⟨stU, sgiU⟩ := pair
                      simp only [hSet] at hStep
                      cases hStep
                      exact .of_frameK fun hI => RecordsFrame.setMCPriorityOnCore hI hSet
    all_goals try cases hStep
  case tcbSetIPCBuffer =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeSetIPCBufferArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vtid =>
              simp only [hVal] at hStep
              cases hSet : Architecture.IpcBufferValidation.setIPCBufferOp executingCore st
                  vtid tid (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0)
                  args.bufferAddr with
              | error e => simp only [hSet] at hStep; cases hStep
              | ok stU =>
                  simp only [hSet] at hStep
                  cases hStep
                  exact fun h => setIPCBufferOp_kernelRecordsSound executingCore h P.deletes.1 hSet
    all_goals try cases hStep
  case tcbSetAffinity =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : Architecture.SyscallArgDecode.decodeSetAffinityArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vtid =>
              simp only [hVal] at hStep
              cases hAff : decodeAffinity args.affinityRaw with
              | error e => simp only [hAff] at hStep; cases hStep
              | ok affinity =>
                  simp only [hAff] at hStep
                  cases hSet : setThreadCpuAffinityOnCore st vtid affinity
                      executingCore with
                  | error e => simp only [hSet] at hStep; cases hStep
                  | ok pair =>
                      obtain ⟨stU, sgiU⟩ := pair
                      simp only [hSet] at hStep
                      cases hStep
                      exact .of_frameK fun hI => RecordsFrame.setThreadCpuAffinityOnCore hI hSet
    all_goals try cases hStep
  case tcbSetSpace =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : Architecture.SyscallArgDecode.decodeSetSpaceArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vtid =>
              simp only [hVal] at hStep
              cases hR : resolveSetSpace tid decoded.msgInfo.extraCaps args st with
              | error e => simp only [hR] at hStep; cases hStep
              | ok p =>
                  obtain ⟨cn, vr, fh⟩ := p
                  simp only [hR] at hStep
                  cases hSet : copyThreadSpacesZombie executingCore st vtid cn vr args.cspaceRootData fh with
                  | error e => simp only [hSet] at hStep; cases hStep
                  | ok stU =>
                      simp only [hSet] at hStep
                      cases hStep
                      exact fun h => copyThreadSpacesZombie_kernelRecordsSound executingCore ⟨h, P.deletes⟩ hSet
    all_goals try cases hStep
  case pageTableMap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : Architecture.SyscallArgDecode.decodePageTableMapArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hX : callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0 with
          | none => simp only [hX] at hStep; cases hStep
          | some rootCPtr =>
            simp only [hX] at hStep
            cases hR : resolveCallerCapObject tid rootCPtr .write st with
            | error e => simp only [hR] at hStep; cases hStep
            | ok p =>
                obtain ⟨_, rootId⟩ := p
                simp only [hR] at hStep
                exact RecordsStage.pageTableMap hStep
    all_goals try cases hStep
  case pageTableUnmap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      exact RecordsStage.pageTableUnmap hStep
    all_goals try cases hStep

/-! ### The wrapping steps of the capability dispatch -/

/-- The tail every waking arm ends with: clear the woken receiver's stash, then
stage the delivered frames. -/
theorem clearStashStage_recordsStage {st s st' : SystemState}
    {woken? : Option SeLe4n.ThreadId} {stage : SystemState → SystemState}
    (hS : RecordsStage st s) (hStage : ∀ x, RecordsStage x (stage x))
    (h : (match clearWokenReceiverStash woken? s with
      | .error e => .error e
      | .ok ((), s') => .ok ((), stage s')) =
        (.ok ((), st') : Except KernelError (Unit × SystemState))) :
    RecordsStage st st' := by
  split at h
  · cases h
  · rename_i s3 hClr
    cases h
    exact hS.trans ((RecordsStage.of_frameK fun hI =>
      RecordsFrame.clearWokenReceiverStash woken? hI hClr).trans (hStage _))

/-- A delivered-frame staging. -/
theorem stageWokenDelivery_recordsStage (x : SystemState) (w : Option SeLe4n.ThreadId) (n : Nat) :
    RecordsStage x (Architecture.stageWokenDelivery x w n) :=
  .of_frameK fun hI => RecordsFrame.stageWokenDelivery x w n hI

/-- A return-frame write. -/
theorem writeReturnFrameToTcb_recordsStage (x : SystemState) (t : SeLe4n.ThreadId)
    (f : Architecture.SyscallReturnFrame) : RecordsStage x (Architecture.writeReturnFrameToTcb x t f) :=
  .of_frameK fun hI => RecordsFrame.writeReturnFrameToTcb x t f hI

/-- **seL4-MCS `maybeDonateSchedContext` keeps the records**: the identity, or
the bind's writes under seL4's guard (`RecordsFrame.schedContextBindPerform`). -/
theorem maybeDonateSchedContext_recordsStage (x : SystemState) (n : SeLe4n.ObjId)
    (t : SeLe4n.ThreadId) : RecordsStage x (maybeDonateSchedContext x n t) :=
  .of_frameK fun hI => maybeDonateSchedContext_induct (fun a b => RecordsFrame a b) x n t
    (RecordsFrame.refl hI) (fun vS vT _ _ => RecordsFrame.schedContextBindPerform x vS vT hI)

/-- **seL4's return on a running receiver keeps the records**: the context's
thread link and the thread's binding written in place, then reschedule flags. -/
theorem RecordsFrame.schedContextReturnLinks {st : SystemState} (vS : SeLe4n.ValidObjId)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    RecordsFrame st (SeLe4n.Kernel.schedContextReturnLinks st vS tid) := by
  have hU : ∀ S : SystemState, S.objects.invExt → RecordsFrame S
      (S.updateTcb tid fun t => { t with scBindingScCode := 0, scBindingOwnerCode := 0 }) :=
    fun S h => RecordsFrame.updateTcb _ _ h fun _ => rfl
  unfold SeLe4n.Kernel.schedContextReturnLinks
  split
  · exact RecordsFrame.refl hInv
  rename_i sc hSc _
  split
  · exact RecordsFrame.refl hInv
  dsimp only
  refine RecordsFrame.chain ?_ (RecordsFrame.markKeyChangeFor _ _ _) hInv
  refine RecordsFrame.chain ?_ (RecordsFrame.markCandidacyGainFor _ _ _)
  split
  · exact RecordsFrame.chain (RecordsFrame.chain (RecordsFrame.rewriteObject_schedContext hSc _ _)
      fun h => hU _ h) (RecordsFrame.markReschedulePendingOnCore _ _)
  · exact RecordsFrame.chain (RecordsFrame.rewriteObject_schedContext hSc _ _) fun h => hU _ h

/-- **The return keeps the records**: seL4's three writes, then the purge. -/
theorem RecordsFrame.schedContextReturnPerform {st : SystemState} (vS : SeLe4n.ValidObjId)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    RecordsFrame st (SeLe4n.Kernel.schedContextReturnPerform st vS tid) :=
  let F1 := RecordsFrame.schedContextReturnLinks vS tid hInv
  F1.trans (RecordsFrame.purgeReplenishment _ _ F1.invExt)

/-- **seL4 `receiveIPC`'s return keeps what the receive needs of its state**:
the store's integrity, the queue heads' blocking states and the caller ready —
it writes two binding codes and a context's thread link, no IPC state and no
endpoint. -/
theorem receiveReturnSchedContext_receivePremises (blocks : Bool) (st : SystemState)
    (tid : SeLe4n.ThreadId) (hI : st.objects.invExt) (hQ : queueHeadBlockedConsistent st)
    (hC : CallerReady st tid) :
    (receiveReturnSchedContext blocks st tid).objects.invExt ∧
      queueHeadBlockedConsistent (receiveReturnSchedContext blocks st tid) ∧
      CallerReady (receiveReturnSchedContext blocks st tid) tid := by
  refine ⟨receiveReturnSchedContext_objects_invExt blocks st tid hI, ?_, ?_⟩
  · intro epId ep hd tcb hEp hT
    have hEp0 : st.objects[epId]? = some (.endpoint ep) := by
      rcases receiveReturnSchedContext_objects blocks st tid hI epId with e | ⟨_, _, e⟩ | ⟨_, _, _, e⟩ <;>
        rw [e] at hEp
      · exact hEp
      · cases hEp
      · cases hEp
    obtain ⟨y, hy, hxy⟩ := receiveReturnSchedContext_tcb blocks st tid hI _ tcb hT
    have h := hQ epId ep hd y hEp0 hy
    rcases hxy with h' | h' <;> (subst tcb; exact h)
  · obtain ⟨t, hT, hR⟩ := hC
    rcases receiveReturnSchedContext_objects blocks st tid hI tid.toObjId with e | ⟨y, hy, e⟩ | ⟨_, _, hs, _⟩
    · exact ⟨t, by rw [e]; exact hT, hR⟩
    · rw [hT] at hy; cases hy; exact ⟨_, e, hR⟩
    · rw [hT] at hs; cases hs

/-- **seL4 `receiveIPC`'s return keeps the records.** -/
theorem receiveReturnSchedContext_recordsStage (blocks : Bool) (x : SystemState)
    (t : SeLe4n.ThreadId) : RecordsStage x (receiveReturnSchedContext blocks x t) :=
  .of_frameK fun hI => receiveReturnSchedContext_induct (fun a b => RecordsFrame a b) blocks x t
    (RecordsFrame.refl hI) (fun vS _ _ _ => RecordsFrame.schedContextReturnPerform vS t hI)

/-- **seL4 `receiveIPC`'s return keeps the receive leg's facts**: the queue
heads' blocking states, the receiver ready, and every endpoint as it was — it
writes two binding codes and a context's thread link, no IPC state and no
endpoint. -/
theorem receiveReturnSchedContext_receiveLegFacts (blocks : Bool) (st : SystemState)
    (tid : SeLe4n.ThreadId) (hI : st.objects.invExt) (hQ : queueHeadBlockedConsistent st)
    (hReady : ∀ x, st.getTcb? tid = some x → x.ipcState = .ready) :
    queueHeadBlockedConsistent (receiveReturnSchedContext blocks st tid) ∧
      (∀ x, (receiveReturnSchedContext blocks st tid).getTcb? tid = some x →
        x.ipcState = .ready) ∧
      (∀ (e : SeLe4n.ObjId) (ep : Endpoint),
        (receiveReturnSchedContext blocks st tid).objects[e]? = some (.endpoint ep) →
          st.objects[e]? = some (.endpoint ep)) := by
  have hEB : ∀ (e : SeLe4n.ObjId) (ep : Endpoint),
      (receiveReturnSchedContext blocks st tid).objects[e]? = some (.endpoint ep) →
        st.objects[e]? = some (.endpoint ep) := fun e ep hEp => by
    rcases receiveReturnSchedContext_objects blocks st tid hI e with h | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ <;>
      rw [h] at hEp
    · exact hEp
    · cases hEp
    · cases hEp
  refine ⟨fun epId ep hd tcb hEp hT => ?_, fun x hx => ?_, hEB⟩
  · obtain ⟨y, hy, hxy⟩ := receiveReturnSchedContext_tcb blocks st tid hI _ tcb hT
    have h := hQ epId ep hd y (hEB epId ep hEp) hy
    rcases hxy with h' | h' <;> (subst tcb; exact h)
  · obtain ⟨y, hy, hxy⟩ := receiveReturnSchedContext_tcb blocks st tid hI _ x
      ((SystemState.getTcb?_eq_some_iff _ _ _).mp hx)
    rcases hxy with h' | h' <;> (subst x; exact hReady y ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hy))

section ReplyRecvRecords

open SeLe4n.Kernel.Concurrency (CoreId)

namespace RecordsStep

/-- **The reply-receive keeps the address-space records and every fault record
parked**: the reply leg unparks its caller, every step after it keeps the
records, and the answer either finds the caller carrying no fault record or
clears the one it answers. -/
theorem endpointReplyRecvAnsweringOnCore {answer : Option Architecture.FaultReplyOutcome}
    {epId : SeLe4n.ObjId} {tid : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    {prevCaller : SeLe4n.ThreadId} {msg : IpcMessage} {grant : Bool}
    {c : CoreId} {st st' : SystemState} {summary : CapTransferSummary}
    (hInv : st.objects.invExt) (hQ : queueHeadBlockedConsistent st)
    (hReady : ∀ x, st.getTcb? tid = some x → x.ipcState = .ready)
    (hAns : answer = none → NoFaultAt st prevCaller)
    (h : _root_.SeLe4n.Kernel.endpointReplyRecvAnsweringOnCore answer epId tid rid prevCaller msg
      grant c st = .ok (summary, st')) :
    RecordsStep st st' := by
  unfold _root_.SeLe4n.Kernel.endpointReplyRecvAnsweringOnCore at h
  dsimp only at h
  have A := ReplyLegStep.endpointReplyOnCore (replier := tid) (target := prevCaller) (msg := msg)
    (c := c) hInv
  revert h A
  cases hR : _root_.SeLe4n.Kernel.endpointReplyOnCore tid prevCaller msg c st with
  | mk st1 res1 =>
  cases res1 with
  | error _ => intro h; cases h
  | ok sgi =>
  intro h A
  dsimp only at h A
  split at h
  · cases h
  rename_i ret st1q hPop
  obtain ⟨⟨xs, st1p⟩, hX⟩ := replyRecvReplyTransfer_ok answer st tid prevCaller grant st1q
  rw [hX] at h
  dsimp only at h
  obtain ⟨hQp, hRp, -⟩ := replyRecvReceiveLegFacts hInv hQ hR hPop hX hReady
  have F0 := RecordsFrame.replyRecvPopDonation A.1.invExt hPop
  have F1 := F0.trans (RecordsFrame.receiveTransferCaps F0.invExt
    (by rw [replyRecvReplyTransfer_eq_receiveTransferCaps] at hX; exact hX))
  -- seL4-MCS `receiveIPC`'s `maybeReturnSchedContext`, before the receive leg.
  have FR : RecordsFrame st1p (receiveReturnSchedContext true st1p tid) :=
    receiveReturnSchedContext_induct (fun a b => RecordsFrame a b) true st1p tid
      (RecordsFrame.refl F1.invExt)
      (fun vS _ _ _ => RecordsFrame.schedContextReturnPerform vS tid F1.invExt)
  obtain ⟨hQr, hRr, -⟩ := receiveReturnSchedContext_receiveLegFacts true st1p tid F1.invExt
    hQp hRp
  have S2 := endpointReceiveDualWithCapsOnCore (endpointId := epId) (replyId := some rid)
    (c := c) FR.invExt hQr
    (fun x hx => by rw [hRr x hx]; exact ipcParked_ready)
  revert h S2
  generalize _root_.SeLe4n.Kernel.endpointReceiveDualWithCapsOnCore epId tid (some rid)
    c (receiveReturnSchedContext true st1p tid) = r2
  obtain ⟨st2, res2⟩ := r2
  cases res2 with
  | error _ => intro h; cases h
  | ok q =>
  obtain ⟨nextThread, summ, _⟩ := q
  intro h S2
  dsimp only at h S2
  split at h
  · cases h
  rename_i st3 hPost
  cases h
  have F3 := RecordsFrame.replyRecvPostReceiveDonation S2.invExt hPost
  have F4 := RecordsFrame.applyReceiveLegPipHandoff st3 tid nextThread
    ((recordedReplyServer? st prevCaller).getD tid) c F3.invExt
  have Mid : RecordsStep st1 _ :=
    ((((RecordsStep.of_frame (F1.trans FR)).trans S2).trans (.of_frame F3)).trans (.of_frame F4))
  cases answer with
  | none =>
    have F5 := RecordsFrame.stageDeliveredMessage _ prevCaller xs.capInfo F4.invExt
    exact ((A.2 (hAns rfl)).trans Mid).trans (.of_frame F5)
  | some o =>
    obtain ⟨S5, hN⟩ := faultReplyApplyOnCore _ prevCaller o F4.invExt
    have F6 := RecordsFrame.refl S5.invExt
    exact ((A.1.trans (.of_step (Mid.trans S5))).trans (.of_step (.of_frame F6))).close
      (hN.frame F6)

end RecordsStep

namespace CallerReady

theorem ready {st : SystemState} {t : SeLe4n.ThreadId} (h : CallerReady st t) :
    ∀ x, st.getTcb? t = some x → x.ipcState = .ready := fun x hx => by
  obtain ⟨tcb, hT, hR⟩ := h
  have hE := hT.symm.trans ((SystemState.getTcb?_eq_some_iff _ _ _).mp hx)
  simp only [Option.some.injEq, KernelObject.tcb.injEq] at hE
  subst hE; exact hR

end CallerReady

open SeLe4n.Model.SystemState in
/-- **The reply-receive keeps the records**, its server the running thread: an
answer to a faulted caller clears its fault record, any other answer finds none. -/
theorem RecordsStage.endpointReplyRecvAnsweringOnCore
    {answer : Option Architecture.FaultReplyOutcome} {epId : SeLe4n.ObjId} {tid : SeLe4n.ThreadId}
    {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId} {msg : IpcMessage} {grant : Bool}
    {c : CoreId} {st st' : SystemState}
    {summary : CapTransferSummary} (hR : ipcReachable st) (hC : CallerReady st tid)
    (hAns : answer = none → NoFaultAt st prevCaller)
    (h : _root_.SeLe4n.Kernel.endpointReplyRecvAnsweringOnCore answer epId tid rid prevCaller msg
      grant c st = .ok (summary, st')) : RecordsStage st st' :=
  have hQ := hR.ipcInvariantFull.queueHeadBlockedConsistent
  RecordsStage.of_step (RecordsStep.endpointReplyRecvAnsweringOnCore hR.objects_invExt hQ hC.ready hAns h)
    fun hW => by
      have hOk := h
      unfold _root_.SeLe4n.Kernel.endpointReplyRecvAnsweringOnCore at hOk
      dsimp only at hOk
      cases hRl : _root_.SeLe4n.Kernel.endpointReplyOnCore tid prevCaller msg c st with
      | mk st1 res1 =>
      rw [hRl] at hOk
      cases res1 with
      | error _ => cases hOk
      | ok sgi =>
      dsimp only at hOk
      cases hP : _root_.SeLe4n.Kernel.replyRecvPopDonation rid prevCaller st1 with
      | error _ => rw [hP] at hOk; cases hOk
      | ok p =>
      obtain ⟨ret, st1q⟩ := p
      obtain ⟨⟨xs, st1p⟩, hX⟩ := replyRecvReplyTransfer_ok answer st tid prevCaller grant st1q
      obtain ⟨hQp0, hRp0, hEp0⟩ :=
        replyRecvReceiveLegFacts hR.objects_invExt hQ hRl hP hX hC.ready
      have hInvP : st1p.objects.invExt :=
        replyRecvReplyTransfer_objects_invExt
          (replyRecvPopDonation_preserves_objects_invExt rid prevCaller st1 st1q ret
            (by have := endpointReplyOnCore_preserves_objects_invExt tid prevCaller msg c st
                  hR.objects_invExt
                rw [hRl] at this; exact this) hP) hX
      obtain ⟨hQp, hRp, hEpR⟩ := receiveReturnSchedContext_receiveLegFacts true st1p tid hInvP
        hQp0 hRp0
      have hEp : ∀ (e : SeLe4n.ObjId) (ep : Endpoint),
          (receiveReturnSchedContext true st1p tid).objects[e]? = some (.endpoint ep) →
          st.objects[e]? = some (.endpoint ep) := fun e ep h => hEp0 e ep (hEpR e ep h)
      have hPost : replyRecvReceiveLegState answer st tid grant rid prevCaller
          (_root_.SeLe4n.Kernel.endpointReplyOnCore tid prevCaller msg c st).1 =
            receiveReturnSchedContext true st1p tid := by
        rw [hRl]; exact replyRecvReceiveLegState_eq_of_ok _ _ _ _ _ _ _ _ _ _ _ hP hX
      refine endpointReplyRecvOnCore_preserves_replyWaitersConsistent epId tid rid prevCaller msg
        grant c st st' summary hR.objects_invExt hW ?_ ?_ h
      · rw [hPost]
        intro v hv
        obtain ⟨t, hT, rfl⟩ := tcb_of_replyViews hv
        have hS := hRp t ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hT)
        simp only [TCB.replyView, TCB.blockingServer?, hS]
      · rw [hPost]
        intro ep s hE hH
        refine ⟨fun hs => ?_, sendHead_serverFree hQp hE hH⟩
        subst hs
        obtain ⟨tcb, hT, hRd⟩ := hC
        rcases (hQ epId ep s tcb (hEp epId ep hE) hT).2 hH with hS | hS <;> rw [hRd] at hS <;>
          cases hS

/-- **The `.replyRecv` arm's transition keeps the records**: the answer the
caller's own fault record selects, so a caller answered with its message
carries no fault record. -/
theorem RecordsStage.replyRecvTransferOnCore {epId : SeLe4n.ObjId} {tid : SeLe4n.ThreadId}
    {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId} {label : Nat} {msg : IpcMessage}
    {grant : Bool} {c : CoreId} {st st' : SystemState}
    {summary : CapTransferSummary} (hR : ipcReachable st) (hC : CallerReady st tid)
    (h : _root_.SeLe4n.Kernel.replyRecvTransferOnCore epId tid rid prevCaller label msg
      grant c st = .ok (summary, st')) : RecordsStage st st' := by
  unfold _root_.SeLe4n.Kernel.replyRecvTransferOnCore at h
  refine RecordsStage.endpointReplyRecvAnsweringOnCore hR hC (fun hA x hx => ?_) h
  cases hF : x.pendingFault with
  | none => rfl
  | some _ => simp only [replyRecvCallerFaultAnswer?, hx, hF] at hA; cases hA

end ReplyRecvRecords


/-- **seL4-MCS `maybeReturnSchedContext` keeps the kernel records**: the
identity, or seL4's writes and the purge (`RecordsFrame.schedContextReturnPerform`). -/
theorem maybeReturnSchedContext_recordsStage (x : SystemState) (n : SeLe4n.ObjId)
    (t : SeLe4n.ThreadId) : RecordsStage x (maybeReturnSchedContext x n t) :=
  .of_frameK fun hI => maybeReturnSchedContext_induct (fun a b => RecordsFrame a b) x n t
    (RecordsFrame.refl hI) (fun vS _ _ _ => RecordsFrame.schedContextReturnPerform vS t hI)

/-- **seL4's `sendSignal` keeps the records**: the wake's step, then the
donation's. -/
theorem sendSignalOnCore_recordsStage {n : SeLe4n.ObjId} {badge : SeLe4n.Badge}
    {c : Concurrency.CoreId} {st : SystemState} (hR : ipcReachable st) :
    RecordsStage st (sendSignalOnCore n badge c st).1 :=
  sendSignalOnCore_induct (RecordsStage st) n badge c st
    (RecordsStage.notificationSignalBoundOnCore hR)
    (fun t _ _ _ => (RecordsStage.notificationSignalBoundOnCore hR).trans
      (maybeDonateSchedContext_recordsStage _ n t))

/-- **The declassifying dispatch keeps the records**: the declassifying
signal's stage, then the donation's. -/
theorem notificationSignalDeclassifiedCrossCoreDispatch_recordsStage {ctx : GenericLabelingContext}
    {declPolicy : DeclassificationPolicy} {nid : SeLe4n.ObjId} {badge : SeLe4n.Badge}
    {c : Concurrency.CoreId} {st : SystemState} (hR : ipcReachable st) :
    RecordsStage st
      (notificationSignalDeclassifiedCrossCoreDispatch ctx declPolicy nid badge c st).1 :=
  have hS := RecordsStage.notificationSignalDeclassifiedOnCore (ctx := ctx)
    (declPolicy := declPolicy) (badge := badge) (c := c) hR
  notificationSignalDeclassifiedCrossCoreDispatch_induct (RecordsStage st) ctx declPolicy nid
    badge c st hS (fun t _ _ _ => hS.trans (maybeDonateSchedContext_recordsStage _ nid t))

/-- **The checked bound signal keeps the records.** -/
theorem notificationSignalBoundCrossCoreDispatchChecked_recordsStage {ctx : LabelingContext}
    {nid : SeLe4n.ObjId} {signaler : SeLe4n.ThreadId} {badge : SeLe4n.Badge}
    {c : Concurrency.CoreId} {st : SystemState} (hR : ipcReachable st) :
    RecordsStage st (notificationSignalBoundCrossCoreDispatchChecked ctx nid signaler badge c st).1 :=
  notificationSignalBoundCrossCoreDispatchChecked_induct (RecordsStage st) ctx nid signaler badge
    c st (RecordsStage.refl _) (sendSignalOnCore_recordsStage hR)

/-- The `Call`-gated reply write keeps the records. -/
theorem writeCallReturnWord_recordsStage (x : SystemState) (t : SeLe4n.ThreadId)
    (w : UInt64) : RecordsStage x (Architecture.writeCallReturnWord x t w) :=
  .of_frameK fun hI => RecordsFrame.writeCallReturnWord x t w hI

/-- **A receive that completes its bound notification keeps the records**: the
checked wait's consumption, read with no reachability premise -- the reply-waiter
consistency it needs is the one the records themselves carry -- and the badge
register written. -/
theorem completeSignalArm_recordsStage {ctx : LabelingContext} {tid : SeLe4n.ThreadId}
    {nid : SeLe4n.ObjId} {c : Concurrency.CoreId} {st st' : SystemState}
    (hInv : st.objects.invExt) (hC : CallerReady st tid)
    (h : completeSignalArm ctx tid nid c st = .ok ((), st')) :
    RecordsStage st st' := by
  have hW : RecordsStage st (notificationWaitCrossCoreDispatchChecked ctx nid tid c st).1 :=
    RecordsStage.of_step (RecordsStep.notificationWaitCrossCoreDispatchChecked hInv
      hC.notParked) fun hRW => by
      unfold notificationWaitCrossCoreDispatchChecked
      split
      · split
        · exact hRW
        · exact notificationWaitOnCore_preserves_replyWaitersConsistent nid tid c st
            hInv hRW hC.serverFree
      · exact hRW
  unfold completeSignalArm at h
  split at h
  · rename_i hR
    cases h
    exact ((RecordsStage.of_fst_eq hW hR).trans (writeReturnFrameToTcb_recordsStage _ _ _)).trans
      (maybeDonateSchedContext_recordsStage _ _ _)
  · rename_i hR
    cases h
    exact (RecordsStage.of_fst_eq hW hR).trans (maybeReturnSchedContext_recordsStage _ _ _)
  · cases h

/-- A receive run on its busy-reply-cancelled state keeps the records: the
`.receive` arm, and the `.replyRecv` arm whose reply is skipped. -/
theorem receiveResolvedArm_recordsStage (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (epId : SeLe4n.ObjId)
    (st st' : SystemState) (P : RecordsArmPremises st) (hCaller : CallerReady st tid)
    (h : receiveResolvedArm ctx decoded gate tid epId executingCore
      (cancelRecvBusyReply ctx tid gate decoded executingCore st) = .ok ((), st')) :
    RecordsStage st st' := by
  unfold receiveResolvedArm at h
  have hInv := P.deletes.2.1.2.1
  have hIpc := P.deletes.2.1.1
  have hSC : RecordsStage st (cancelRecvBusyReply ctx tid gate decoded executingCore st) ∧
      (cancelRecvBusyReply ctx tid gate decoded executingCore st).objects.invExt ∧
      queueHeadBlockedConsistent (cancelRecvBusyReply ctx tid gate decoded executingCore st) ∧
      CallerReady (cancelRecvBusyReply ctx tid gate decoded executingCore st) tid := by
    rcases cancelRecvBusyReply_cases ctx tid gate decoded executingCore st with e | ⟨hd, hne, e⟩ <;>
      rw [e]
    · exact ⟨.refl _, hInv, hIpc.queueHeadBlockedConsistent, hCaller⟩
    · exact ⟨RecordsStage.cancelReplyHolder st hd executingCore,
        cancelReplyHolder_objects_invExt st hd executingCore hInv,
        cancelReplyHolder_queueHeadBlockedConsistent st hd executingCore hInv
          (.of_ipcInvariantFull hIpc),
        hCaller.cancelReplyHolder hInv (Ne.symm hne)⟩
  obtain ⟨hS, hIC, hQC, hCC⟩ := hSC
  generalize cancelRecvBusyReply ctx tid gate decoded executingCore st = stC at h hS hIC hQC hCC
  by_cases hSig : receiveCompletesSignal ctx stC tid = true
  · -- seL4-MCS `receiveIPC`: the bound notification is completed.
    cases hRes : resolveRecvReplyId gate decoded stC with
    | error _ => rw [hRes] at h; cases h
    | ok r =>
    rw [hRes] at h
    simp only [hSig, ↓reduceIte] at h
    exact hS.trans (completeSignalArm_recordsStage hIC hCC h)
  simp only [Bool.not_eq_true] at hSig
  by_cases hNb : receiveFindsNothing (Syscall.wordReceiveBlocks (callerSyscallWord stC tid)) stC epId = true
  · -- WS-SX SX7.2: `NBRecv` with no sender waiting writes the badge register.
    cases hRes : resolveRecvReplyId gate decoded stC with
    | error _ => rw [hRes] at h; cases h
    | ok r =>
    rw [hRes] at h
    simp only [hSig, Bool.false_eq_true, hNb, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq,
      true_and] at h
    subst h
    exact hS.trans (writeReturnFrameToTcb_recordsStage _ _ _)
  simp only [Bool.not_eq_true] at hNb
  simp only [hSig, hNb, Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · cases h
  split at h
  · rename_i st1 dequeued summ sgi hRecv
    split at h
    · cases h
    rename_i stDon hHand
    cases h
    -- seL4-MCS `receiveIPC`'s return, before the endpoint: it writes no IPC
    -- state, so the receive's premises carry over it.
    obtain ⟨hIR, hQR, hCR⟩ := receiveReturnSchedContext_receivePremises
      (Syscall.wordReceiveBlocks (callerSyscallWord stC tid)) stC tid hIC hQC hCC
    exact hS.trans ((receiveReturnSchedContext_recordsStage _ _ _).trans ((RecordsStage.of_fst_eq
      (RecordsStage.endpointReceiveDualWithCapsOnCore hIR hQR hCR) hRecv).trans
      ((RecordsStage.of_frameK fun hI => RecordsFrame.applyReceiveRendezvousHandoff hI hHand).trans
        (RecordsStage.of_frameK fun hI => RecordsFrame.stageDeliveredMessage _ _ _ hI))))
  · cases h

/-- **A reply-receive whose receive completes its bound notification keeps the
records**: the reply leg (`RecordsStage.replyTransferOnCoreChecked`), then the
notification's completion on the replier the reply leg left `.ready`. -/
theorem replyRecvCompletesSignalArm_recordsStage {ctx : LabelingContext}
    {tid prevCaller : SeLe4n.ThreadId} {label : Nat} {msg : IpcMessage} {grant : Bool}
    {c : Concurrency.CoreId} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : replyRecvCompletesSignalArm ctx tid prevCaller label msg grant c st = .ok ((), st')) :
    RecordsStage st st' := by
  obtain ⟨st1, hR, hOr⟩ := replyRecvCompletesSignalArm_split h
  have hS := RecordsStage.replyTransferOnCoreChecked hR
  rcases hOr with rfl | ⟨_, ⟨t, hT, hReady⟩, hC⟩
  · exact hS
  · exact hS.trans (completeSignalArm_recordsStage (replyTransferOnCoreChecked_stepCovers c hInv hR).2
      ⟨t, (SystemState.getTcb?_eq_some_iff _ _ _).mp hT, hReady⟩ hC)

/-- **Every arm `dispatchWithCapChecked` routes keeps the records**, the
capability-only arms it delegates, the IPC arms, the audit read and drain and
the declassification included.  The IPC arms read the reachable state the
deletes carry and the running thread, `.ready` in IPC; the reply-receive
answers its caller as the caller's fault record selects
(`RecordsStage.replyRecvTransferOnCore`). -/
theorem dispatchWithCapChecked_recordsStage (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (st st' : SystemState) (P : RecordsArmPremises st) (hCaller : CallerReady st tid)
    (h : dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .ok ((), st')) :
    RecordsStage st st' := by
  unfold dispatchWithCapChecked at h
  cases hC : dispatchCapabilityOnly decoded cap tid executingCore with
  | some k =>
    rw [hC] at h
    exact dispatchCapabilityOnly_recordsStage decoded cap tid executingCore k st st' hC P
      (dispatchCapabilityOnlyChecked_ok hC h)
  | none =>
  rw [hC] at h
  dsimp only at h
  cases hId : decoded.syscallId <;> rw [hId] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  case none.auditRead =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i hA
    cases h
    exact (RecordsStage.of_frameK fun hI => RecordsFrame.auditReadFromCore hI hA).trans
      (writeCallReturnWord_recordsStage _ _ _)
  case none.auditDrain =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i hA
    cases h
    exact (RecordsStage.of_frameK fun hI => RecordsFrame.auditDrainVisiblePrefix hI hA).trans
      (writeCallReturnWord_recordsStage _ _ _)
  all_goals
    cases hT : cap.target <;> rw [hT] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  case none.send.object epId =>
    split at h
    · cases h; exact RecordsStage.refl _
    split at h
    · cases h
    rename_i hSend
    exact clearStashStage_recordsStage
      (RecordsStage.of_fst_eq (RecordsStage.endpointSendCrossCoreDispatchChecked P.deletes.1 hCaller)
        hSend)
      (fun x => stageWokenDelivery_recordsStage x _ _) h
  case none.receive.object epId =>
    split at h
    · cases h
    exact receiveResolvedArm_recordsStage ctx decoded tid executingCore gate epId st st' P hCaller h
  case none.call.object epId =>
    split at h
    · rename_i hCall
      cases h
      exact (RecordsStage.of_fst_eq
        (RecordsStage.endpointCallCrossCoreDispatchChecked P.deletes.1 hCaller) hCall).trans
        (stageWokenDelivery_recordsStage _ _ _)
    · cases h
  case none.reply.replyCap rid =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    exact RecordsStage.replyTransferOnCoreChecked h
  case none.replyRecv.object epId =>
    split at h
    · cases h
    -- WS-SX SX6.1: an extra capability that does not look up skips the reply,
    -- and the receive runs alone
    split at h
    · exact receiveResolvedArm_recordsStage ctx decoded tid executingCore gate epId st st' P hCaller h
    -- the reply's resolution: refused, a reply with no caller (the receive
    -- runs, as on a skipped reply), or a caller to answer
    split at h
    · cases h
    · exact receiveResolvedArm_recordsStage ctx decoded tid executingCore gate epId st st' P hCaller h
    repeat' split at h
    all_goals first | (cases h; done) | skip
    · exact replyRecvCompletesSignalArm_recordsStage P.deletes.2.1.2.1 h
    rename_i hX
    cases h
    exact (RecordsStage.replyRecvTransferOnCore P.deletes.1 hCaller hX).trans
      (RecordsStage.of_frameK fun hI => RecordsFrame.stageDeliveredMessage _ _ _ hI)
  case none.cspaceMint.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    all_goals
      unfold cspaceMintChecked at h
      dsimp only at h
      split at h
      · exact .of_frameK fun hI => RecordsFrame.cspaceMintWithCdt hI h
      · cases h
  case none.cspaceCopy.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold cspaceCopyChecked at h
    dsimp only at h
    split at h
    · exact .of_frameK fun hI => RecordsFrame.cspaceCopy hI h
    · cases h
  case none.cspaceMove.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold cspaceMoveChecked at h
    dsimp only at h
    split at h
    · exact .of_frameK fun hI => RecordsFrame.cspaceMove hI h
    · cases h
  case none.serviceRegister.serviceRegistry _ =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    replace h := serviceEndpointArm_ok h
    obtain ⟨_, epId, -, h⟩ := h
    try dsimp only at h
    unfold registerServiceChecked at h
    split at h
    · exact .of_frameK fun hI => RecordsFrame.registerService hI h
    · cases h
  case none.notificationSignal.object notifId =>
    try dsimp only at h
    split at h
    · rename_i hSig
      cases h
      exact (RecordsStage.of_fst_eq
        (notificationSignalBoundCrossCoreDispatchChecked_recordsStage P.deletes.1) hSig)
    · cases h
  case none.notificationWait.object notifId =>
    split at h
    · cases h; exact writeReturnFrameToTcb_recordsStage _ _ _
    unfold completeSignalArm at h
    split at h
    · rename_i hW
      cases h
      exact ((RecordsStage.of_fst_eq
        (RecordsStage.notificationWaitCrossCoreDispatchChecked P.deletes.1 hCaller) hW).trans
        (writeReturnFrameToTcb_recordsStage _ _ _)).trans
        (maybeDonateSchedContext_recordsStage _ _ _)
    · rename_i hW
      cases h
      exact (RecordsStage.of_fst_eq
        (RecordsStage.notificationWaitCrossCoreDispatchChecked P.deletes.1 hCaller) hW).trans
        (maybeReturnSchedContext_recordsStage _ _ _)
    · cases h
  case none.declassify.auditTrail code =>
    split at h
    · cases h
    exact .of_frameK fun hI => RecordsFrame.declassifyObjectFromCore hI h
  case none.declassifySignal.auditTrail code =>
    split at h
    · cases h
    try dsimp only at h
    split at h
    · rename_i hSig
      cases h
      exact (RecordsStage.of_fst_eq (notificationSignalDeclassifiedCrossCoreDispatch_recordsStage P.deletes.1) hSig)
    · cases h

/-- **The taint pass keeps the records**: it writes the taint words alone. -/
theorem applySyscallTaint_recordsStage (plan : TaintPlan) (pre post : SystemState) :
    RecordsStage post (applySyscallTaint plan pre post) :=
  .of_frameK fun hI => RecordsFrame.of_agreeOffTaint
    (applySyscallTaint_objectsAgreeOffTaint _ _ _) (by rw [applySyscallTaint_frame])
    (applySyscallTaint_invExt hI) (by rw [applySyscallTaint_machine])

/-- **The checked syscall dispatch keeps the records**: the yield, the
capability resolution (a read, so the arm runs on the dispatcher's state and
reads its premises there), the routed arm, and the taint pass, which writes the
taint words alone. -/
theorem dispatchSyscallChecked_recordsStage (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (st st' : SystemState)
    (P : RecordsArmPremises st) (hCaller : CallerReady st tid)
    (h : dispatchSyscallChecked ctx decoded tid executingCore st = .ok ((), st')) :
    RecordsStage st st' := by
  unfold dispatchSyscallChecked at h
  split at h
  · cases h
  by_cases hY : decoded.syscallId = .yield
  · simp only [hY, ↓reduceIte, dispatchYield] at h
    split at h
    · cases h
    · rename_i hYieldOk
      cases h
      exact .of_frameK fun hI => RecordsFrame.yieldOnCore hI hYieldOk
  simp only [hY, ↓reduceIte] at h
  split at h <;> try (cases h; done)
  split at h
  · cases h
  rename_i stPost hD
  cases h
  refine RecordsStage.trans (b := stPost) ?_ (applySyscallTaint_recordsStage _ _ _)
  obtain ⟨cap, -, -, hD⟩ := syscallInvokeTyped_ok _ _ _ st () stPost hD
  exact dispatchWithCapChecked_recordsStage ctx decoded tid executingCore _ cap _ stPost P
    hCaller hD

end SeLe4n.Kernel
