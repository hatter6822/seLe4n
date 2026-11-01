/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.Scheduling
import SeLe4n.Kernel.ReschedulePendingArms.Dispatch

/-!
# Every kernel entry keeps the run-queue link agreement

WS-ZA ZA4.5 part 2.  The capability-only dispatch, the capability dispatch, the
checked syscall dispatch, the timer tick and the reschedule interrupt are
`RunQueueStage`s: composed from the per-arm stages, so the run queues agree with
the threads' run-queue links after every entry that started from agreement.
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Model.SystemState (RunQueueStage)
open Architecture.RegisterDecode
open Architecture.SyscallArgDecode

/-- Between scheduling points a notification's head waiter is blocked on it,
so no core runs it. -/
theorem notificationHeadsWakeable_of {st : SystemState} (hD : st.currentDequeuedUnique)
    (hNW : notificationWaiterConsistent st) : notificationHeadsWakeable st := by
  intro nid ntfn hN w hW
  obtain ⟨tcb, hT, hB⟩ := waitHead_blocked_of_notificationWaiterConsistent hNW
    ((SystemState.getNotification?_eq_some_iff _ _ _).mp hN) hW
  have hT' : st.getTcb? w = some tcb := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hNR : tcb.ipcState ≠ .ready := by rw [hB]; exact fun h => by cases h
  exact ⟨blockedCurrentNowhere_of_currentDequeuedUnique hD w tcb hT' hNR, tcb, hT', hNR⟩

/-- **A step that changes no thread's IPC blocking**: it keeps every object
that is no TCB, every thread's IPC state and every core's current slot, and
the object store's invariant (a register save, a ledger write).  Every thread
after it was there before with the same scheduling-context binding, too, so the
current threads' contexts stay where they were (WS-ZA ZA6.4). -/
def IpcFrame (st st' : SystemState) : Prop :=
  st.objects.invExt → st'.objects.invExt ∧
    (∀ (k : SeLe4n.ObjId) (o : KernelObject), (∀ t : TCB, o ≠ .tcb t) →
      st'.objects[k]? = some o → st.objects[k]? = some o) ∧
    (∀ (w : SeLe4n.ThreadId) (t' : TCB), st'.getTcb? w = some t' →
      ∃ t, st.getTcb? w = some t ∧ t.ipcState = t'.ipcState ∧
        t.schedContextBinding = t'.schedContextBinding) ∧
    (∀ (w : SeLe4n.ThreadId) (t : TCB), st.getTcb? w = some t →
      ∃ t', st'.getTcb? w = some t' ∧ t'.ipcState = t.ipcState) ∧
    (∀ c : Concurrency.CoreId, st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c)

namespace IpcFrame

variable {st st' st'' : SystemState}

theorem refl (st : SystemState) : IpcFrame st st :=
  fun h => ⟨h, fun _ _ _ h => h, fun _ t' h => ⟨t', h, rfl, rfl⟩, fun _ t h => ⟨t, h, rfl⟩,
    fun _ => rfl⟩

theorem trans (h1 : IpcFrame st st') (h2 : IpcFrame st' st'') : IpcFrame st st'' := fun h =>
  let ⟨h', a1, b1, c1, d1⟩ := h1 h
  let ⟨h'', a2, b2, c2, d2⟩ := h2 h'
  ⟨h'', fun k o ho hk => a1 k o ho (a2 k o ho hk),
    fun w t'' hw =>
      let ⟨t', ht', e2, f2⟩ := b2 w t'' hw
      let ⟨t, ht, e1, f1⟩ := b1 w t' ht'
      ⟨t, ht, e1.trans e2, f1.trans f2⟩,
    fun w t hw =>
      let ⟨t', ht', e1⟩ := c1 w t hw
      let ⟨t'', ht'', e2⟩ := c2 w t' ht'
      ⟨t'', ht'', e2.trans e1⟩,
    fun c => (d2 c).trans (d1 c)⟩

/-- A step that keeps the object store and every current slot. -/
theorem of_frame (hO : st'.objects = st.objects)
    (hC : ∀ c, st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c) :
    IpcFrame st st' := fun h =>
  have hT : ∀ w, st'.getTcb? w = st.getTcb? w := fun w => by
    unfold SystemState.getTcb?; rw [hO]
  ⟨by rw [hO]; exact h, fun _ _ _ hk => hO ▸ hk, fun w t' hw => ⟨t', (hT w) ▸ hw, rfl, rfl⟩,
    fun w t hw => ⟨t, (hT w).symm ▸ hw, rfl⟩, hC⟩

/-- A write to one TCB that keeps its IPC state and its binding. -/
theorem updateTcb (st : SystemState) (tid : SeLe4n.ThreadId) {f : TCB → TCB}
    (hf : ∀ x, (f x).ipcState = x.ipcState)
    (hb : ∀ x, (f x).schedContextBinding = x.schedContextBinding := by intro _; rfl) :
    IpcFrame st (st.updateTcb tid f) := fun h =>
  ⟨SystemState.updateTcb_preserves_objects_invExt _ _ _ h,
    fun _ _ ho hk => updateTcb_objects_back_nonTcb h ho hk,
    fun w t' hw => by
      rw [updateTcb_getTcb?_eq h] at hw
      split at hw
      · obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hw
        exact ⟨t, ht, (hf t).symm, (hb t).symm⟩
      · exact ⟨t', hw, rfl, rfl⟩,
    fun _ _ hw => updateTcb_getTcb?_fwd h hf hw,
    fun _ => by rw [SystemState.updateTcb_scheduler]⟩

end IpcFrame

/-- What a kernel entry reads off the state it starts from: the three placement
properties, the endpoint queues' heads and the notifications' head waiters
blocked, and every core's current context placeable on its core (WS-ZA ZA6.4:
what the bound yield's postpone needs). -/
structure EntryPremises (st : SystemState) : Prop where
  objInv : st.objects.invExt
  refined : st.runQueueRefined
  dequeued : st.currentDequeuedUnique
  queueHeads : queueHeadBlockedConsistent st
  ntfnHeads : notificationHeadsWakeable st
  placeable : ∀ c, st.currentContextPlaceableOnCore c

/-- What a syscall arm reads besides: the caller is core `c`'s current thread and
no idle thread (an idle thread runs the kernel's own loop and never traps). -/
structure SyscallArmPremises (st : SystemState) (c : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) : Prop extends EntryPremises st where
  current : st.scheduler.currentOnCore c = some tid
  notIdle : isIdleThreadId tid = false

namespace EntryPremises

variable {st st' : SystemState}

/-- The premises from the state's invariants. -/
theorem of_invariants (hInv : st.objects.invExt) (hR : st.runQueueRefined)
    (hD : st.currentDequeuedUnique) (hQ : queueHeadBlockedConsistent st)
    (hNW : notificationWaiterConsistent st) (hP : ∀ c, st.currentContextPlaceableOnCore c) :
    EntryPremises st :=
  ⟨hInv, hR, hD, hQ, notificationHeadsWakeable_of hD hNW, hP⟩

theorem endpointHeads (E : EntryPremises st) : endpointHeadsWakeable st :=
  endpointHeadsWakeable_of E.dequeued E.queueHeads

theorem blocked (E : EntryPremises st) : blockedCurrentNowhere st :=
  blockedCurrentNowhere_of_currentDequeuedUnique E.dequeued

/-- The premises hold after a stage that changes no thread's IPC blocking. -/
theorem of_ipcFrame (E : EntryPremises st) (hS : RunQueueStage st st') (hF : IpcFrame st st') :
    EntryPremises st' :=
  let hL := hS.1 E.objInv E.refined
  let ⟨_, hNT, hTB, hTF, hC⟩ := hF E.objInv
  { objInv := hL.1, refined := hL.2
    dequeued := hS.2.1 none E.objInv E.refined hL.2 E.dequeued
    queueHeads := queueHeadBlockedConsistent_of_endpoint_tcb_backward st st'
      (fun _ _ hE => hNT _ _ (fun _ h => by cases h) hE)
      (fun y t' hY =>
        let ⟨t, ht, hs, _⟩ := hTB y t' ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hY)
        ⟨t, (SystemState.getTcb?_eq_some_iff _ _ _).mp ht, hs⟩) E.queueHeads
    ntfnHeads := fun nid ntfn hN w hW => by
      have hN0 : st.getNotification? nid = some ntfn :=
        (SystemState.getNotification?_eq_some_iff _ _ _).mpr (hNT _ _ (fun _ h => by cases h)
          ((SystemState.getNotification?_eq_some_iff _ _ _).mp hN))
      obtain ⟨hCN, t, ht, hb⟩ := E.ntfnHeads nid ntfn hN0 w hW
      obtain ⟨t', ht', hs⟩ := hTF w t ht
      exact ⟨fun c => by rw [hC c]; exact hCN c, t', ht', by rw [hs]; exact hb⟩
    placeable := fun c tid tcb' scId sc hCur hT hb hS => by
      rw [hC c] at hCur
      obtain ⟨t, ht, -, hbd⟩ := hTB tid tcb' hT
      have hS0 : st.getSchedContext? scId = some sc :=
        (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr (hNT _ _ (fun _ h => by cases h)
          ((SystemState.getSchedContext?_eq_some_iff _ _ _).mp hS))
      obtain ⟨h1, h2⟩ := E.placeable c tid t scId sc hCur ht (by rw [hbd]; exact hb) hS0
      refine ⟨h1, ?_⟩
      unfold SystemState.releaseFreeFor SystemState.releaseCoreOf at h2 ⊢
      rw [hS]; rw [hS0] at h2; exact h2 }

/-- The caller's premises: core `c`'s current thread, no idle thread. -/
theorem arm (E : EntryPremises st) {c : Concurrency.CoreId} {tid : SeLe4n.ThreadId}
    (hCur : st.scheduler.currentOnCore c = some tid) (hNI : isIdleThreadId tid = false) :
    SyscallArmPremises st c tid :=
  { toEntryPremises := E, current := hCur, notIdle := hNI }

end EntryPremises

namespace SyscallArmPremises

variable {st st' : SystemState} {c : Concurrency.CoreId} {tid : SeLe4n.ThreadId}

theorem endpointHeads (P : SyscallArmPremises st c tid) : endpointHeadsWakeable st :=
  P.toEntryPremises.endpointHeads

theorem blocked (P : SyscallArmPremises st c tid) : blockedCurrentNowhere st :=
  P.toEntryPremises.blocked

/-- The premises hold after a stage that changes no thread's IPC blocking. -/
theorem of_ipcFrame (P : SyscallArmPremises st c tid) (hS : RunQueueStage st st')
    (hF : IpcFrame st st') : SyscallArmPremises st' c tid :=
  (P.toEntryPremises.of_ipcFrame hS hF).arm
    (by rw [(hF P.objInv).2.2.2.2 c]; exact P.current) P.notIdle

end SyscallArmPremises

/-- A validated thread operand is no core's idle thread. -/
theorem validateThreadIdArg_ok_val_not_idle {tid : SeLe4n.ThreadId} {vtid : SeLe4n.ValidThreadId}
    (h : validateThreadIdArg tid = .ok vtid) : isIdleThreadId vtid.val = false := by
  rw [SeLe4n.ThreadId.toValid?_some_val_eq _ _ (validateThreadIdArg_ok_toValid? _ _ h)]
  exact validateThreadIdArg_ok_not_reserved _ _ h

/-- The capability-only dispatch keeps the run queues in agreement with the
threads' links on every arm. -/
theorem dispatchCapabilityOnly_runQueueEntryStage
    (decoded : SyscallDecodeResult) (cap : Capability) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (k : Kernel Unit) (st st' : SystemState)
    (hArm : dispatchCapabilityOnly decoded cap tid executingCore = some k)
    (hStep : k st = .ok ((), st')) :
    SystemState.RunQueueEntryStage st st' := by
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
          exact cspaceDeleteSlotZombie_runQueueEntryStage hStep
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
          exact cspaceRevokeCdtFinalising_runQueueEntryStage hStep
    all_goals try cases hStep
  case mintReplyCap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object cnodeId =>
      try dsimp only [] at hStep
      cases hDec : decodeCSpaceCopyArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          refine RunQueueStage.entry ?_
          exact mintReplyCapWithCdt_runQueueStage hStep
    all_goals try cases hStep
  case untypedRetype =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object _ =>
      refine RunQueueStage.entry ?_
      exact untypedRetypeFromCap_runQueueStage hStep
    all_goals try cases hStep
  case untypedReset =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object _ =>
      refine RunQueueStage.entry ?_
      obtain ⟨_, _, _, -, -, hS⟩ := untypedResetFromCap_ok _ _ _ _ hStep
      exact untypedResetSlot_runQueueStage hS
    all_goals try cases hStep
  case vspaceMap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      cases hDec : decodeVSpaceMapArgs decoded st.machine.maxASID with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          · refine RunQueueStage.entry ?_
            exact vspaceMapFromFrameCap_runQueueStage hStep
    all_goals try cases hStep
  case vspaceUnmap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      cases hDec : decodeVSpaceUnmapArgs decoded st.machine.maxASID with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          · refine RunQueueStage.entry ?_
            exact vspaceUnmapPageWithShootdownAndIcacheBroadcast_runQueueStage hStep
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
          · refine RunQueueStage.entry ?_
            exact vspaceUnifyInstructionPage_runQueueStage hStep
    all_goals try cases hStep
  case serviceRevoke =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      obtain ⟨_, hRev⟩ := revokeServiceByRecordedRegistration_revokeService hStep
      refine RunQueueStage.entry ?_
      exact revokeService_runQueueStage hRev
    all_goals try cases hStep
  case serviceQuery =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object epId =>
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
          refine RunQueueStage.entry ?_
          exact writeReturnFrameToTcb_runQueueStage _ _ _
    all_goals try cases hStep
  case schedContextConfigure =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case schedControl core =>
      try dsimp only [] at hStep
      cases hDec : decodeSchedContextConfigureArgsChecked decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : resolveSchedControlConfigureTarget tid core args.scCPtr st with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vScId =>
              simp only [hVal] at hStep
              split at hStep
              · exact schedControlConfigure_runQueueEntryStage hStep
              · cases hStep
    all_goals try cases hStep
  case schedContextBind =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hRes : resolveSchedContextBindThread tid (decodeSchedContextBindArgs decoded) st with
      | error e => simp only [hRes] at hStep; cases hStep
      | ok vThreadId =>
          simp only [hRes] at hStep
          cases hVal : validateObjIdArg scId with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vScId =>
              simp only [hVal] at hStep
              refine RunQueueStage.entry ?_
              exact schedContextBind_runQueueStage hStep
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
              cases hUn : SchedContextOps.schedContextUnbindOnCore vScId
                  executingCore st with
              | error e => simp only [hUn] at hStep; cases hStep
              | ok pair =>
                  obtain ⟨stU, sgiU⟩ := pair
                  simp only [hUn] at hStep
                  cases hStep
                  exact schedContextUnbindOnCore_runQueueEntryStage hUn
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
              exact SystemState.schedContextConsumedOnCore_runQueueEntryStage hC
    all_goals try cases hStep
  case tcbBindNotification =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object tcbObjId =>
      try dsimp only [] at hStep
      cases hDec : decodeTcbBindNotificationArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hCaller : st.getTcb? tid with
          | none => simp only [hCaller] at hStep; cases hStep
          | some callerTcb =>
              simp only [hCaller] at hStep
              cases hRoot : st.getCNode? callerTcb.cspaceRoot with
              | none => simp only [hRoot] at hStep; cases hStep
              | some rootCn =>
                  simp only [hRoot] at hStep
                  try dsimp only [] at hStep
                  cases hCap2 : syscallLookupCap { callerId := tid, cspaceRoot := callerTcb.cspaceRoot, capAddr := args.notificationCPtr, capDepth := rootCn.depth, requiredRight := .write } st with
                  | error e => simp only [hCap2] at hStep; cases hStep
                  | ok pair =>
                      obtain ⟨ntfnCap, stL⟩ := pair
                      simp only [hCap2] at hStep
                      cases hNT : ntfnCap.target with
                      | object notifId =>
                          simp only [hNT] at hStep
                          refine RunQueueStage.entry ?_
                          exact bindNotification_runQueueStage hStep
                      | _ => simp only [hNT] at hStep; cases hStep
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
          refine RunQueueStage.entry ?_
          exact unbindNotification_runQueueStage hUn
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
                  exact suspendThreadOnCore_runQueueEntryStage
                    (validateThreadIdArg_ok_val_not_idle hVal) hSus
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
          cases hRes : Lifecycle.Suspend.resumeThreadOnCore
              (retirePendingFaultForResume st vtid.val) vtid
              executingCore with
          | error e => simp only [hRes] at hStep; cases hStep
          | ok pair =>
              obtain ⟨stU, sgiU⟩ := pair
              simp only [hRes] at hStep
              cases hStep
              exact (retirePendingFaultForResume_runQueueStage st vtid.val).entry.trans
                  (resumeThreadOnCore_runQueueEntryStage hRes)
    all_goals try cases hStep
  case tcbSetPriority =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeSetPriorityArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hValC : validateThreadIdArg tid with
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
                      exact setPriorityOnCore_runQueueEntryStage hSet
    all_goals try cases hStep
  case tcbSetMCPriority =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeSetMCPriorityArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hValC : validateThreadIdArg tid with
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
                      exact setMCPriorityOnCore_runQueueEntryStage hSet
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
              cases hSet : Architecture.IpcBufferValidation.setIPCBufferOp st vtid
                  args.bufferAddr with
              | error e => simp only [hSet] at hStep; cases hStep
              | ok stU =>
                  simp only [hSet] at hStep
                  cases hStep
                  refine RunQueueStage.entry ?_
                  exact setIPCBufferOp_runQueueStage hSet
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
                      exact setThreadCpuAffinityOnCore_runQueueEntryStage hSet
    all_goals try cases hStep
  case tcbSetFaultHandler =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : Architecture.SyscallArgDecode.decodeSetFaultHandlerArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vtid =>
              simp only [hVal] at hStep
              cases hSet : setThreadFaultHandlerOp st vtid args.handlerCPtr with
              | error e => simp only [hSet] at hStep; cases hStep
              | ok stU =>
                  simp only [hSet] at hStep
                  cases hStep
                  refine RunQueueStage.entry ?_
                  exact setThreadFaultHandlerOp_runQueueStage hSet
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
              cases hR : resolveSetSpace tid args st with
              | error e => simp only [hR] at hStep; cases hStep
              | ok p =>
                  obtain ⟨cn, vr⟩ := p
                  simp only [hR] at hStep
                  cases hSet : copyThreadSpacesZombie executingCore st vtid cn vr with
                  | error e => simp only [hSet] at hStep; cases hStep
                  | ok stU =>
                      simp only [hSet] at hStep
                      cases hStep
                      exact copyThreadSpacesZombie_runQueueEntryStage hSet
    all_goals try cases hStep
  case pageTableMap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : Architecture.SyscallArgDecode.decodePageTableMapArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hR : resolveCallerCapObject tid args.vspaceRoot .write st with
          | error e => simp only [hR] at hStep; cases hStep
          | ok p =>
              obtain ⟨_, rootId⟩ := p
              simp only [hR] at hStep
              refine RunQueueStage.entry ?_
              exact pageTableMap_runQueueStage hStep
    all_goals try cases hStep
  case pageTableUnmap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      refine RunQueueStage.entry ?_
      exact pageTableUnmap_runQueueStage hStep
    all_goals try cases hStep

/-! ### The wrapping steps of the capability dispatch -/

/-- Clearing a woken receiver's stash rewrites one TCB's stash field. -/
theorem clearWokenReceiverStash_runQueueStage (receiver? : Option SeLe4n.ThreadId)
    {st st' : SystemState} (h : clearWokenReceiverStash receiver? st = .ok ((), st')) :
    RunQueueStage st st' := by
  unfold clearWokenReceiverStash at h
  split at h
  · cases h; exact RunQueueStage.refl _
  · split at h
    · rename_i rTcb hT
      split at h
      · exact storeObject_tcbOver_runQueueStage hT h (fun _ => rfl)
      · cases h; exact RunQueueStage.refl _
    · cases h; exact RunQueueStage.refl _

/-- Read a pair-returning transition's stage off the equation naming its result. -/
theorem runQueueStage_of_pair_eq {α : Type} {R : SystemState → SystemState → Prop}
    {st s : SystemState} {p : SystemState × α}
    {r : α} (hS : R st p.1) (hEq : p = (s, r)) : R st s := by
  subst hEq; exact hS

/-- The tail every waking arm ends with: clear the woken receiver's stash, then
stage the delivered frames. -/
theorem clearStashStage_runQueueEntryStage {st s st' : SystemState}
    {woken? : Option SeLe4n.ThreadId} {stage : SystemState → SystemState}
    (hS : SystemState.RunQueueEntryStage st s) (hStage : ∀ x, RunQueueStage x (stage x))
    (h : (match clearWokenReceiverStash woken? s with
      | .error e => .error e
      | .ok ((), s') => .ok ((), stage s')) =
        (.ok ((), st') : Except KernelError (Unit × SystemState))) :
    SystemState.RunQueueEntryStage st st' := by
  split at h
  · cases h
  · rename_i s3 hClr
    cases h
    exact hS.trans ((clearWokenReceiverStash_runQueueStage woken? hClr).trans (hStage _)).entry

/-- The two badge stagings a signal arm ends with. -/
theorem stageWokenDeliveryTwice_runQueueStage (x : SystemState) (w p : Option SeLe4n.ThreadId) :
    RunQueueStage x (Architecture.stageWokenDelivery
      (Architecture.stageWokenDelivery x w 0) p 0) :=
  (stageWokenDelivery_runQueueStage x w 0).trans (stageWokenDelivery_runQueueStage _ p 0)

theorem endpointSendCrossCoreDispatchChecked_runQueueEntryStage (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (payload : SendPayload)
    (base : SeLe4n.Slot) (c : Concurrency.CoreId)
    (st : SystemState) (P : SyscallArmPremises st c sender) :
    SystemState.RunQueueEntryStage st
      (endpointSendCrossCoreDispatchChecked ctx endpointId sender payload base c st).1 := by
  unfold endpointSendCrossCoreDispatchChecked
  repeat' split
  all_goals first
    | exact (RunQueueStage.refl _).entry
    | exact endpointSendDualWithCapsOnCore_runQueueEntryStage _ _ _ _ _ _ P.endpointHeads
        P.current P.notIdle

theorem endpointCallCrossCoreDispatchChecked_runQueueEntryStage (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (payload : SendPayload)
    (base : SeLe4n.Slot) (c : Concurrency.CoreId)
    (st : SystemState) (P : SyscallArmPremises st c caller) :
    SystemState.RunQueueEntryStage st
      (endpointCallCrossCoreDispatchChecked ctx endpointId caller payload base c st).1 := by
  unfold endpointCallCrossCoreDispatchChecked
  split
  · exact endpointCallCrossCoreDispatch_runQueueEntryStage _ _ _ _ _ _ P.endpointHeads
      P.current P.notIdle
  · exact (RunQueueStage.refl _).entry

theorem notificationSignalBoundCrossCoreDispatchChecked_runQueueStage (ctx : LabelingContext)
    (notificationId : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId) (badge : SeLe4n.Badge)
    (c : Concurrency.CoreId) (st : SystemState) (hHeads : notificationHeadsWakeable st)
    (hBlk : blockedCurrentNowhere st) :
    RunQueueStage st (notificationSignalBoundCrossCoreDispatchChecked ctx notificationId
      signaler badge c st).1 := by
  unfold notificationSignalBoundCrossCoreDispatchChecked
  repeat' split
  all_goals first
    | exact RunQueueStage.refl _
    | exact notificationSignalBoundOnCore_runQueueStage _ _ _ _ hHeads hBlk

theorem notificationWaitCrossCoreDispatchChecked_runQueueEntryStage (ctx : LabelingContext)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (c : Concurrency.CoreId)
    (st : SystemState) (P : SyscallArmPremises st c waiter) :
    SystemState.RunQueueEntryStage st
      (notificationWaitCrossCoreDispatchChecked ctx notificationId waiter c st).1 := by
  unfold notificationWaitCrossCoreDispatchChecked
  split
  · exact notificationWaitOnCore_runQueueEntryStage _ _ _ _ P.current P.notIdle
  · exact (RunQueueStage.refl _).entry

/-- The declassified signal: the bound signal, then the audit records, which
touch the trail alone. -/
theorem notificationSignalDeclassifiedOnCore_runQueueStage (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : Concurrency.CoreId) (st : SystemState)
    (hHeads : notificationHeadsWakeable st) (hBlk : blockedCurrentNowhere st) :
    RunQueueStage st
      (notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge c st).1 := by
  unfold notificationSignalDeclassifiedOnCore
  split
  · exact RunQueueStage.refl _
  split
  · split <;> exact RunQueueStage.refl _
  dsimp only
  split
  · exact RunQueueStage.refl _
  have hB := notificationSignalBoundOnCore_runQueueStage notificationId badge c st hHeads hBlk
  generalize notificationSignalBoundOnCore notificationId badge c st = r at hB
  obtain ⟨st1, res⟩ := r
  cases res with
  | error _ => exact RunQueueStage.refl _
  | ok sgi =>
    dsimp only at hB ⊢
    split
    · exact RunQueueStage.refl _
    · rename_i st2 hRec
      rw [recordDeclassifiedHops_frame _ _ _ _ _ hRec]
      exact hB.trans (RunQueueStage.of_frame rfl rfl rfl)

/-- **Every arm `dispatchWithCapChecked` routes keeps the run queues in
agreement with the threads' links**, the capability-only arms it delegates
included. -/
theorem dispatchWithCapChecked_runQueueEntryStage (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (st st' : SystemState)
    (P : SyscallArmPremises st executingCore tid)
    (h : dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .ok ((), st')) :
    SystemState.RunQueueEntryStage st st' := by
  unfold dispatchWithCapChecked at h
  cases hC : dispatchCapabilityOnly decoded cap tid executingCore with
  | some k =>
    rw [hC] at h
    exact dispatchCapabilityOnly_runQueueEntryStage decoded cap tid executingCore k st st' hC
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
    rw [auditReadFromCore_frame _ _ _ _ _ _ _ hA]
    refine RunQueueStage.entry ?_
    exact writeReturnFrameToTcb_runQueueStage _ _ _
  case none.auditDrain =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i hA
    cases h
    unfold auditDrainVisiblePrefix at hA
    split at hA
    · cases hA
      refine RunQueueStage.entry ?_
      refine RunQueueStage.trans ?_ (writeReturnFrameToTcb_runQueueStage _ _ _)
      exact RunQueueStage.of_frame rfl rfl rfl
    · cases hA
  all_goals
    cases hT : cap.target <;> rw [hT] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  case none.send.object epId =>
    split at h
    · cases h
    rename_i hSend
    exact clearStashStage_runQueueEntryStage
      ((runQueueStage_of_pair_eq
        (endpointSendCrossCoreDispatchChecked_runQueueEntryStage _ _ _ _ _ _ _ P) hSend))
      (fun x => stageWokenDelivery_runQueueStage x _ _) h
  case none.receive.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i summ _ hRecv _ stDon hHand
    cases h
    exact (runQueueStage_of_pair_eq
      (endpointReceiveDualWithCapsOnCore_runQueueEntryStage _ _ _ _ _ _ _ P.endpointHeads
        P.current P.notIdle) hRecv).trans
      (((applyReceiveRendezvousHandoff_runQueueStage hHand).trans
        (stageWokenSendCompletion_runQueueStage _ _)).trans
        (stageDeliveredMessage_runQueueStage _ _ _)).entry
  case none.call.object epId =>
    split at h
    · rename_i hCall
      cases h
      exact ((runQueueStage_of_pair_eq
        (endpointCallCrossCoreDispatchChecked_runQueueEntryStage _ _ _ _ _ _ _ P) hCall)).trans
        (stageWokenDelivery_runQueueStage _ _ _).entry
    · cases h
  case none.reply.replyCap rid =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    exact replyTransferOnCoreChecked_runQueueEntryStage P.objInv P.dequeued h
  case none.cspaceMint.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    all_goals
      unfold cspaceMintChecked at h
      dsimp only at h
      split at h
      · refine RunQueueStage.entry ?_
        exact cspaceMintWithCdt_runQueueStage h
      · cases h
  case none.cspaceCopy.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold cspaceCopyChecked at h
    dsimp only at h
    split at h
    · refine RunQueueStage.entry ?_
      exact cspaceCopy_runQueueStage h
    · cases h
  case none.cspaceMove.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold cspaceMoveChecked at h
    dsimp only at h
    split at h
    · refine RunQueueStage.entry ?_
      exact cspaceMove_runQueueStage h
    · cases h
  case none.serviceRegister.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    unfold registerServiceChecked at h
    split at h
    · refine RunQueueStage.entry ?_
      exact registerService_runQueueStage h
    · cases h
  case none.notificationSignal.object notifId =>
    split at h
    · cases h
    try dsimp only at h
    split at h
    · rename_i hSig
      exact clearStashStage_runQueueEntryStage (runQueueStage_of_pair_eq
        (notificationSignalBoundCrossCoreDispatchChecked_runQueueStage _ _ _ _ _ _ P.ntfnHeads
          P.blocked) hSig).entry
        (fun x => stageWokenDeliveryTwice_runQueueStage x _ _) h
    · cases h
  case none.notificationWait.object notifId =>
    split at h
    · rename_i hW
      cases h
      exact (runQueueStage_of_pair_eq
        (notificationWaitCrossCoreDispatchChecked_runQueueEntryStage _ _ _ _ _ P) hW).trans
        (writeReturnFrameToTcb_runQueueStage _ _ _).entry
    · rename_i hW
      cases h
      exact runQueueStage_of_pair_eq
        (notificationWaitCrossCoreDispatchChecked_runQueueEntryStage _ _ _ _ _ P) hW
    · cases h
  case none.replyRecv.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i summ stR hRR
    cases h
    exact (endpointReplyRecvOnCore_runQueueEntryStage P.objInv P.dequeued P.queueHeads
      P.current P.notIdle hRR).trans (stageDeliveredMessage_runQueueStage _ _ _).entry
  case none.declassify.object targetId =>
    unfold declassifyObjectFromCore at h
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rw [(authorizeDeclassificationOnCore_frame _ _ _ _ _ _ _ _ _ h).1]
    refine RunQueueStage.entry ?_
    exact RunQueueStage.of_frame rfl rfl rfl
  case none.declassifySignal.object notifId =>
    split at h
    · cases h
    try dsimp only at h
    split at h
    · rename_i hSig
      exact clearStashStage_runQueueEntryStage (runQueueStage_of_pair_eq
        (notificationSignalDeclassifiedOnCore_runQueueStage _ _ _ _ _ _ P.ntfnHeads
          P.blocked) hSig).entry
        (fun x => stageWokenDeliveryTwice_runQueueStage x _ _) h
    · cases h

/-- **The checked syscall dispatch keeps the run queues in agreement with the
threads' links**: the yield, the capability resolution (a read), the routed arm,
and the taint pass, which writes the taint table and the taint words alone.  The one premise is the
retype arm's detached target. -/
theorem dispatchSyscallChecked_runQueueEntryStage (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (st st' : SystemState)
    (P : SyscallArmPremises st executingCore tid)
    (h : dispatchSyscallChecked ctx decoded tid executingCore st = .ok ((), st')) :
    SystemState.RunQueueEntryStage st st' := by
  unfold dispatchSyscallChecked at h
  split at h
  · cases h
  by_cases hY : decoded.syscallId = .yield
  · simp only [hY, ↓reduceIte, dispatchYield] at h
    split at h
    · cases h
    · rename_i hYieldOk
      cases h
      exact yieldOnCore_runQueueEntryStage hYieldOk (P.placeable executingCore)
  simp only [hY, ↓reduceIte] at h
  split at h <;> try (cases h; done)
  split at h <;> try (cases h; done)
  cases hTF : syscallChecksTargetFirst decoded.syscallId <;>
    simp only [hTF, Bool.false_eq_true, ↓reduceIte] at h
  all_goals
    split at h
    · cases h
    rename_i stPost hD
    cases h
    refine SystemState.RunQueueEntryStage.trans (st' := stPost) ?_ (RunQueueStage.of_objectsAgreeOffTaint
      (applySyscallTaint_objectsAgreeOffTaint _ _ _) applySyscallTaint_invExt
      (fun _ => applySyscallTaint_preserves_tableReferencesRecorded)
      (by rw [applySyscallTaint_scheduler]) (by rw [applySyscallTaint_scheduler])
      (by rw [applySyscallTaint_scheduler]) (by rw [applySyscallTaint_scheduler])).entry
  · unfold syscallInvoke at hD
    split at hD
    · cases hD
    · rename_i cap s1 hLk
      have hRz := syscallResolveCap_of_lookup _ st cap s1 hLk
      obtain ⟨-, -, -, hStEq⟩ := syscallResolveCap_implies_capability_at_slot _ st cap s1 hRz
      subst hStEq
      exact dispatchWithCapChecked_runQueueEntryStage ctx decoded tid executingCore _ cap _ stPost
        P hD
  · unfold syscallInvokeResolved at hD
    split at hD
    · cases hD
    · rename_i cap s1 hRz
      obtain ⟨-, -, -, hStEq⟩ := syscallResolveCap_implies_capability_at_slot _ st cap s1 hRz
      subst hStEq
      exact dispatchWithCapChecked_runQueueEntryStage ctx decoded tid executingCore _ cap _ stPost
        P hD

/-- **Every arm the unchecked `dispatchWithCap` routes keeps the run queues in
agreement with the threads' links**, the capability-only arms included. -/
theorem dispatchWithCap_runQueueEntryStage (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (st st' : SystemState)
    (P : SyscallArmPremises st executingCore tid)
    (h : dispatchWithCap decoded tid executingCore gate cap st = .ok ((), st')) :
    SystemState.RunQueueEntryStage st st' := by
  unfold dispatchWithCap at h
  cases hC : dispatchCapabilityOnly decoded cap tid executingCore with
  | some k =>
    rw [hC] at h
    exact dispatchCapabilityOnly_runQueueEntryStage decoded cap tid executingCore k st st' hC h
  | none =>
  rw [hC] at h
  dsimp only at h
  cases hId : decoded.syscallId <;> rw [hId] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  all_goals
    cases hT : cap.target <;> rw [hT] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  case none.send.object epId =>
    split at h
    · cases h
    rename_i hSend
    exact clearStashStage_runQueueEntryStage
      ((runQueueStage_of_pair_eq
        (endpointSendDualWithCapsOnCore_runQueueEntryStage _ _ _ _ _ _ P.endpointHeads
          P.current P.notIdle) hSend))
      (fun x => stageWokenDelivery_runQueueStage x _ _) h
  case none.receive.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i summ _ hRecv _ stDon hHand
    cases h
    exact (runQueueStage_of_pair_eq
      (endpointReceiveDualWithCapsOnCore_runQueueEntryStage _ _ _ _ _ _ _ P.endpointHeads
        P.current P.notIdle) hRecv).trans
      (((applyReceiveRendezvousHandoff_runQueueStage hHand).trans
        (stageWokenSendCompletion_runQueueStage _ _)).trans
        (stageDeliveredMessage_runQueueStage _ _ _)).entry
  case none.call.object epId =>
    split at h
    · rename_i hCall
      cases h
      exact ((runQueueStage_of_pair_eq
        (endpointCallCrossCoreDispatch_runQueueEntryStage _ _ _ _ _ _ P.endpointHeads
          P.current P.notIdle) hCall)).trans
        (stageWokenDelivery_runQueueStage _ _ _).entry
    · cases h
  case none.reply.replyCap rid =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    exact replyTransferOnCore_runQueueEntryStage P.objInv P.dequeued h
  case none.cspaceMint.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    all_goals exact (cspaceMintWithCdt_runQueueStage h).entry
  case none.cspaceCopy.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    refine RunQueueStage.entry ?_
    exact cspaceCopy_runQueueStage h
  case none.cspaceMove.object cnodeId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    refine RunQueueStage.entry ?_
    exact cspaceMove_runQueueStage h
  case none.serviceRegister.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    refine RunQueueStage.entry ?_
    exact registerService_runQueueStage h
  case none.notificationSignal.object notifId =>
    split at h
    · cases h
    try dsimp only at h
    split at h
    · rename_i hSig
      exact clearStashStage_runQueueEntryStage (runQueueStage_of_pair_eq
        (notificationSignalBoundOnCore_runQueueStage _ _ _ _ P.ntfnHeads P.blocked) hSig).entry
        (fun x => stageWokenDeliveryTwice_runQueueStage x _ _) h
    · cases h
  case none.notificationWait.object notifId =>
    split at h
    · rename_i hW
      cases h
      exact (runQueueStage_of_pair_eq (notificationWaitOnCore_runQueueEntryStage _ _ _ _
        P.current P.notIdle) hW).trans (writeReturnFrameToTcb_runQueueStage _ _ _).entry
    · rename_i hW
      cases h
      exact runQueueStage_of_pair_eq (notificationWaitOnCore_runQueueEntryStage _ _ _ _
        P.current P.notIdle) hW
    · cases h
  case none.replyRecv.object epId =>
    repeat' split at h
    all_goals first | (cases h; done) | skip
    rename_i summ stR hRR
    cases h
    exact (endpointReplyRecvOnCore_runQueueEntryStage P.objInv P.dequeued P.queueHeads
      P.current P.notIdle hRR).trans (stageDeliveredMessage_runQueueStage _ _ _).entry

/-- **The unchecked syscall dispatch keeps the run queues in agreement with the
threads' links.** -/
theorem dispatchSyscall_runQueueEntryStage (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (st st' : SystemState)
    (P : SyscallArmPremises st executingCore tid)
    (h : dispatchSyscall decoded tid executingCore st = .ok ((), st')) :
    SystemState.RunQueueEntryStage st st' := by
  unfold dispatchSyscall at h
  split at h
  · cases h
  by_cases hY : decoded.syscallId = .yield
  · simp only [hY, ↓reduceIte, dispatchYield] at h
    split at h
    · cases h
    · rename_i hYieldOk
      cases h
      exact yieldOnCore_runQueueEntryStage hYieldOk (P.placeable executingCore)
  simp only [hY, ↓reduceIte] at h
  split at h <;> try (cases h; done)
  split at h <;> try (cases h; done)
  split at h
  · cases h
  rename_i stPost hD
  cases h
  refine SystemState.RunQueueEntryStage.trans (st' := stPost) ?_ (RunQueueStage.of_objectsAgreeOffTaint
    (applySyscallTaint_objectsAgreeOffTaint _ _ _) applySyscallTaint_invExt
    (fun _ => applySyscallTaint_preserves_tableReferencesRecorded)
    (by rw [applySyscallTaint_scheduler]) (by rw [applySyscallTaint_scheduler])
    (by rw [applySyscallTaint_scheduler]) (by rw [applySyscallTaint_scheduler])).entry
  unfold syscallInvoke at hD
  split at hD
  · cases hD
  · rename_i cap s1 hLk
    have hRz := syscallResolveCap_of_lookup _ st cap s1 hLk
    obtain ⟨-, -, -, hStEq⟩ := syscallResolveCap_implies_capability_at_slot _ st cap s1 hRz
    subst hStEq
    exact dispatchWithCap_runQueueEntryStage decoded tid executingCore _ cap _ stPost
      P hD

end SeLe4n.Kernel
