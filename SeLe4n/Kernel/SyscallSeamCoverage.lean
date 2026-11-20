/-
  seLe4n — Syscall seam coverage (WS-LS LS2.3)

  The ABI syscall step, the state-committing seam a declared footprint
  brackets, is covered by the footprint it declares: every object-store, run-queue and replenish-queue write the step
  makes is under a lock the footprint names (`footprintCoversWrites`).

  What this module discharges is the `hCover` premise of
  `unifiedLockSetForSyscall_coversWrites`, which the lock-state separation plan
  (WS-LS) had left assumed at the seam.  The proof is the per-arm containment
  family (`SyscallSchedContainment`) composed with the seam's own writes: the
  register spill and the IPC-buffer fill before the dispatch, the return-frame
  staging, the executing core's local reschedule and the residency settling
  after it, and the two hardware-ledger clears at the very end.  Every seam
  write that is not an arm's is either scheduler-inert (so the table write lock
  every footprint names covers it) or confined to the executing core (whose
  run-queue write lock every unified footprint names).

  The one arm the seam runs that no footprint covers is the capability-fault
  delivery; it is unreachable once operands resolved, because the resolution
  the operands required is the resolution the fault would have failed.
-/
import SeLe4n.Kernel.SyscallDispatchStep
import SeLe4n.Kernel.SyscallSchedFootprint
import SeLe4n.Kernel.SyscallSchedContainment
import SeLe4n.Kernel.IPC.Invariant.LookupCongruence
import SeLe4n.Kernel.InterruptEntry
import SeLe4n.Kernel.IPC.Invariant.SignalDonationFrame
import SeLe4n.Kernel.IPC.Invariant.ReplySignalFrame
import SeLe4n.Kernel.IPC.Invariant.ReplyBindingPairFrame

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId AccessMode LockKey LockSet)

-- ============================================================================
-- §1  The executing core's scheduling points
-- ============================================================================

/-- A footprint that names the table write lock and the executing core's
run-queue write lock covers every step confined to that core that writes no
replenish queue — the shape of every scheduling point the seams run after an
arm. -/
theorem footprintCoversWrites_of_confinedToCore (S : LockSet) (e : CoreId)
    {st st' : SystemState}
    (hTable : (LockKey.objStore, AccessMode.write) ∈ S.pairs)
    (hRun : (LockKey.runQueue e, AccessMode.write) ∈ S.pairs)
    (hConf : observableSlotsConfinedToCores st st' [e])
    (hRepl : ∀ d : CoreId,
      st'.scheduler.replenishQueueOnCore d = st.scheduler.replenishQueueOnCore d) :
    footprintCoversWrites S st st' :=
  ⟨fun hAbsent => absurd hTable hAbsent,
   fun d hd => by
     have hne : d ∉ [e] := by
       intro hm
       rw [List.mem_singleton] at hm
       subst hm
       exact hd hRun
     exact ⟨hConf.runQueue d hne, hConf.current d hne, hConf.activeDomain d hne⟩,
   fun d _ => hRepl d⟩

theorem switchToThreadOnCore_coversWrites (S : LockSet) (e : CoreId) (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (hTable : (LockKey.objStore, AccessMode.write) ∈ S.pairs)
    (hRun : (LockKey.runQueue e, AccessMode.write) ∈ S.pairs)
    (h : switchToThreadOnCore st e tid = .ok st') :
    footprintCoversWrites S st st' :=
  footprintCoversWrites_of_confinedToCore S e hTable hRun
    (switchToThreadOnCore_confinedToCores st st' e tid h)
    (fun d => switchToThreadOnCore_replenishQueueOnCore st e tid st' d h)

theorem dropCurrentOnCore_coversWrites (S : LockSet) (e : CoreId) (st : SystemState)
    (hTable : (LockKey.objStore, AccessMode.write) ∈ S.pairs)
    (hRun : (LockKey.runQueue e, AccessMode.write) ∈ S.pairs) :
    footprintCoversWrites S st (dropCurrentOnCore st e) :=
  footprintCoversWrites_of_confinedToCore S e hTable hRun
    (dropCurrentOnCore_confinedToCores st e)
    (fun d => dropCurrentOnCore_replenishQueueOnCore st e d)

theorem handleRescheduleSgiOnCore_coversWrites (S : LockSet) (e : CoreId) (st st' : SystemState)
    (hTable : (LockKey.objStore, AccessMode.write) ∈ S.pairs)
    (hRun : (LockKey.runQueue e, AccessMode.write) ∈ S.pairs)
    (h : handleRescheduleSgiOnCore st e = .ok st') :
    footprintCoversWrites S st st' :=
  footprintCoversWrites_of_confinedToCore S e hTable hRun
    (handleRescheduleSgiOnCore_confinedToCores st st' e h)
    (fun d => handleRescheduleSgiOnCore_replenishQueueOnCore st e st' d h)

/-- The commit's local successor on the executing core is covered, whichever
caller the seam captured. -/
theorem scheduleLocalSuccessorFrom_coversWrites (S : LockSet) (e : CoreId)
    (caller? : Option SeLe4n.ThreadId) (post : SystemState)
    (hTable : (LockKey.objStore, AccessMode.write) ∈ S.pairs)
    (hRun : (LockKey.runQueue e, AccessMode.write) ∈ S.pairs) :
    footprintCoversWrites S post
      (PriorityInheritance.scheduleLocalSuccessorFrom caller? post e) := by
  unfold PriorityInheritance.scheduleLocalSuccessorFrom
  split
  · split
    · rename_i st' h
      exact handleRescheduleSgiOnCore_coversWrites S e post st' hTable hRun h
    · exact footprintCoversWrites_refl S post
  · exact footprintCoversWrites_refl S post

theorem dispatchVacatedCore_coversWrites (S : LockSet) (e : CoreId) (st : SystemState)
    (hTable : (LockKey.objStore, AccessMode.write) ∈ S.pairs)
    (hRun : (LockKey.runQueue e, AccessMode.write) ∈ S.pairs) :
    footprintCoversWrites S st (PriorityInheritance.dispatchVacatedCore st e) := by
  unfold PriorityInheritance.dispatchVacatedCore
  split
  · exact footprintCoversWrites_refl S st
  · split
    · rename_i st' h
      exact handleRescheduleSgiOnCore_coversWrites S e st st' hTable hRun h
    · exact footprintCoversWrites_refl S st

/-- Deferring a thread still resident elsewhere switches the executing core to
its idle thread, or preempts and vacates it — both on the executing core. -/
theorem deferResidentElsewhere_coversWrites (S : LockSet) (e : CoreId) (st : SystemState)
    (hTable : (LockKey.objStore, AccessMode.write) ∈ S.pairs)
    (hRun : (LockKey.runQueue e, AccessMode.write) ∈ S.pairs) :
    footprintCoversWrites S st (PriorityInheritance.deferResidentElsewhere st e) := by
  unfold PriorityInheritance.deferResidentElsewhere
  split
  · rename_i tid _
    have hR : footprintCoversWrites S st (restoreIncomingContextOnCore st e tid) :=
      ⟨fun _ _ _ => by rw [restoreIncomingContextOnCore_objects],
       fun _ _ => by rw [restoreIncomingContextOnCore_scheduler]; exact ⟨rfl, rfl, rfl⟩,
       fun _ _ => by rw [restoreIncomingContextOnCore_scheduler]⟩
    split
    · dsimp only
      split
      · rename_i st' h
        exact footprintCoversWrites_trans S hR
          (switchToThreadOnCore_coversWrites S e _ st' _ hTable hRun h)
      · exact footprintCoversWrites_trans S hR (dropCurrentOnCore_coversWrites S e _ hTable hRun)
    · exact footprintCoversWrites_refl S st
  · exact footprintCoversWrites_refl S st

/-- A step that writes only reschedule-pending flags, on any core, is covered by
every footprint: no clause of the coverage reads the flags (the cross-core
poke raises another core's flag as the KSC-1 accumulator's remote write). -/
theorem footprintCoversWrites_of_objects_reschedule_eq (S : LockSet) {st st' : SystemState}
    {flags : PerCoreFlags}
    (hObj : st'.objects = st.objects)
    (hSched : st'.scheduler = { st.scheduler with reschedulePending := flags }) :
    footprintCoversWrites S st st' :=
  ⟨fun _ oid _ => by rw [hObj], fun d _ => by rw [hSched]; exact ⟨rfl, rfl, rfl⟩,
   fun d _ => by rw [hSched]; rfl⟩

/-- The residency settling: the dispatch and the deferral are scheduling points
on the executing core, the residency record is a machine write, and the poke of
the released thread's queue core writes only that core's reschedule flag. -/
theorem settleResidencyOnCore_coversWrites (S : LockSet) (e : CoreId) (st : SystemState)
    (hTable : (LockKey.objStore, AccessMode.write) ∈ S.pairs)
    (hRun : (LockKey.runQueue e, AccessMode.write) ∈ S.pairs) :
    footprintCoversWrites S st (PriorityInheritance.settleResidencyOnCore st e) := by
  unfold PriorityInheritance.settleResidencyOnCore
  exact footprintCoversWrites_trans S
    (footprintCoversWrites_trans S (dispatchVacatedCore_coversWrites S e st hTable hRun)
      (deferResidentElsewhere_coversWrites S e _ hTable hRun))
    (footprintCoversWrites_trans S (footprintCoversWrites_of_objects_scheduler_eq S rfl rfl)
      (footprintCoversWrites_of_objects_reschedule_eq S
        (PriorityInheritance.pokeReleasedResident_objects _ _ _ _)
        (PriorityInheritance.pokeReleasedResident_scheduler _ _ _ _)))

/-- WS-ZA ZA6.7: **the activation is covered by every footprint naming the table
write lock.**  It writes the executing core's current thread and the context its
yield link names — objects the footprint, computed before the scheduler chose
that thread, cannot name one by one, and the table write lock covers at once —
and the executing core's register bank, which no lock guards; no scheduler
state.  Every declared footprint of the kernel names the table write lock
(`schedFootprintOfCores`, `mem_unifiedLockSetForSyscall_objStore`), as seL4's
big kernel lock covers its `activateThread`. -/
theorem activateThreadOnCore_coversWrites (S : LockSet) (e : CoreId) (st : SystemState)
    (hTable : (LockKey.objStore, AccessMode.write) ∈ S.pairs) :
    footprintCoversWrites S st (activateThreadOnCore st e) :=
  footprintCoversWrites_of_scheduler_eq S hTable (activateThreadOnCore_scheduler st e)

/-- **The syscall commit's tail is covered**: from the dispatched state, staging
the caller's result (a register write under the table lock), the local successor
and the residency settling (the executing core's own scheduling points), the
activation of the thread the core resumes (under the table lock,
`activateThreadOnCore_coversWrites`), and the two hardware-ledger clears
(scheduler- and store-inert). -/
theorem syscallCommitTail_coversWrites (S : LockSet) (e : CoreId)
    (caller? : Option SeLe4n.ThreadId) (post : SystemState) (o : Architecture.SyscallOutcome)
    (hTable : (LockKey.objStore, AccessMode.write) ∈ S.pairs)
    (hRun : (LockKey.runQueue e, AccessMode.write) ∈ S.pairs) :
    footprintCoversWrites S post
      (Architecture.clearPhysicalWrites (Architecture.clearIcacheMaintenance
        (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore
          (PriorityInheritance.scheduleLocalSuccessorFrom caller?
            (Architecture.stageCallerReturnFor caller? post e o) e) e) e))) :=
  footprintCoversWrites_trans S
    (footprintCoversWrites_trans S
      (footprintCoversWrites_of_scheduler_eq S hTable
        (Architecture.stageCallerReturnFor_scheduler caller? post e o))
      (footprintCoversWrites_trans S
        (footprintCoversWrites_trans S
          (scheduleLocalSuccessorFrom_coversWrites S e caller? _ hTable hRun)
          (settleResidencyOnCore_coversWrites S e _ hTable hRun))
        (activateThreadOnCore_coversWrites S e _ hTable)))
    (footprintCoversWrites_of_objects_scheduler_eq S
      (by simp only [Architecture.clearPhysicalWrites, (Architecture.clearIcacheMaintenance_frame _).1])
      (by simp only [Architecture.clearPhysicalWrites, (Architecture.clearIcacheMaintenance_frame _).2.2.1]))

-- ============================================================================
-- §2  The checked dispatcher, arm by arm
-- ============================================================================

/-- A promoted thread id promotes back to itself — what ties `.tcbSuspend`'s
operand, carried as the promoted id's value, to the resolver's re-promotion. -/
theorem validThreadId_val_toValid? (v : SeLe4n.ValidThreadId) :
    v.val.toValid? = some v := by
  unfold SeLe4n.ThreadId.toValid?
  rw [dif_neg v.property]

/-- **The `.replyRecv` arm's composite is covered by the arm's footprint**: the
composite's own footprint (`schedLockSet_replyRecvTransferOnCore_coversWrites`)
is contained in the arm's (`schedLockSet_replyRecvTransferOnCore_subset_arm`). -/
theorem schedLockSet_replyRecvArmOnCore_coversTransfer (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId)
    (label : Nat) (msg : IpcMessage) (grant : Bool) (e : CoreId) (st st' : SystemState)
    (summary : CapTransferSummary) (S : LockSet) (hObjInv : st.objects.invExt)
    (hS : LockSet.ofList? (schedLockSet_replyRecvArmOnCore endpointId receiver replyId
      prevCaller label msg grant e st) = some S)
    (hStep : replyRecvTransferOnCore endpointId receiver replyId prevCaller label msg grant
      e st = .ok (summary, st')) :
    footprintCoversWrites S st st' := by
  obtain ⟨S0, hS0⟩ := schedFootprintOfCores_ofList?_isSome
    (replyRecvTransferWriteSet endpointId receiver replyId prevCaller label msg grant e st)
    (replyRecvHandoffReplenishCores (replyRecvCallerFaultAnswer? st prevCaller label msg)
      endpointId receiver replyId prevCaller
      (replyRecvLegMessage (replyRecvCallerFaultAnswer? st prevCaller label msg) msg) grant e st)
  refine footprintCoversWrites_mono S0 S st st' (fun l hl => ?_)
    (schedLockSet_replyRecvTransferOnCore_coversWrites endpointId receiver replyId prevCaller
      label msg grant e st st' summary S0 hObjInv hS0 hStep)
  rw [LockSet.ofList?_pairs hS]
  rw [LockSet.ofList?_pairs hS0] at hl
  exact schedLockSet_replyRecvTransferOnCore_subset_arm endpointId receiver replyId prevCaller
    label msg grant e st _ hl

/-- ...and so is the notification the receive's lock operands name. -/
theorem cancelRecvBusyReply_receiverBoundNotification? (ctx : LabelingContext)
    (tid : SeLe4n.ThreadId) (gate : SyscallGate) (decoded : SyscallDecodeResult)
    (ec : Concurrency.CoreId) (st : SystemState) (hInv : st.objects.invExt) :
    Concurrency.receiverBoundNotification? (cancelRecvBusyReply ctx tid gate decoded ec st) tid =
      Concurrency.receiverBoundNotification? st tid := by
  have e := cancelRecvBusyReply_boundNotificationCode ctx tid gate decoded ec st hInv
  unfold Concurrency.receiverBoundNotification?
  cases h1 : (cancelRecvBusyReply ctx tid gate decoded ec st).getTcb? tid <;>
    cases h0 : st.getTcb? tid <;> rw [h1, h0] at e <;> simp only [Option.map] at e
  all_goals first
    | rfl
    | cases e
    | (simp only [Option.bind_some, TCB.boundNotification]
       rw [Option.some.inj e])

/-- **A receive that completes a signal after its cancel completes the
notification its entry state names.** -/
theorem receiveCompletion_receiverBoundNotification?_eq {ctx : LabelingContext}
    {tid : SeLe4n.ThreadId} {gate : SyscallGate} {decoded : SyscallDecodeResult}
    {ec : Concurrency.CoreId} {st : SystemState} (hInv : st.objects.invExt)
    (hSig : receiveCompletesSignal ctx (cancelRecvBusyReply ctx tid gate decoded ec st) tid = true) :
    Concurrency.receiverBoundNotification? st tid =
      some (receiverBoundNotification (cancelRecvBusyReply ctx tid gate decoded ec st) tid) := by
  rw [← cancelRecvBusyReply_receiverBoundNotification? ctx tid gate decoded ec st hInv]
  unfold receiveCompletesSignal at hSig
  unfold Concurrency.receiverBoundNotification? receiverBoundNotification
  cases hT : (cancelRecvBusyReply ctx tid gate decoded ec st).getTcb? tid with
  | none => rw [hT] at hSig; cases hSig
  | some t =>
    rw [hT] at hSig
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hSig
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hSig.1.1
    simp only [Option.bind_some, TCB.boundNotification, hk, SeLe4n.ObjId.ofOptCode]
    rfl

/-- **seL4-MCS `receiveIPC`'s `completeSignal` writes a notification the
receive locks**: the one the completion reads after the busy-reply cancel is the
one the footprint names on the entry state
(`receiveCompletion_receiverBoundNotification?_eq`). -/
theorem lockSetForSyscall_receive_covers_completedNotification
    (ops : Concurrency.SyscallLockOperands) (st : SystemState) (caller : TCB)
    (endpointId : SeLe4n.ObjId) (S : LockSet) {ctx : LabelingContext} {gate : SyscallGate}
    {decoded : SyscallDecodeResult} {ec : CoreId} (hInv : st.objects.invExt)
    (hTcb : st.getTcb? ops.caller = some caller)
    (hEp : ops.targetObject = some endpointId)
    (hSig : receiveCompletesSignal ctx (cancelRecvBusyReply ctx ops.caller gate decoded ec st)
      ops.caller = true)
    (hDecl : Concurrency.lockSetForSyscall .receive ops st = some S) :
    (Concurrency.notificationLock
        (receiverBoundNotification (cancelRecvBusyReply ctx ops.caller gate decoded ec st) ops.caller),
      AccessMode.write) ∈ S.pairs :=
  Concurrency.lockSetForSyscall_receive_covers_boundNotification ops st caller endpointId S _ hTcb hEp
    (receiveCompletion_receiverBoundNotification?_eq hInv hSig) hDecl

/-- **A reply that leaves the receive's test true kept the receiver's binding**:
the receiver's TCB on the entry state names the notification it names after
the reply, since the reply keeps every binding code
(`notificationsAndBindingsKept`). -/
theorem replyRecv_boundCode_of_completes {ctx : LabelingContext}
    {st st1 : SystemState} {tid : SeLe4n.ThreadId}
    (hK : notificationsAndBindingsKept st st1)
    (hSig : receiveCompletesSignal ctx st1 tid = true) :
    ∃ t t1, st.getTcb? tid = some t ∧ st1.getTcb? tid = some t1 ∧
      t.boundNotificationCode = t1.boundNotificationCode ∧ t1.boundNotificationCode ≠ 0 := by
  unfold receiveCompletesSignal at hSig
  cases hT1 : st1.getTcb? tid with
  | none => rw [hT1] at hSig; cases hSig
  | some t1 =>
    rw [hT1] at hSig
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hSig
    have hc := hSig.1.1
    have hB := hK.2.1 tid.toObjId
    rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp hT1] at hB
    cases hO : st.objects[tid.toObjId]? with
    | none =>
      rw [hO] at hB
      simp only [notificationBindingCodes, KernelObject.bindingCodes, Prod.mk.injEq] at hB
      exact absurd hB.1 hc
    | some o =>
      rw [hO] at hB
      cases o <;> simp only [notificationBindingCodes, KernelObject.bindingCodes,
        Prod.mk.injEq] at hB
      all_goals first
        | exact absurd hB.1 hc
        | skip
      rename_i t
      exact ⟨t, t1, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO, rfl, hB.1.symm, hc⟩

/-- **The reply-receive's donation core is the receiver's home core** whenever
the receive completes a signal (`replyRecv_boundCode_of_completes`). -/
theorem replyRecvDonationCores_eq_home_of_completes {ctx : LabelingContext}
    {st st1 : SystemState} {tid : SeLe4n.ThreadId}
    (hK : notificationsAndBindingsKept st st1)
    (hSig : receiveCompletesSignal ctx st1 tid = true) :
    replyRecvDonationCores st tid = [determineTargetCore st tid] := by
  obtain ⟨t, t1, hT, -, hE, hc⟩ := replyRecv_boundCode_of_completes hK hSig
  unfold replyRecvDonationCores
  rw [hT]
  simp only [hE, hc, ↓reduceIte]

/-- **The reply-receive's donated context is in its object-domain footprint**:
the context the completion's donation writes (`signalDonationContext?`, read on
the state the completion hands it) is the context the receiver's bound
notification names on the entry state (`boundSignalDonationContext?` with its
guard read after the reply), which the footprint locks.  The reply creates,
deletes and rewrites no notification (`notificationsAndBindingsKept`), and the
consumption and the badge frame keep every notification's context word
(`completeSignalArm_donationPre_ntfnContexts`). -/
theorem replyRecvDonationContext_superset {ctx : LabelingContext}
    {tid prevCaller : SeLe4n.ThreadId} {mi : MessageInfo} {regs : Array SeLe4n.RegValue}
    {msg : IpcMessage} {grant : Bool} {c : CoreId} {st st1 st2 : SystemState}
    {badge : SeLe4n.Badge} {s : SeLe4n.SchedContextId} (hObjInv : st.objects.invExt)
    (hR : replyTransferOnCoreChecked ctx tid prevCaller mi regs msg grant c st = .ok ((), st1))
    (hSig : receiveCompletesSignal ctx st1 tid = true)
    (hW : notificationWaitCrossCoreDispatchChecked ctx (receiverBoundNotification st1 tid) tid c
      st1 = (st2, .ok (some badge)))
    (hD : signalDonationContext? (Architecture.writeReturnFrameToTcb st2 tid
      (Architecture.badgeReturnFrame st2 tid badge)) (receiverBoundNotification st1 tid) tid
        = some s) :
    Concurrency.boundSignalDonationContext? st tid true = some s := by
  have hK := notificationsAndBindingsKept.of_replyTransferOnCoreChecked hObjInv hR
  have hObj1 := replyTransferOnCoreChecked_objects_invExt hObjInv hR
  have hA := (ntfnContextsAgree.of_notificationsAndBindingsKept hK).trans
    (completeSignalArm_donationPre_ntfnContexts hObj1
      (notificationWaitCrossCoreDispatchChecked_ok_inner hW))
  have hN := notificationContext?_of_signalDonationContext? hD
  rw [notificationContext?_congr hA] at hN
  obtain ⟨t, t1, hT, hT1, hE, hc⟩ := replyRecv_boundCode_of_completes hK hSig
  unfold Concurrency.boundSignalDonationContext? Concurrency.receiverBoundNotification?
  rw [hT]
  unfold receiverBoundNotification at hN
  rw [hT1] at hN
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hc
  simp only [Option.bind_some, TCB.boundNotification, hE, hk, SeLe4n.ObjId.ofOptCode,
    ↓reduceIte, Nat.add_sub_cancel] at hN ⊢
  exact hN

/-- **A reply-receive whose receive completes its bound notification is covered by
the arm's footprint**: the reply leg is confined to its own write set and
replenish cores, which the arm's footprint names, the completion and the badge
frame leave the scheduler alone, and the completion's donation
(`maybeDonateSchedContext`) writes the receiver's home core, which no step
before it moves (`replyTransferOnCoreChecked_homeCoresKept`) and the arm names
(`replyRecvDonationCores_eq_home_of_completes`). -/
theorem replyRecvCompletesSignalArm_coversWrites (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId)
    (prevCaller : SeLe4n.ThreadId) (label : Nat) (msg : IpcMessage) (grant : Bool)
    (e : CoreId) (st st' : SystemState) (S : LockSet) (hObjInv : st.objects.invExt)
    (hFlow : securityFlowsTo (ctx.threadLabelOf receiver) (ctx.threadLabelOf prevCaller) = true)
    (hS : LockSet.ofList? (schedLockSet_replyRecvArmOnCore endpointId receiver replyId
      prevCaller label msg grant e st) = some S)
    (hStep : replyRecvCompletesSignalArm ctx receiver prevCaller label msg grant e st
      = .ok ((), st')) :
    footprintCoversWrites S st st' := by
  obtain ⟨st1, hR, hOr⟩ := replyRecvCompletesSignalArm_cases hStep
  have hK := notificationsAndBindingsKept.of_replyTransferOnCoreChecked hObjInv hR
  have hHK := replyTransferOnCoreChecked_homeCoresKept hObjInv hR
  have hObj1 := replyTransferOnCoreChecked_objects_invExt hObjInv hR
  have hTable : (LockKey.objStore, AccessMode.write) ∈ S.pairs :=
    LockSet.ofList?_pairs hS ▸ schedFootprintOfCores_contains_objStore_write _ _
  rw [replyTransferOnCoreChecked_eq_unchecked_of_flow_allowed ctx receiver prevCaller _ _ _ _ e
    st hFlow] at hR
  have hConf := replyTransferOnCore_confinedToCores receiver prevCaller _ _ msg grant e st st1
    hObjInv hR
  have hRep : footprintCoversWrites S st st1 := by
    refine footprintCoversWrites_of_cores S _ _ st st1 (LockSet.ofList?_pairs hS)
      (fun d hd => ?_) (fun d hd => ?_)
    · have hd' := fun m => hd (List.mem_append_right _ (List.mem_append_left _ m))
      exact ⟨hConf.runQueue d hd', hConf.current d hd', hConf.activeDomain d hd'⟩
    · exact replyTransferOnCore_replenishQueueOnCore_ne receiver prevCaller _ _ msg grant e st
        st1 d hObjInv (fun m => hd (List.mem_append_right _ (List.mem_append_left _ m))) hR
  rcases hOr with rfl | ⟨st2, badge, hSig1, _, hW, hS2, rfl⟩
  · exact hRep
  have hW' := notificationWaitCrossCoreDispatchChecked_ok_inner hW
  refine footprintCoversWrites_trans S hRep (footprintCoversWrites_trans S
    (footprintCoversWrites_of_scheduler_eq S hTable
      (by rw [Architecture.writeReturnFrameToTcb_scheduler_eq]; exact hS2))
    (maybeDonateSchedContext_coversWrites S _ _ receiver
      (completeSignalArm_donationPre_objects_invExt hObj1 hW') hTable fun d hd => ?_))
  -- The donation writes the receiver's home core on the state the completion
  -- hands it, which is its home core on the entry state: neither the reply
  -- nor the consumption nor the badge frame writes an affinity.
  have hHome : determineTargetCore (Architecture.writeReturnFrameToTcb st2 receiver
      (Architecture.badgeReturnFrame st2 receiver badge)) receiver
        = determineTargetCore st receiver :=
    (hHK.trans
      (homeCoresKept.of_schedLinkFrame
        (completeSignalArm_donationPre_schedLinkFrame hObj1 hW'))) receiver
  have hAll : d ∈ replyRecvDonationCores st receiver := by
    rw [replyRecvDonationCores_eq_home_of_completes hK hSig1, ← hHome]
    unfold signalDonationCores at hd
    split at hd
    · exact hd
    · cases hd
  rw [LockSet.ofList?_pairs hS]
  unfold schedLockSet_replyRecvArmOnCore
  exact ⟨(mem_schedFootprintOfCores_runQueue_iff _ _ d).mpr
      (List.mem_append_right _ (List.mem_append_right _ hAll)),
    (mem_schedFootprintOfCores_replenishQueue_iff _ _ d).mpr
      (List.mem_append_right _ (List.mem_append_right _ hAll))⟩

/-- **A receive run on its busy-reply-cancelled state is covered** by the
receive's footprint (`schedLockSet_receiveCancellingHolderOnCore`) at the
operands it declares (`receiveLockOperands`): the holder's cancel, then the
receive.  The `.receive` arm, and the `.replyRecv` arm whose reply is skipped. -/
theorem receiveResolvedArm_coversWrites (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (e : CoreId)
    (gate : SyscallGate) (epId : SeLe4n.ObjId) (st st' : SystemState)
    (ops : Concurrency.SyscallLockOperands) (S : LockSet)
    (hObjInv : st.objects.invExt) (hHeads : queueHeadBlockedConsistent st)
    (hTable : (LockKey.objStore, AccessMode.write) ∈ S.pairs)
    (hOps : receiveLockOperands gate decoded tid epId st = some ops)
    (hSched : schedLockSetForSyscall .receive ops e st = some S)
    (hDisp : receiveResolvedArm ctx decoded gate tid epId e
      (cancelRecvBusyReply ctx tid gate decoded e st) = .ok ((), st')) :
    footprintCoversWrites S st st' := by
  unfold receiveLockOperands at hOps
  unfold receiveResolvedArm at hDisp
  generalize hC : cancelRecvBusyReply ctx tid gate decoded e st = stC at hDisp
  have hCancel : footprintCoversWrites S st stC := by
      unfold cancelRecvBusyReply at hC
      cases hCode : recvBusyReplyHolderCode ctx tid gate decoded st with
      | zero =>
        rw [hCode] at hC
        simp only at hC
        subst hC
        exact footprintCoversWrites_refl S st
      | succ k =>
        rw [hCode] at hC
        simp only at hC
        subst hC
        have hB := recvBusyReplyHolderCode_succ hCode
        split at hOps
        · obtain ⟨rid, hRid⟩ : ∃ rid, recvReplyLookup? gate decoded st = some rid := by
            cases hL : recvReplyLookup? gate decoded st with
            | none => rw [hL] at hB; exact absurd hB (by simp [busyReplyHolder?])
            | some rid => exact ⟨rid, rfl⟩
          simp only [hB, Option.isSome_some, ↓reduceIte, Option.some.injEq] at hOps
          subst hOps
          rw [hRid] at hB
          simp only [schedLockSetForSyscall, Option.bind_some,
            schedLockSet_receiveCancellingHolderOnCore, hRid, hB] at hSched
          exact footprintCoversWrites_of_cores S _ _ st _ (LockSet.ofList?_pairs hSched)
            (fun d hd => absurd (List.mem_append_left _ (Concurrency.mem_allCores d)) hd)
            (fun d _ => cancelReplyHolder_replenishQueueOnCore st ⟨k⟩ e d)
        · rename_i hR0
          exact absurd (recvBusyReplyHolderCode_eq_zero_of_resolveRecvReplyId_ok hR0)
            (by rw [hCode]; simp)
  by_cases hSig : receiveCompletesSignal ctx stC tid = true
  · -- seL4-MCS `receiveIPC`: the bound notification is active, so the receive
    -- completes it: the wait's consumption, which moves no scheduler state,
    -- then the badge register written.
    cases hRes : resolveRecvReplyId gate decoded stC with
    | error _ => rw [hRes] at hDisp; exact absurd hDisp (by simp)
    | ok r =>
    rw [hRes] at hDisp
    simp only [hSig, ↓reduceIte] at hDisp
    obtain ⟨st1, badge, hW, hSch, hPost⟩ := completeSignalArm_consumes hSig hDisp
    subst hPost
    have hW' := notificationWaitCrossCoreDispatchChecked_ok_inner hW
    -- seL4-MCS `completeSignal`'s `maybeDonateSchedContext`, on the cores the
    -- footprint read off the completion's pre-state: the cancelled state when
    -- the reply names a holder, the entry's own otherwise.
    unfold cancelRecvBusyReply at hC
    cases hCode : recvBusyReplyHolderCode ctx tid gate decoded st with
    | zero =>
      rw [hCode] at hC
      simp only at hC
      subst hC
      rw [hRes] at hOps
      injection hOps with hOps
      subst hOps
      simp only [schedLockSetForSyscall, Option.bind_some] at hSched
      refine footprintCoversWrites_trans S (st₂ := st) hCancel
        (footprintCoversWrites_trans S
          (footprintCoversWrites_of_scheduler_eq S hTable
            (by rw [Architecture.writeReturnFrameToTcb_scheduler_eq, hSch]))
          (maybeDonateSchedContext_coversWrites S _ _ tid
            (completeSignalArm_donationPre_objects_invExt hObjInv hW') hTable fun d hd => ?_))
      rw [completeSignalArm_signalDonationCores_eq _ hObjInv hW'] at hd
      have hD : d ∈ receiveDonationCores st tid r e := by
        simpa only [receiveDonationCores, busyReplyHolder?_of_resolveRecvReplyId_ok tid hRes]
          using hd
      rw [LockSet.ofList?_pairs hSched]
      unfold schedLockSet_receiveCancellingHolderOnCore
      exact ⟨(mem_schedFootprintOfCores_runQueue_iff _ _ d).mpr (List.mem_append_right _ hD),
        (mem_schedFootprintOfCores_replenishQueue_iff _ _ d).mpr (List.mem_append_right _ hD)⟩
    | succ k =>
      rw [hCode] at hC
      simp only at hC
      subst hC
      have hB := recvBusyReplyHolderCode_succ hCode
      have hObjC := cancelReplyHolder_objects_invExt st ⟨k⟩ e hObjInv
      split at hOps
      · simp only [hB, Option.isSome_some, ↓reduceIte, Option.some.injEq] at hOps
        subst hOps
        simp only [schedLockSetForSyscall, Option.bind_some] at hSched
        refine footprintCoversWrites_trans S hCancel
          (footprintCoversWrites_trans S
            (footprintCoversWrites_of_scheduler_eq S hTable
              (by rw [Architecture.writeReturnFrameToTcb_scheduler_eq, hSch]))
            (maybeDonateSchedContext_coversWrites S _ _ tid
              (completeSignalArm_donationPre_objects_invExt hObjC hW') hTable fun d hd => ?_))
        rw [completeSignalArm_signalDonationCores_eq _ hObjC hW'] at hd
        have hD : d ∈ receiveDonationCores st tid (recvReplyLookup? gate decoded st) e := by
          simpa only [receiveDonationCores, hB] using hd
        rw [LockSet.ofList?_pairs hSched]
        unfold schedLockSet_receiveCancellingHolderOnCore
        exact ⟨(mem_schedFootprintOfCores_runQueue_iff _ _ d).mpr (List.mem_append_right _ hD),
          (mem_schedFootprintOfCores_replenishQueue_iff _ _ d).mpr (List.mem_append_right _ hD)⟩
      · rename_i hR0
        exact absurd (recvBusyReplyHolderCode_eq_zero_of_resolveRecvReplyId_ok hR0)
          (by rw [hCode]; simp)
  simp only [Bool.not_eq_true] at hSig
  by_cases hNb : receiveFindsNothing (Syscall.wordReceiveBlocks (callerSyscallWord stC tid)) stC epId = true
  · -- WS-SX SX7.2: `NBRecv` with no sender waiting: the holder's cancel, then
    -- the badge register written, which moves no scheduler state.
    cases hRes : resolveRecvReplyId gate decoded stC with
    | error _ => rw [hRes] at hDisp; exact absurd hDisp (by simp)
    | ok r =>
    rw [hRes] at hDisp
    simp only [hSig, Bool.false_eq_true, hNb, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq, true_and] at hDisp
    subst hDisp
    exact footprintCoversWrites_trans S (st₂ := stC) hCancel
      (footprintCoversWrites_of_scheduler_eq S hTable
        (Architecture.writeReturnFrameToTcb_scheduler_eq _ _ _))
  simp only [Bool.not_eq_true] at hNb
  split at hDisp
  · exact absurd hDisp (by simp)
  rename_i replyId? hR
  simp only [hSig, hNb, Bool.false_eq_true, ↓reduceIte] at hDisp
  split at hDisp
  · rename_i st₁ dequeued summary sgi hLeg
    split at hDisp
    · exact absurd hDisp (by simp)
    rename_i stDon hHand
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hDisp
    subst hDisp
    refine footprintCoversWrites_trans S (st₂ := stDon) ?_
      (footprintCoversWrites_of_scheduler_eq S hTable
        (by rw [Architecture.stageDeliveredMessage_scheduler_eq]))
    unfold cancelRecvBusyReply at hC
    cases hCode : recvBusyReplyHolderCode ctx tid gate decoded st with
    | zero =>
      -- nothing to cancel: the receive's own footprint, read at `st`
      rw [hCode] at hC
      simp only at hC
      subst hC
      rw [hR] at hOps
      injection hOps with hOps
      subst hOps
      simp only [schedLockSetForSyscall, Option.bind_some,
        schedLockSet_receiveCancellingHolderOnCore,
        busyReplyHolder?_of_resolveRecvReplyId_ok tid hR] at hSched
      exact footprintCoversWrites_of_cores_append S _ _ _ _ st stDon (LockSet.ofList?_pairs hSched)
        fun S0 hS0 => schedLockSet_endpointReceiveOnCore_coversWrites epId tid replyId? e st st₁
          stDon dequeued summary sgi S0 hObjInv hHeads hS0 hLeg hHand
    | succ k =>
      -- the holder `⟨k⟩` is cancelled first; the operands name its reply
      rw [hCode] at hC
      simp only at hC
      subst hC
      have hB := recvBusyReplyHolderCode_succ hCode
      split at hOps
      · obtain ⟨rid, hRid⟩ : ∃ rid, recvReplyLookup? gate decoded st = some rid := by
          cases hL : recvReplyLookup? gate decoded st with
          | none => rw [hL] at hB; exact absurd hB (by simp [busyReplyHolder?])
          | some rid => exact ⟨rid, rfl⟩
        simp only [hB, Option.isSome_some, ↓reduceIte, Option.some.injEq] at hOps
        subst hOps
        have hReply := resolveRecvReplyId_eq_of_getCNode?
          (cancelReplyHolder_getCNode? st ⟨k⟩ e hObjInv) hRid hR
        subst hReply
        rw [hRid] at hB
        simp only [schedLockSetForSyscall, Option.bind_some,
          schedLockSet_receiveCancellingHolderOnCore, hRid, hB] at hSched
        exact footprintCoversWrites_of_cores_append S _ _ _ _ st stDon
          (LockSet.ofList?_pairs hSched) fun S0 hS0 =>
            schedLockSet_receiveCancellingHolder_coversWrites epId tid (some rid) e ⟨k⟩ st
              st₁ stDon dequeued summary sgi S0 hObjInv (LockSet.ofList?_pairs hS0) hLeg hHand
      · rename_i hR0
        exact absurd (recvBusyReplyHolderCode_eq_zero_of_resolveRecvReplyId_ok hR0)
          (by rw [hCode]; simp)
  · exact absurd hDisp (by simp)

/-- **The sixteen declared arms are covered by the footprint the resolver
declares for them**, at the operands the ABI entry resolves.

One `cases` over the syscall id: the twenty-five undeclared arms are closed by
the resolver answering `none`, and each declared arm is its own containment
theorem (`SyscallSchedContainment`) composed with the arm's own
scheduler-inert prefix and suffix — the extra-capability resolution before a
send or call, the woken-receiver stash clear and the frame stagings after.
The hypotheses are exactly what `dispatchSyscallChecked` establishes before it
calls the dispatcher: the gate the operands were resolved through is the gate
it builds, and the capability is the one that gate's lookup returned. -/
theorem dispatchWithCapChecked_coversWrites (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (e : CoreId) (tcb : TCB)
    (gate : SyscallGate) (cap : Capability) (st st' : SystemState)
    (ops : Concurrency.SyscallLockOperands) (S : LockSet)
    (hObjInv : st.objects.invExt) (hHeads : queueHeadBlockedConsistent st)
    (hGate : abiEntryGate decoded tid st = some (tcb, gate))
    (hLk : syscallLookupCap gate st = .ok (cap, st))
    (hOps : abiEntryLockOperands decoded tid st = some ops)
    (hSched : schedLockSetForSyscall (abiEntryFootprintId decoded tid st) ops e st = some S)
    (hDisp : dispatchWithCapChecked ctx decoded tid e gate cap st = .ok ((), st')) :
    footprintCoversWrites S st st' := by
  -- WS-ZA ZA4.3: a yield never reaches this tier (`dispatchYield` runs first).
  have hY : decoded.syscallId ≠ .yield := by
    intro hY
    unfold dispatchWithCapChecked dispatchCapabilityOnly at hDisp
    rw [hY] at hDisp
    simp only at hDisp
    cases hDisp
  have hTable : (LockKey.objStore, AccessMode.write) ∈ S.pairs :=
    schedLockSetForSyscall_contains_objStore_write _ ops e st S hSched
  obtain ⟨hTcb, -, -, hGateEq⟩ := abiEntryGate_components decoded tid st tcb gate hGate
  unfold abiEntryLockOperands at hOps
  rw [if_neg hY] at hOps
  split at hOps
  · exact absurd hOps (by simp)
  rw [hGate] at hOps
  simp only at hOps
  rw [hLk] at hOps
  simp only at hOps
  -- the operands were declared, so the receive's gate did not refuse
  have hRecv : receiveGateRefuses decoded.syscallId tid st cap = false := by
    cases hG : receiveGateRefuses decoded.syscallId tid st cap
    · rfl
    · rw [hG] at hOps; simp at hOps
  simp only [hRecv, Bool.false_eq_true, ↓reduceIte] at hOps
  unfold dispatchWithCapChecked dispatchCapabilityOnly dispatchCapabilityOnlyChecked at hDisp
  unfold abiEntryFootprintId at hSched
  cases hId : decoded.syscallId <;> rw [hId] at hOps hSched hDisp <;> simp only at hDisp
  all_goals try simp only [reduceCtorEq, false_and, ↓reduceIte] at hSched
  all_goals try (simp only [schedLockSetForSyscall, reduceCtorEq] at hSched; done)
  case yield => exact absurd hId hY
  -- ---- `.cspaceDelete` / `.cspaceRevoke` (WS-ZA ZA5.4 part 23) ------------
  -- WS-ZA ZA6.37: the delete's operands name the CNode and the slot the
  -- dispatch empties, so its footprint is the cores that slot's delete reads.
  case cspaceDelete =>
    cases hT : cap.target <;> rw [hT] at hDisp <;> simp only [reduceCtorEq] at hDisp
    rename_i cnodeId
    rw [hT] at hOps
    split at hDisp
    · cases hDisp
    · next args hA =>
      simp only [hA] at hOps
      injection hOps with hOps
      subst hOps
      simp only [schedLockSetForSyscall, Option.bind_some] at hSched
      split at hDisp
      · cases hDisp
      · exact schedLockSet_cspaceDeleteSlotZombie_coversWrites e _ st st' S hObjInv hSched hDisp
  case cspaceRevoke =>
    simp only [schedLockSetForSyscall] at hSched
    cases hT : cap.target <;> rw [hT] at hDisp <;> simp only [reduceCtorEq] at hDisp
    split at hDisp
    · cases hDisp
    · split at hDisp
      · cases hDisp
      · exact schedLockSet_cspaceRevokeCdtFinalising_coversWrites e _ st st' S hSched hDisp
  -- ---- `.tcbSetSpace` (WS-ZA ZA5.4 part 26: through the zombie delete) ----
  case tcbSetSpace =>
    simp only [schedLockSetForSyscall] at hSched
    exact schedLockSet_capabilityDestroyOnCore_coversWrites st st' S hSched
  -- ---- the interrupt handler's set and clear (WS-ZA ZA6.32: the node slot's
  -- finalising delete) ----------------------------------------------------
  case irqHandlerSetNotification | irqHandlerClear =>
    simp only [schedLockSetForSyscall] at hSched
    exact schedLockSet_capabilityDestroyOnCore_coversWrites st st' S hSched
  -- ---- `.tcbSuspend` ------------------------------------------------------
  case tcbSuspend =>
    cases hT : cap.target <;> rw [hT] at hOps <;> simp only [reduceCtorEq] at hOps
    rename_i objId
    split at hOps
    · exact absurd hOps (by simp)
    · rename_i valid hV
      injection hOps with hOps
      subst hOps
      simp only [schedLockSetForSyscall, Concurrency.SyscallLockOperands.ofThreadTarget,
        Option.bind_some, validThreadId_val_toValid?] at hSched
      rw [hT] at hDisp
      simp only at hDisp
      split at hDisp
      · exact absurd hDisp (by simp)
      · split at hDisp
        · exact absurd hDisp (by simp)
        · rename_i vtid hVt
          have hEq : vtid = valid := by
            have h := validateThreadIdArg_ok_toValid? _ _ hVt
            rw [hV] at h
            exact (Option.some.inj h).symm
          subst hEq
          split at hDisp
          · rename_i st₁ sgi hStep
            simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hDisp
            subst hDisp
            exact schedLockSet_suspendThreadOnCore_coversWrites st st₁ vtid e sgi S hStep hSched
          · exact absurd hDisp (by simp)
  -- ---- `.tcbResume` -------------------------------------------------------
  case tcbResume =>
    cases hT : cap.target <;> rw [hT] at hOps <;> simp only [Option.some.injEq, reduceCtorEq] at hOps
    rename_i objId
    subst hOps
    simp only [schedLockSetForSyscall, Concurrency.SyscallLockOperands.ofThreadTarget,
      Option.bind_some] at hSched
    rw [hT] at hDisp
    simp only at hDisp
    split at hDisp
    · exact absurd hDisp (by simp)
    · split at hDisp
      · exact absurd hDisp (by simp)
      · rename_i vtid hVt
        rw [validateThreadIdArg_ok_toValid? _ _ hVt, Option.bind_some] at hSched
        split at hDisp
        · rename_i st₁ sgi hStep
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hDisp
          subst hDisp
          exact schedLockSet_restartThreadOnCore_coversWrites st st₁ vtid e sgi S hObjInv hStep
            hSched
        · exact absurd hDisp (by simp)
  -- ---- `.tcbSetPriority` / `.tcbSetMCPriority` ----------------------------
  case tcbSetPriority =>
    cases hT : cap.target <;> rw [hT] at hOps <;> simp only [Option.some.injEq, reduceCtorEq] at hOps
    rename_i objId
    subst hOps
    simp only [schedLockSetForSyscall, Concurrency.SyscallLockOperands.ofThreadTarget,
      Option.bind_some] at hSched
    rw [hT] at hDisp
    simp only at hDisp
    split at hDisp
    · exact absurd hDisp (by simp)
    · split at hDisp
      · exact absurd hDisp (by simp)
      · rename_i vCaller hVc
        split at hDisp
        · exact absurd hDisp (by simp)
        · rename_i vTarget hVt
          rw [← SeLe4n.ThreadId.toValid?_some_val_eq _ _ (validateThreadIdArg_ok_toValid? _ _ hVt)]
            at hSched
          split at hDisp
          · rename_i st₁ sgi hStep
            simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hDisp
            subst hDisp
            exact schedLockSet_setPriorityOnCore_coversWrites st st₁ vCaller vTarget _ e sgi S
              hObjInv hStep hSched
          · exact absurd hDisp (by simp)
  case tcbSetMCPriority =>
    cases hT : cap.target <;> rw [hT] at hOps <;> simp only [Option.some.injEq, reduceCtorEq] at hOps
    rename_i objId
    subst hOps
    simp only [schedLockSetForSyscall, Concurrency.SyscallLockOperands.ofThreadTarget,
      Option.bind_some] at hSched
    rw [hT] at hDisp
    simp only at hDisp
    split at hDisp
    · exact absurd hDisp (by simp)
    · split at hDisp
      · exact absurd hDisp (by simp)
      · rename_i vCaller hVc
        split at hDisp
        · exact absurd hDisp (by simp)
        · rename_i vTarget hVt
          rw [← SeLe4n.ThreadId.toValid?_some_val_eq _ _ (validateThreadIdArg_ok_toValid? _ _ hVt)]
            at hSched
          split at hDisp
          · rename_i st₁ sgi hStep
            simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hDisp
            subst hDisp
            exact schedLockSet_setMCPriorityOnCore_coversWrites st st₁ vCaller vTarget _ e sgi S
              hObjInv hStep hSched
          · exact absurd hDisp (by simp)
  -- ---- `.tcbSetAffinity` --------------------------------------------------
  case tcbSetAffinity =>
    cases hT : cap.target <;> rw [hT] at hOps <;> simp only [reduceCtorEq] at hOps
    rename_i objId
    split at hOps
    · exact absurd hOps (by simp)
    · rename_i args hArgs
      split at hOps
      · exact absurd hOps (by simp)
      · rename_i affinity hAff
        injection hOps with hOps
        subst hOps
        simp only [schedLockSetForSyscall, Option.bind_some] at hSched
        rw [hT] at hDisp
        simp only at hDisp
        rw [hArgs] at hDisp
        simp only at hDisp
        split at hDisp
        · exact absurd hDisp (by simp)
        · rename_i vtid hVt
          rw [hAff] at hDisp
          simp only at hDisp
          rw [← SeLe4n.ThreadId.toValid?_some_val_eq _ _ (validateThreadIdArg_ok_toValid? _ _ hVt)]
            at hSched
          split at hDisp
          · rename_i st₁ sgi hStep
            simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hDisp
            subst hDisp
            unfold setThreadCpuAffinityOnCore at hStep
            exact schedLockSet_setThreadCpuAffinityOnCore_coversWrites st st₁ vtid.val affinity e
              sgi S hObjInv hStep hSched
          · exact absurd hDisp (by simp)
  -- ---- `.schedContextConfigure` -------------------------------------------
  -- WS-ZA ZA6.4: the operand is the context the scheduling control's resolver
  -- answers, read by the arm and the footprint from one definition.
  case schedContextConfigure =>
    cases hT : cap.target <;> rw [hT] at hOps <;> simp only [reduceCtorEq] at hOps
    rename_i core
    split at hOps
    · exact absurd hOps (by simp)
    · rename_i scCPtr hXc
      split at hOps
      · exact absurd hOps (by simp)
      · rename_i v hRes
        split at hOps
        · exact absurd hOps (by simp)
        · rename_i args hArgs
          split at hOps
          · rename_i hCore
            injection hOps with hOps
            subst hOps
            simp only [schedLockSetForSyscall, Concurrency.SyscallLockOperands.ofObjectTarget,
              Option.bind_some] at hSched
            rw [hT] at hDisp
            simp only at hDisp
            rw [hXc] at hDisp
            simp only at hDisp
            rw [hRes] at hDisp
            simp only at hDisp
            rw [hArgs] at hDisp
            simp only [hCore, dite_true] at hDisp
            exact schedLockSet_schedControlConfigure_coversWrites st st' _ v _ _ _ _ _ S
              hObjInv hDisp hSched
          · exact absurd hOps (by simp)
  -- ---- `.schedContextBind` ------------------------------------------------
  case schedContextBind =>
    cases hT : cap.target <;> rw [hT] at hOps <;> simp only [reduceCtorEq] at hOps
    rename_i scId
    split at hOps
    · exact absurd hOps (by simp)
    · rename_i v hRes
      injection hOps with hOps
      subst hOps
      simp only [schedLockSetForSyscall, Concurrency.SyscallLockOperands.ofThreadTarget,
        Option.bind_some] at hSched
      rw [hT] at hDisp
      simp only at hDisp
      rw [resolveSchedContextBindNotificationCode_eq_zero_of_thread hRes] at hDisp
      simp only at hDisp
      rw [hRes] at hDisp
      simp only at hDisp
      split at hDisp
      · exact absurd hDisp (by simp)
      · rename_i vScId hV
        exact schedLockSet_schedContextBindOnCore_coversWrites st st' vScId v S hObjInv hDisp hSched
  -- ---- `.schedContextUnbind` ----------------------------------------------
  case schedContextUnbind =>
    cases hT : cap.target <;> rw [hT] at hOps <;> simp only [Option.some.injEq, reduceCtorEq] at hOps
    rename_i scId
    subst hOps
    simp only [schedLockSetForSyscall, Concurrency.SyscallLockOperands.ofObjectTarget,
      Option.bind_some] at hSched
    rw [hT] at hDisp
    simp only at hDisp
    split at hDisp
    · exact absurd hDisp (by simp)
    · split at hDisp
      · exact absurd hDisp (by simp)
      · rename_i vScId hV
        rw [← validateObjIdArg_ok_val _ _ hV] at hSched
        split at hDisp
        · rename_i st₁ sgi hStep
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hDisp
          subst hDisp
          exact schedLockSet_schedContextUnbindAllOnCore_coversWrites st st₁ vScId e sgi S hObjInv
            hStep hSched
        · exact absurd hDisp (by simp)
  -- ---- `.schedContextYieldTo` (WS-ZA ZA6.29) -------------------------------
  case schedContextYieldTo =>
    cases hT : cap.target <;> rw [hT] at hOps <;> simp only [Option.some.injEq, reduceCtorEq] at hOps
    rename_i scId
    subst hOps
    simp only [schedLockSetForSyscall, Concurrency.SyscallLockOperands.ofObjectTarget,
      Option.bind_some] at hSched
    rw [hT] at hDisp
    simp only at hDisp
    split at hDisp
    · exact absurd hDisp (by simp)
    · rename_i vScId hV
      rw [← validateObjIdArg_ok_val _ _ hV] at hSched
      split at hDisp
      · rename_i st₁ hStep
        simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hDisp
        subst hDisp
        exact schedLockSet_schedContextYieldToOnCore_coversWrites st st₁ vScId.val e S hObjInv
          hStep hSched
      · exact absurd hDisp (by simp)
  -- ---- `.notificationSignal` ----------------------------------------------
  case notificationSignal =>
    cases hT : cap.target <;> rw [hT] at hOps <;> simp only [Option.some.injEq, reduceCtorEq] at hOps
    rename_i nId
    subst hOps
    simp only [schedLockSetForSyscall, Concurrency.SyscallLockOperands.ofObjectTarget,
      Option.bind_some] at hSched
    rw [hT] at hDisp
    simp only at hDisp
    split at hDisp
    · rename_i st₁ r hSig
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hDisp
      subst hDisp
      have h₁ := notificationSignalBoundCrossCoreDispatchChecked_fst_of_ok ctx nId tid
        cap.signalBadge e st st₁ r hSig
      rw [← h₁]
      exact schedLockSet_sendSignalOnCore_coversWrites nId cap.signalBadge e st S
        hObjInv hSched
    · exact absurd hDisp (by simp)
  -- ---- `.notificationWait` ------------------------------------------------
  case notificationWait =>
    cases hT : cap.target <;> rw [hT] at hOps <;> simp only [Option.some.injEq, reduceCtorEq] at hOps
    rename_i nId
    subst hOps
    simp only [schedLockSetForSyscall] at hSched
    rw [hT] at hDisp
    simp only at hDisp
    by_cases hNb : waitFindsNothing ctx (Syscall.wordReceiveBlocks (callerSyscallWord st tid)) st tid nId = true
    · -- WS-SX SX7.2: `NBWait` with nothing pending writes the badge register.
      simp only [hNb, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq, true_and] at hDisp
      subst hDisp
      exact footprintCoversWrites_of_scheduler_eq S hTable
        (Architecture.writeReturnFrameToTcb_scheduler_eq _ _ _)
    simp only [Bool.not_eq_true] at hNb
    simp only [hNb, Bool.false_eq_true, ↓reduceIte] at hDisp
    unfold completeSignalArm at hDisp
    split at hDisp
    · rename_i st₁ badge hWait
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hDisp
      subst hDisp
      have h₁ := notificationWaitCrossCoreDispatchChecked_fst_of_ok ctx nId tid e st st₁ _ hWait
      have hW' := notificationWaitCrossCoreDispatchChecked_ok_inner hWait
      have hWaitCov : footprintCoversWrites S st st₁ := by
        rw [← h₁]
        exact schedLockSet_notificationWaitOnCore_coversWrites nId tid e st S _ hSched
      -- seL4-MCS `completeSignal`'s `maybeDonateSchedContext`: on the cores the
      -- footprint read off the wait's pre-state, which the consumption and the
      -- badge register keep.
      refine footprintCoversWrites_trans S hWaitCov (footprintCoversWrites_trans S
        (footprintCoversWrites_of_scheduler_eq S hTable
          (Architecture.writeReturnFrameToTcb_scheduler_eq _ _ _))
        (maybeDonateSchedContext_coversWrites S _ nId tid
          (completeSignalArm_donationPre_objects_invExt hObjInv hW') hTable fun d hd => ?_))
      rw [completeSignalArm_signalDonationCores_eq nId hObjInv hW'] at hd
      rw [LockSet.ofList?_pairs hSched]
      exact schedLockSet_notificationWaitOnCore_contains_donation_writes st (some nId) tid e d
        (by simpa only [waitDonationCores, Option.map_some, Option.getD_some] using hd)
    · rename_i st₁ hWait
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hDisp
      subst hDisp
      have h₁ := notificationWaitCrossCoreDispatchChecked_fst_of_ok ctx nId tid e st st₁ _ hWait
      rw [← h₁]
      exact schedLockSet_notificationWaitOnCore_coversWrites nId tid e st S _ hSched
    · exact absurd hDisp (by simp)
  -- ---- `.send` ------------------------------------------------------------
  case send =>
    cases hT : cap.target <;> rw [hT] at hOps <;> simp only [Option.some.injEq, reduceCtorEq] at hOps
    rename_i epId
    subst hOps
    simp only [schedLockSetForSyscall, Concurrency.SyscallLockOperands.ofObjectTarget,
      Option.bind_some] at hSched
    rw [hT] at hDisp
    simp only at hDisp
    by_cases hNb : sendDropsMessage ctx (Syscall.wordSendBlocks (callerSyscallWord st tid)) st tid epId = true
    · -- WS-SX SX7.2: `NBSend` with no receiver waiting writes nothing.
      simp only [hNb, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq, true_and] at hDisp
      subst hDisp
      exact footprintCoversWrites_refl S st
    simp only [Bool.not_eq_true] at hNb
    simp only [hNb, Bool.false_eq_true, ↓reduceIte] at hDisp
    split at hDisp
    · exact absurd hDisp (by simp)
    · rename_i st₂ summary x hSend
      split at hDisp
      · exact absurd hDisp (by simp)
      · rename_i st₃ hClr
        simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hDisp
        subst hDisp
        refine footprintCoversWrites_trans S (st₂ := st₂) ?_
          (footprintCoversWrites_trans S (st₂ := st₃)
            (footprintCoversWrites_of_scheduler_eq S hTable
              (clearWokenReceiverStash_scheduler_eq _ _ _ hClr))
            (footprintCoversWrites_of_scheduler_eq S hTable
              (Architecture.stageWokenDelivery_scheduler_eq _ _ _)))
        rw [← show _ = st₂ from congrArg Prod.fst hSend]
        exact schedLockSet_endpointSendOnCore_coversWrites ctx epId tid _ e _ S hObjInv hSched
  -- ---- `.call` ------------------------------------------------------------
  case call =>
    cases hT : cap.target <;> rw [hT] at hOps <;> simp only [Option.some.injEq, reduceCtorEq] at hOps
    rename_i epId
    subst hOps
    simp only [schedLockSetForSyscall, Option.bind_some] at hSched
    rw [hT] at hDisp
    subst hGateEq
    simp only at hDisp
    split at hDisp
    · rename_i st₂ summary x hCallC
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hDisp
      subst hDisp
      unfold endpointCallCrossCoreDispatchChecked at hCallC
      split at hCallC
      · refine footprintCoversWrites_trans S (st₂ := st₂) ?_
          (footprintCoversWrites_of_scheduler_eq S hTable
            (Architecture.stageWokenDelivery_scheduler_eq _ _ _))
        rw [← show _ = st₂ from congrArg Prod.fst hCallC]
        exact schedLockSet_endpointCallOnCore_coversWrites epId tid _ e _ S hObjInv hSched
      · exact absurd (congrArg Prod.snd hCallC) (by simp)
    · exact absurd hDisp (by simp)
  -- ---- `.receive` ---------------------------------------------------------
  case receive =>
    cases hT : cap.target <;> rw [hT] at hOps <;> simp only [reduceCtorEq] at hOps
    rename_i epId
    rw [hT] at hDisp
    simp only at hDisp
    split at hDisp
    · exact absurd hDisp (by simp)
    exact receiveResolvedArm_coversWrites ctx decoded tid e gate epId st st' ops S hObjInv hHeads
      hTable hOps hSched hDisp
  -- ---- `.reply` -----------------------------------------------------------
  case reply =>
    cases hT : cap.target <;> rw [hT] at hOps <;> simp only [Option.some.injEq, reduceCtorEq] at hOps
    rename_i rid
    subst hOps
    simp only [schedLockSetForSyscall, Option.bind_some] at hSched
    rw [hT] at hDisp
    simp only at hDisp
    split at hDisp
    · exact absurd hDisp (by simp)
    · rename_i callerTid hAns
      rw [hAns] at hSched
      simp only [Option.bind_some] at hSched
      split at hDisp
      · rename_i hFlow
        rw [replyTransferOnCoreChecked_eq_unchecked_of_flow_allowed ctx tid callerTid _ _ _ _ e st
          hFlow] at hDisp
        exact schedLockSet_replyTransferOnCore_coversWrites tid callerTid decoded.msgInfo
          decoded.msgRegs _ _ e st st' S hObjInv hSched hDisp
      · exact absurd hDisp (by simp)
  -- ---- `.replyRecv` -------------------------------------------------------
  case replyRecv =>
    cases hT : cap.target <;> rw [hT] at hOps <;> simp only [reduceCtorEq] at hOps
    rename_i epId
    rw [hT] at hDisp
    simp only at hDisp
    split at hDisp
    · exact absurd hDisp (by simp)
    -- WS-SX SX6.1, SX7.3: an extra capability that does not look up, or a
    -- reply that answers no caller, skips the reply, and the receive runs alone
    -- under the receive's footprint
    have hGc : resolveReplyRecvReply gate decoded st =
        resolveReplyRecvReply (callerReplyGate st tid decoded) decoded st := by
      have hO := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTcb
      rw [hGateEq]
      exact resolveReplyRecvReply_congr _ _ decoded rfl
        (by simp only [callerReplyGate, callerCspaceRoot, SystemState.getObject?_eq_getElem, hO])
    cases hXc : callerExtraCapsFault? st tid decoded.msgInfo.extraCaps with
    | some xf =>
      have hSk : replyRecvSkipsReply decoded tid st = true := by
        simp [replyRecvSkipsReply, hXc]
      rw [hXc] at hDisp hOps
      simp only [Option.isSome_some, ↓reduceIte] at hOps
      simp only [hSk, and_self, ↓reduceIte] at hSched
      exact receiveResolvedArm_coversWrites ctx decoded tid e gate epId st st' ops S hObjInv
        hHeads hTable hOps hSched hDisp
    | none =>
      rw [hXc] at hDisp hOps
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hOps
      simp only at hDisp
      cases hRRR : resolveReplyRecvReply gate decoded st with
      | error err => rw [hRRR] at hOps; exact absurd hOps (by simp)
      | ok r =>
      cases r with
      | none =>
        have hSk : replyRecvSkipsReply decoded tid st = true := by
          simp [replyRecvSkipsReply, hXc, ← hGc, hRRR]
        rw [hRRR] at hOps hDisp
        simp only [hSk, and_self, ↓reduceIte] at hSched
        exact receiveResolvedArm_coversWrites ctx decoded tid e gate epId st st' ops S hObjInv
          hHeads hTable hOps hSched hDisp
      | some r =>
        obtain ⟨rid, prev, replyBadge, replyGrant⟩ := r
        have hSk : replyRecvSkipsReply decoded tid st = false := by
          simp [replyRecvSkipsReply, hXc, ← hGc, hRRR]
        rw [hRRR] at hOps
        simp only [hSk, Bool.false_eq_true, and_false, ↓reduceIte] at hSched
        injection hOps with hOps
        subst hOps
        simp only [schedLockSetForSyscall, Option.bind_some] at hSched
        rw [resolveReplyRecvReply_answered gate decoded st rid prev replyBadge replyGrant hRRR]
          at hSched
        simp only [Option.bind_some] at hSched
        rw [hRRR] at hDisp
        simp only at hDisp
        split at hDisp
        · rename_i hFlow
          split at hDisp
          · exact replyRecvCompletesSignalArm_coversWrites ctx epId tid rid prev _ _ _ e st st' S
              hObjInv hFlow hSched hDisp
          split at hDisp
          · rename_i summary st₁ hStep
            simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hDisp
            subst hDisp
            subst hGateEq
            refine footprintCoversWrites_trans S ?_ (footprintCoversWrites_of_scheduler_eq S hTable
              (Architecture.stageDeliveredMessage_scheduler_eq _ _ _))
            exact schedLockSet_replyRecvArmOnCore_coversTransfer epId tid rid prev _ _ _
              e st st₁ summary S hObjInv hSched hStep
          · exact absurd hDisp (by simp)
        · exact absurd hDisp (by simp)

/-- **The checked dispatcher is covered**: `dispatchSyscallChecked` refuses
unless the caller is the executing core's current thread, builds its gate from
the caller's TCB and root CNode (the two lookups `abiEntryGate` made), runs the
rights-gated lookup (or the resolve-only one for the two target-first audit
arms, neither of which declares a footprint), dispatches, and applies the taint
plan — which writes only taint words in the store, under the table write lock
every scheduler footprint names, and leaves the scheduler alone. -/
theorem dispatchSyscallChecked_coversWrites (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (e : CoreId)
    (st st' : SystemState) (ops : Concurrency.SyscallLockOperands) (S : LockSet)
    (hObjInv : st.objects.invExt) (hHeads : queueHeadBlockedConsistent st)
    (hOps : abiEntryLockOperands decoded tid st = some ops)
    (hSched : schedLockSetForSyscall (abiEntryFootprintId decoded tid st) ops e st = some S)
    (hDisp : dispatchSyscallChecked ctx decoded tid e st = .ok ((), st')) :
    footprintCoversWrites S st st' := by
  -- WS-ZA ZA4.3: the capability-free yield runs before any lookup, under its
  -- own footprint.
  by_cases hY : decoded.syscallId = .yield
  · rw [abiEntryFootprintId_of_not_replyRecv decoded tid st (by rw [hY]; decide), hY] at hSched
    simp only [schedLockSetForSyscall] at hSched
    unfold dispatchSyscallChecked at hDisp
    split at hDisp
    · exact absurd hDisp (by simp)
    · simp only [dispatchYield] at hDisp
      split at hDisp
      · exact absurd hDisp (by simp)
      · rename_i stY hYieldOk
        simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hDisp
        subst hDisp
        exact schedLockSet_yieldOnCore_coversWrites e st stY S hSched hYieldOk
  obtain ⟨tcb, gate, cap, hGate, hLk, -⟩ :=
    abiEntryLockOperands_gate_lookup decoded tid st ops hY hOps
  obtain ⟨hTcb, -, -, hGateEq⟩ := abiEntryGate_components decoded tid st tcb gate hGate
  have hTcbObj : st.getObject? tid.toObjId = some (.tcb tcb) :=
    (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb
  have hRes : syscallResolveCap gate st = .ok (cap, st) := syscallLookupCap_resolve gate st cap hLk
  have key : ∀ stPost, dispatchWithCapChecked ctx decoded tid e gate cap st = .ok ((), stPost) →
      footprintCoversWrites S st (applySyscallTaint (syscallTaintPlan st tid decoded) st stPost) :=
    fun stPost hD => footprintCoversWrites_trans S
      (dispatchWithCapChecked_coversWrites ctx decoded tid e tcb gate cap st stPost ops S hObjInv
        hHeads hGate hLk hOps hSched hD)
      (footprintCoversWrites_of_scheduler_eq S
        (schedLockSetForSyscall_contains_objStore_write _ _ _ _ _ hSched)
        (applySyscallTaint_scheduler _ _ _))
  unfold dispatchSyscallChecked at hDisp
  split at hDisp
  · exact absurd hDisp (by simp)
  · simp only at hDisp
    rw [hTcbObj] at hDisp
    simp only at hDisp
    rw [← hGateEq] at hDisp
    split at hDisp
    · exact absurd hDisp (by simp)
    · rename_i stPost hD
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hDisp
      subst hDisp
      obtain ⟨cap', hLk', -, hD⟩ := syscallInvokeTyped_ok _ _ _ st () stPost hD
      rw [hLk] at hLk'
      cases hLk'
      exact key stPost hD

-- ============================================================================
-- §3  The ABI syscall seam
-- ============================================================================

/-- A write that keeps every object's type and TCB slots keeps each thread's
CSpace root, which the reply capability's fault reads. -/
theorem finaliseWriteAny_callerCspaceRoot {st st' : SystemState}
    (h : finaliseWriteAny st st') (tid : SeLe4n.ThreadId) :
    callerCspaceRoot st' tid = callerCspaceRoot st tid := by
  unfold callerCspaceRoot
  simp only [SystemState.getObject?_eq_getElem]
  rcases h tid.toObjId with e | ⟨pre, post, hp, hq, hT, hS, -⟩
  · rw [e]
  · rw [hp, hq]
    cases pre <;> cases post <;>
      simp_all [KernelObject.objectType, KernelObject.tcbSlots]

/-- **The refusal's reported state is inside the declared footprint**: either
the spill itself, or the spill with the busy reply's holder cancelled, and then
the operands are the busy receive's, whose footprint is every core's run queue
and moves no reservation the cancel does not keep. -/
theorem cancelReceiveBusyReply_coversWrites (ctx : LabelingContext) (e : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (decoded : SyscallDecodeResult)
    (stRegs stSpilled : SystemState) (ops : Concurrency.SyscallLockOperands) (S U : LockSet)
    (hRegsObjInv : stRegs.objects.invExt)
    (hCur : stRegs.scheduler.currentOnCore e = some tid)
    (hTcbRegs : stRegs.getObject? tid.toObjId = some (.tcb tcb))
    (hDec : SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState
      (threadOperationCode stRegs tid SeLe4n.arm64DefaultLayout tcb.registerContext) stRegs tid
      SeLe4n.arm64DefaultLayout tcb.registerContext 32 = .ok decoded)
    (hFillObj : stSpilled.objects = stRegs.objects)
    (hCode : ∀ gate, recvBusyReplyHolderCode ctx tid gate decoded stSpilled
      = recvBusyReplyHolderCode ctx tid gate decoded stRegs)
    (hXc : ∀ n, callerExtraCapsFault? stSpilled tid n = callerExtraCapsFault? stRegs tid n)
    (hOps : abiEntryLockOperands decoded tid stSpilled = some ops)
    (hSched : schedLockSetForSyscall (abiEntryFootprintId decoded tid stSpilled) ops e stSpilled
      = some S)
    (hU : unifiedLockSetForSyscall (abiEntryFootprintId decoded tid stSpilled) ops e stSpilled
      = some U) :
    footprintCoversWrites U stRegs (cancelReceiveBusyReply ctx e stRegs) := by
  rcases cancelReceiveBusyReply_cases_decoded ctx e stRegs with
    h | ⟨tid', tcb', decoded', k, hCur', hObj', hDec', hRecv', hCode', h⟩
  · rw [h]; exact footprintCoversWrites_refl U stRegs
  rw [h]
  rw [hCur] at hCur'
  cases hCur'
  rw [hTcbRegs] at hObj'
  cases hObj'
  rw [hDec] at hDec'
  cases hDec'
  have hRecvF : receivesWithoutReply decoded tid stSpilled := by
    unfold receivesWithoutReply replyRecvSkipsReply callerReplyGate at hRecv' ⊢
    rw [hXc, callerCspaceRoot_congr_objects tid hFillObj,
      resolveReplyRecvReply_congr_objects _ decoded hFillObj]
    exact hRecv'
  obtain ⟨tcbF, gate, cap, hGate, -, -, -⟩ :=
    abiEntryLockOperands_gate_lookup decoded tid stSpilled ops
      (by rcases hRecvF with h | ⟨h, -⟩ <;> rw [h] <;> decide) hOps
  obtain ⟨hTcbF, -, -, hGateEq⟩ := abiEntryGate_components decoded tid stSpilled tcbF gate hGate
  have hTcbF' := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTcbF
  have hTcbRegs' : stRegs.objects[tid.toObjId]? = some (.tcb tcb) := hTcbRegs
  rw [hFillObj, hTcbRegs'] at hTcbF'
  simp only [Option.some.injEq, KernelObject.tcb.injEq] at hTcbF'
  subst hTcbF'
  have hCodeF : recvBusyReplyHolderCode ctx tid gate decoded stSpilled = k + 1 := by
    rw [hCode]
    exact hCode' gate (by rw [hGateEq]; simp only [callerCspaceRoot, hTcbRegs])
  have hB := recvBusyReplyHolderCode_succ hCodeF
  obtain ⟨epId, hOpsEq⟩ :=
    abiEntryLockOperands_receive_busy decoded tid stSpilled ops _ gate ⟨k⟩ hRecvF hGate hB hOps
  refine unifiedLockSetForSyscall_coversWrites _ _ _ _ S U _ _ hSched hU ?_
  subst hOpsEq
  rw [(abiEntryFootprintId_eq_receive_iff decoded tid stSpilled).mpr hRecvF] at hSched
  simp only [schedLockSetForSyscall, Option.bind_some,
    schedLockSet_receiveCancellingHolderOnCore, hB] at hSched
  exact footprintCoversWrites_of_allCores S _ stRegs _ (LockSet.ofList?_pairs hSched)
    (fun d _ => cancelReplyHolder_replenishQueueOnCore stRegs ⟨k⟩ e d)

/-- **The live ABI syscall step is covered by the unified footprint it declares.**

The seam's pre-state invariant is the object-store invariant with the
queue-head consistency the receive arm's chain walk reads; both transport
across the seam's register spill (a TCB rewrite that keeps every `ipcState`).
On a successful dispatch the step is
the covered dispatcher followed by the covered commit tail; on a refused one it
is the recorded refusal — scheduler-inert — followed by the same tail.  The
capability-fault delivery is unreachable: the operands resolved, so the rights
gated lookup of the decode's capability succeeded at the dispatch state, and
the fault builder re-runs that resolution at the spilled state, whose object
store is the same. -/
theorem syscallDispatchCrossCoreStep_coversWrites (ctx : LabelingContext) (e : CoreId)
    (syscallId : UInt32) (x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30 : UInt64)
    (st : SystemState) (U : LockSet)
    (hInv : st.objects.invExt ∧ queueHeadBlockedConsistent st)
    (hU : declaredUnifiedLockSetForAbiEntry ctx e syscallId x0 x1 x2 x3 x4 x5 x6 st = some U) :
    footprintCoversWrites U st
      (syscallDispatchCrossCoreStep ctx e syscallId x0 x1 x2 x3 x4 x5 x6 elr spsr
        spEl0 x30 st).2 := by
  obtain ⟨hObjInv, hHeads⟩ := hInv
  unfold declaredUnifiedLockSetForAbiEntry at hU
  cases hPlan : abiEntryPlan ctx e syscallId x0 x1 x2 x3 x4 x5 x6 st with
  | none => rw [hPlan] at hU; exact absurd hU (by simp)
  | some triple =>
  obtain ⟨tid, decoded, stSpilled⟩ := triple
  rw [hPlan] at hU
  simp only at hU
  cases hOps : abiEntryLockOperands decoded tid stSpilled with
  | none => rw [hOps] at hU; exact absurd hU (by simp)
  | some ops =>
  rw [hOps] at hU
  simp only [Option.bind_some] at hU
  obtain ⟨S, hSched⟩ := unifiedLockSetForSyscall_some_imp_sched _ _ _ _ _ hU
  have hTable : (LockKey.objStore, AccessMode.write) ∈ U.pairs :=
    mem_unifiedLockSetForSyscall_objStore _ _ _ _ _ hU
  have hRunE : (LockKey.runQueue e, AccessMode.write) ∈ U.pairs :=
    mem_unifiedLockSetForSyscall_executingCore _ _ _ _ _ hU
  obtain ⟨hCur, tcb, hTcbRegs, hDec, hFilled⟩ :=
    abiEntryPlan_components ctx e syscallId x0 x1 x2 x3 x4 x5 x6 st tid decoded stSpilled hPlan
  have hRegsSch := Platform.FFI.writeFfiRegistersToTcb_scheduler st tid syscallId x0 x1 x2 x3 x4 x5 x6
  have hFillObj : stSpilled.objects
      = (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6).objects := by
    rw [hFilled]
  have hFillSch : stSpilled.scheduler
      = (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6).scheduler := by
    rw [hFilled]
  have hRegsObjInv :
      (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6).objects.invExt :=
    SystemState.updateTcb_preserves_objects_invExt _ _ _ hObjInv
  have hFillObjInv : stSpilled.objects.invExt := by rw [hFillObj]; exact hRegsObjInv
  have hRegsHeads :
      queueHeadBlockedConsistent
        (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6) :=
    queueHeadBlockedConsistent_updateTcb_of_ipcState_eq st tid _ hObjInv (fun _ => rfl) hHeads
  have hFillHeads : queueHeadBlockedConsistent stSpilled :=
    queueHeadBlockedConsistent_of_readViewAgreement (.of_getElem_eq (fun oid => by rw [hFillObj])) hRegsHeads
  have hD := abiEntryPlan_dispatches ctx e syscallId x0 x1 x2 x3 x4 x5 x6 elr spsr
    spEl0 x30 st tid decoded stSpilled hPlan
  cases hDisp : dispatchSyscallChecked ctx decoded tid e stSpilled with
  | ok r =>
    obtain ⟨⟨⟩, st'⟩ := r
    rw [hDisp] at hD
    simp only at hD
    rw [syscallDispatchCrossCoreStep_of_ok hD]
    dsimp only
    refine footprintCoversWrites_trans U (footprintCoversWrites_trans U
      (footprintCoversWrites_trans U (footprintCoversWrites_of_scheduler_eq U hTable hRegsSch)
        (footprintCoversWrites_of_objects_scheduler_eq U hFillObj hFillSch)) ?_)
      (syscallCommitTail_coversWrites U e _ st' _ hTable hRunE)
    exact unifiedLockSetForSyscall_coversWrites _ _ _ _ S U stSpilled st' hSched hU
      (dispatchSyscallChecked_coversWrites ctx decoded tid e stSpilled st' ops S hFillObjInv
        hFillHeads hOps hSched hDisp)
  | error ke =>
    rw [hDisp] at hD
    simp only at hD
    -- the state the refusal reports: the spill, or the spill with its busy
    -- reply's holder cancelled, which keeps every CNode and CSpace root
    have hFrameR : callerCspaceRoot (cancelReceiveBusyReply ctx e
          (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6)) tid
        = callerCspaceRoot (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6)
          tid ∧
        ∀ id, (cancelReceiveBusyReply ctx e
          (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6)).getCNode? id
          = (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6).getCNode? id := by
      rcases cancelReceiveBusyReply_cases_holder ctx e
          (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6) with
        h | ⟨_, holder, -, -, h⟩
      · rw [h]; exact ⟨rfl, fun _ => rfl⟩
      · rw [h]
        exact ⟨finaliseWriteAny_callerCspaceRoot
            (cancelReplyHolder_finaliseFrameAny _ holder e hRegsObjInv).write tid,
          cancelReplyHolder_getCNode? _ holder e hRegsObjInv⟩
    have hNoFault : Platform.FFI.syscallCapFaultAt SeLe4n.arm64DefaultLayout
        (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6)
        (cancelReceiveBusyReply ctx e
          (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6)) tid ke
          = none := by
      have hTcbRegs' :
          (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6).objects[tid.toObjId]?
            = some (.tcb tcb) := hTcbRegs
      -- WS-ZA ZA4.3: a yield has no capability-fault phase.
      by_cases hY : decoded.syscallId = .yield
      · exact Platform.FFI.syscallCapFaultAt_none_of_no_fault_phase SeLe4n.arm64DefaultLayout _ _
          tid ke tcb decoded hTcbRegs' hDec (by rw [hY]; rfl)
      obtain ⟨tcbF, gate, cap, hGate, hLk, hRecv, hReplyF⟩ :=
        abiEntryLockOperands_gate_lookup decoded tid stSpilled ops hY hOps
      obtain ⟨hTcbF, -, -, hGateEq⟩ :=
        abiEntryGate_components decoded tid stSpilled tcbF gate hGate
      have hTcbF' := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTcbF
      rw [hFillObj, hTcbRegs'] at hTcbF'
      simp only [Option.some.injEq, KernelObject.tcb.injEq] at hTcbF'
      subst hTcbF'
      have hResolve := syscallResolveCap_congr_objects gate stSpilled _ cap hFillObj
        (syscallLookupCap_resolve gate stSpilled cap hLk)
      subst hGateEq
      cases hPhase : Platform.FFI.capFaultReceivePhase? decoded.syscallId with
      | none =>
        exact Platform.FFI.syscallCapFaultAt_none_of_no_fault_phase SeLe4n.arm64DefaultLayout _ _
          tid ke tcb decoded hTcbRegs' hDec hPhase
      | some inRecv =>
        have hRecv' : receiveGateRefuses decoded.syscallId tid
            (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6) cap = false := by
          rw [← hRecv]
          unfold receiveGateRefuses receiveBoundRefuses notificationBoundElsewhere
            syscallTargetAccepted objectKindIs
          simp only [SystemState.getObject?, SystemState.getNotification?, hFillObj]
        have hRoot : callerCspaceRoot
            (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6) tid
              = tcb.spaceCells[0] := by
          simp only [callerCspaceRoot, hTcbRegs]
        exact Platform.FFI.syscallCapFaultAt_none_of_lookup_ok SeLe4n.arm64DefaultLayout _ _ tid
          ke tcb decoded inRecv hTcbRegs' hDec hPhase
          (by
            have hX := abiEntryLockOperands_extraCaps decoded tid stSpilled ops hY hOps
            rw [hFilled] at hX
            simp [syscallOperandLookup, hResolve, hRecv', hX])
          (by
            rw [hFrameR.1, hRoot, receiveReplyFault?_congr_getCNode? _ decoded _ _ hFrameR.2,
              ← receiveReplyFault?_congr_objects _ decoded _ _ hFillObj]
            exact hReplyF)
    rw [hNoFault] at hD
    simp only at hD
    have hCancel := cancelReceiveBusyReply_coversWrites ctx e tid tcb decoded _ stSpilled ops S U
      hRegsObjInv (by rw [hRegsSch]; exact hCur) hTcbRegs hDec hFillObj
      (fun gate => recvBusyReplyHolderCode_congr_objects ctx tid gate decoded hFillObj)
      (fun n => by rw [hFilled]) hOps hSched hU
    -- WS-SX SX7.2: a `Call` writes the error's fifth word to its IPC buffer;
    -- any other syscall writes nothing but the refusal record
    by_cases hC : syscallId = Syscall.call.number.toUInt32
    · rw [if_pos hC] at hD
      rw [syscallDispatchCrossCoreStep_of_ok hD]
      dsimp only
      refine footprintCoversWrites_trans U (footprintCoversWrites_trans U
        (footprintCoversWrites_trans U
          (footprintCoversWrites_trans U
            (footprintCoversWrites_of_scheduler_eq U hTable hRegsSch) hCancel)
          (footprintCoversWrites_of_scheduler_eq U hTable
            (Architecture.recordErrorOverflow_scheduler _ tid ke)))
        (footprintCoversWrites_of_scheduler_eq U hTable
          (Platform.FFI.recordSyscallRefusal_scheduler_eq ctx e _ tid ke x0 _)))
        (syscallCommitTail_coversWrites U e _ _ _ hTable hRunE)
    · rw [if_neg hC] at hD
      rw [syscallDispatchCrossCoreStep_of_ok hD]
      dsimp only
      refine footprintCoversWrites_trans U (footprintCoversWrites_trans U
        (footprintCoversWrites_trans U
          (footprintCoversWrites_of_scheduler_eq U hTable hRegsSch) hCancel)
        (footprintCoversWrites_of_scheduler_eq U hTable
          (Platform.FFI.recordSyscallRefusal_scheduler_eq ctx e _ tid ke x0 _)))
        (syscallCommitTail_coversWrites U e _ _ _ hTable hRunE)

/-! ### The timer and reschedule entries' tails

WS-ZA ZA6.7.  The timer and reschedule entries run their bracket's step, then
the residency settle and the activation on the same core.  Both tail steps write
the object store and the executing core's run-queue state only, and both
brackets' footprints name the table write lock and that core's run-queue lock,
so the footprint each bracket declares covers the whole committed tail, not the
step alone. -/

/-- **The timer entry's tick, settle and activation are inside its declared
footprint.** -/
theorem perCoreTimerTickEntryTail_coversWrites (st : SystemState) (coreId : UInt64)
    (h : coreId.toNat < Concurrency.numCores) :
    footprintCoversWrites
      ⟨timerTickOnCoreCompleteLockSet ⟨coreId.toNat, h⟩,
        timerTickOnCoreCompleteLockSet_keys_nodup _⟩
      st (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((timerTickBracket coreId).run st).2 coreId) coreId) := by
  have hTable : (LockKey.objStore, AccessMode.write) ∈
      timerTickOnCoreCompleteLockSet ⟨coreId.toNat, h⟩ := List.mem_cons_self
  have hRun : (LockKey.runQueue ⟨coreId.toNat, h⟩, AccessMode.write) ∈
      timerTickOnCoreCompleteLockSet ⟨coreId.toNat, h⟩ :=
    List.mem_cons_of_mem _ (List.mem_append_left _ (mem_allCoreRunQueueLockSegment _))
  unfold activateThreadAt PriorityInheritance.settleResidencyAt
  rw [Concurrency.coreIdOfUInt64?_eq_some coreId h]
  exact footprintCoversWrites_trans _
    (footprintCoversWrites_trans _ (perCoreTimerTickStepWithClockAdvance_coversWrites st coreId h)
      (settleResidencyOnCore_coversWrites _ _ _ hTable hRun))
    (activateThreadOnCore_coversWrites _ _ _ hTable)

/-- **The reschedule entry's step, settle and activation are inside its declared
footprint** — and the secondary core's first entry's, which is this entry. -/
theorem perCoreRescheduleEntryTail_coversWrites (st : SystemState) (coreId : UInt64)
    (h : coreId.toNat < Concurrency.numCores) :
    footprintCoversWrites
      ⟨handleRescheduleSgiOnCoreLockSet ⟨coreId.toNat, h⟩,
        switchToThreadOnCoreLockSet_keys_nodup _⟩
      st (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((rescheduleBracket coreId).run st).2 coreId) coreId) := by
  have hTable : (LockKey.objStore, AccessMode.write) ∈
      handleRescheduleSgiOnCoreLockSet ⟨coreId.toNat, h⟩ := List.mem_cons_self
  have hRun : (LockKey.runQueue ⟨coreId.toNat, h⟩, AccessMode.write) ∈
      handleRescheduleSgiOnCoreLockSet ⟨coreId.toNat, h⟩ :=
    List.mem_cons_of_mem _ List.mem_cons_self
  unfold activateThreadAt PriorityInheritance.settleResidencyAt
  rw [Concurrency.coreIdOfUInt64?_eq_some coreId h]
  exact footprintCoversWrites_trans _
    (footprintCoversWrites_trans _ (perCoreRescheduleStep_coversWrites st coreId h)
      (settleResidencyOnCore_coversWrites _ _ _ hTable hRun))
    (activateThreadOnCore_coversWrites _ _ _ hTable)

/-- WS-ZA ZA6.32: **the interrupt entry's step, settle and activation are inside
its declared footprint**: the step's own coverage
(`interruptEntryStep_coversWrites`), and the settle and the activation under
the table write lock and the executing core's run queue, which the footprint
always names (`declaredLockSetForInterrupt_objStore`, `_runQueue`). -/
theorem interruptEntryTail_coversWrites (st : SystemState) (coreId intId : UInt64)
    (c : CoreId) (hc : Concurrency.coreIdOfUInt64? coreId = some c) (S : LockSet)
    (hInv : st.objects.invExt) (hS : declaredLockSetForInterrupt coreId intId st = some S) :
    footprintCoversWrites S st (activateThreadAt (PriorityInheritance.settleResidencyAt
      ((interruptBracket coreId intId).run st).2 coreId) coreId) := by
  have hTable := declaredLockSetForInterrupt_objStore hS
  have hRun := declaredLockSetForInterrupt_runQueue hS c hc
  unfold activateThreadAt PriorityInheritance.settleResidencyAt
  rw [hc]
  exact footprintCoversWrites_trans _
    (footprintCoversWrites_trans _ (interruptEntryStep_coversWrites coreId intId st S hInv hS)
      (settleResidencyOnCore_coversWrites _ _ _ hTable hRun))
    (activateThreadOnCore_coversWrites _ _ _ hTable)

end SeLe4n.Kernel
