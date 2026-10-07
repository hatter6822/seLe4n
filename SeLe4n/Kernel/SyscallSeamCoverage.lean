/-
  seLe4n — Syscall seam coverage (WS-LS LS2.3)

  The two state-committing seams a declared footprint brackets — the ABI
  syscall step and the raw suspend entry — are covered by the footprint they
  declare: every object-store, run-queue and replenish-queue write the step
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
import SeLe4n.Kernel.SyscallDispatchEntry
import SeLe4n.Kernel.SyscallSchedContainment
import SeLe4n.Kernel.IPC.Invariant.LookupCongruence

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
  · split
    · split
      · rename_i st' h
        exact switchToThreadOnCore_coversWrites S e st st' _ hTable hRun h
      · refine ⟨fun hAbsent => absurd hTable hAbsent, fun d hd => ?_, fun d _ => ?_⟩
        · have hne : e ≠ d := fun hEq => hd (hEq ▸ hRun)
          simp only [preemptCurrentOnCore_runQueueOnCore_ne st e _ d hne,
            preemptCurrentOnCore_currentOnCore, preemptCurrentOnCore_activeDomainOnCore,
            SchedulerState.setCurrentOnCore_runQueueOnCore,
            SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ hne,
            SchedulerState.setCurrentOnCore_activeDomainOnCore]
          exact ⟨trivial, trivial, trivial⟩
        · simp only [SchedulerState.setCurrentOnCore_replenishQueueOnCore,
            preemptCurrentOnCore_replenishQueueOnCore]
    · exact footprintCoversWrites_refl S st
  · exact footprintCoversWrites_refl S st

/-- The residency settling: the dispatch and the deferral are scheduling points
on the executing core, and the residency record is a machine write. -/
theorem settleResidencyOnCore_coversWrites (S : LockSet) (e : CoreId) (st : SystemState)
    (hTable : (LockKey.objStore, AccessMode.write) ∈ S.pairs)
    (hRun : (LockKey.runQueue e, AccessMode.write) ∈ S.pairs) :
    footprintCoversWrites S st (PriorityInheritance.settleResidencyOnCore st e) := by
  unfold PriorityInheritance.settleResidencyOnCore
  exact footprintCoversWrites_trans S
    (footprintCoversWrites_trans S (dispatchVacatedCore_coversWrites S e st hTable hRun)
      (deferResidentElsewhere_coversWrites S e _ hTable hRun))
    (footprintCoversWrites_of_objects_scheduler_eq S rfl rfl)

/-- **The syscall commit's tail is covered**: from the dispatched state, staging
the caller's result (a register write under the table lock), the local successor
and the residency settling (the executing core's own scheduling points), and
the two hardware-ledger clears (scheduler- and store-inert). -/
theorem syscallCommitTail_coversWrites (S : LockSet) (e : CoreId)
    (caller? : Option SeLe4n.ThreadId) (post : SystemState) (o : Architecture.SyscallOutcome)
    (hTable : (LockKey.objStore, AccessMode.write) ∈ S.pairs)
    (hRun : (LockKey.runQueue e, AccessMode.write) ∈ S.pairs) :
    footprintCoversWrites S post
      (Architecture.clearPhysicalWrites (Architecture.clearIcacheMaintenance
        (PriorityInheritance.settleResidencyOnCore
          (PriorityInheritance.scheduleLocalSuccessorFrom caller?
            (Architecture.stageCallerReturnFor caller? post e o) e) e))) :=
  footprintCoversWrites_trans S
    (footprintCoversWrites_trans S
      (footprintCoversWrites_of_scheduler_eq S hTable
        (Architecture.stageCallerReturnFor_scheduler caller? post e o))
      (footprintCoversWrites_trans S
        (scheduleLocalSuccessorFrom_coversWrites S e caller? _ hTable hRun)
        (settleResidencyOnCore_coversWrites S e _ hTable hRun)))
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
    (hSched : schedLockSetForSyscall decoded.syscallId ops e st = some S)
    (hDisp : dispatchWithCapChecked ctx decoded tid e gate cap st = .ok ((), st')) :
    footprintCoversWrites S st st' := by
  have hTable : (LockKey.objStore, AccessMode.write) ∈ S.pairs :=
    schedLockSetForSyscall_contains_objStore_write decoded.syscallId ops e st S hSched
  obtain ⟨hTcb, rootCn, hRoot, hGateEq⟩ := abiEntryGate_components decoded tid st tcb gate hGate
  unfold abiEntryLockOperands at hOps
  rw [hGate] at hOps
  simp only at hOps
  rw [hLk] at hOps
  simp only at hOps
  unfold dispatchWithCapChecked dispatchCapabilityOnly at hDisp
  cases hId : decoded.syscallId <;> rw [hId] at hOps hSched hDisp <;> simp only at hDisp
  all_goals try (simp only [schedLockSetForSyscall, reduceCtorEq] at hSched; done)
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
          refine footprintCoversWrites_trans S (st₂ := retirePendingFaultForResume st vtid.val)
            (footprintCoversWrites_of_scheduler_eq S hTable
              (retirePendingFaultForResume_scheduler_eq st vtid.val)) ?_
          rw [← schedLockSet_resumeThreadOnCore_retire st vtid e hObjInv] at hSched
          exact schedLockSet_resumeThreadOnCore_coversWrites _ st₁ vtid e sgi S hStep hSched
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
  case schedContextConfigure =>
    cases hT : cap.target <;> rw [hT] at hOps <;> simp only [Option.some.injEq, reduceCtorEq] at hOps
    rename_i scId
    subst hOps
    simp only [schedLockSetForSyscall, Concurrency.SyscallLockOperands.ofObjectTarget,
      Option.bind_some] at hSched
    rw [hT] at hDisp
    simp only at hDisp
    split at hDisp
    · exact absurd hDisp (by simp)
    · rename_i args hArgs
      split at hDisp
      · exact absurd hDisp (by simp)
      · rename_i vScId hV
        rw [← validateObjIdArg_ok_val _ _ hV] at hSched
        exact schedLockSet_schedContextConfigureOnCore_coversWrites st st' vScId _ _ _ _ _ S
          hObjInv hDisp hSched
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
          exact schedLockSet_schedContextUnbindOnCore_coversWrites st st₁ vScId e sgi S hStep hSched
        · exact absurd hDisp (by simp)
  -- ---- `.lifecycleRetype` -------------------------------------------------
  case lifecycleRetype =>
    cases hT : cap.target <;> rw [hT] at hOps <;> simp only [reduceCtorEq] at hOps
    rename_i objId
    split at hOps
    · exact absurd hOps (by simp)
    · rename_i args hArgs
      injection hOps with hOps
      subst hOps
      simp only [schedLockSetForSyscall, Concurrency.SyscallLockOperands.ofObjectTarget,
        Option.bind_some] at hSched
      rw [hT] at hDisp
      simp only at hDisp
      rw [hArgs] at hDisp
      simp only at hDisp
      exact schedLockSet_lifecycleRetypeOnCore_coversWrites e cap args.targetObj _ st st' S hDisp
        hSched
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
    · exact absurd hDisp (by simp)
    · rename_i args hArgs
      split at hDisp
      · rename_i st₁ r hSig
        split at hDisp
        · exact absurd hDisp (by simp)
        · rename_i st₂ hClr
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hDisp
          subst hDisp
          have h₁ := notificationSignalBoundCrossCoreDispatchChecked_fst_of_ok ctx nId tid
            args.badge e st st₁ r hSig
          refine footprintCoversWrites_trans S ?_ (footprintCoversWrites_trans S
            (footprintCoversWrites_of_scheduler_eq S hTable
              (clearWokenReceiverStash_scheduler_eq _ _ _ hClr))
            (footprintCoversWrites_of_scheduler_eq S hTable
              (by rw [Architecture.stageWokenDelivery_scheduler_eq,
                Architecture.stageWokenDelivery_scheduler_eq])))
          rw [← h₁]
          exact schedLockSet_notificationSignalBoundOnCore_coversWrites nId args.badge e st S
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
    split at hDisp
    · rename_i st₁ badge hWait
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hDisp
      subst hDisp
      have h₁ := notificationWaitCrossCoreDispatchChecked_fst_of_ok ctx nId tid e st st₁ _ hWait
      refine footprintCoversWrites_trans S ?_ (footprintCoversWrites_of_scheduler_eq S hTable
        (Architecture.writeReturnFrameToTcb_scheduler_eq _ _ _))
      rw [← h₁]
      exact schedLockSet_notificationWaitOnCore_coversWrites nId tid e st S hSched
    · rename_i st₁ hWait
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hDisp
      subst hDisp
      have h₁ := notificationWaitCrossCoreDispatchChecked_fst_of_ok ctx nId tid e st st₁ _ hWait
      rw [← h₁]
      exact schedLockSet_notificationWaitOnCore_coversWrites nId tid e st S hSched
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
    split at hDisp
    · exact absurd hDisp (by simp)
    · rename_i st₂ summary x hSend
      split at hDisp
      · exact absurd hDisp (by simp)
      · rename_i st₃ hClr
        simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hDisp
        subst hDisp
        have hObj₁ := (resolveExtraCaps_objects_scheduler_eq gate.cspaceRoot
          (Architecture.SyscallArgDecode.decodeExtraCapAddrs decoded) gate.capDepth
          (cap.rights.mem .grant) st).1
        have hSch₁ := (resolveExtraCaps_objects_scheduler_eq gate.cspaceRoot
          (Architecture.SyscallArgDecode.decodeExtraCapAddrs decoded) gate.capDepth
          (cap.rights.mem .grant) st).2
        have hObjInv₁ : (resolveExtraCaps gate.cspaceRoot
            (Architecture.SyscallArgDecode.decodeExtraCapAddrs decoded) gate.capDepth
            (cap.rights.mem .grant) st).2.objects.invExt := by
          rw [hObj₁]; exact hObjInv
        have hS₁ : LockSet.ofList? (schedLockSet_endpointSendOnCore (resolveExtraCaps gate.cspaceRoot
            (Architecture.SyscallArgDecode.decodeExtraCapAddrs decoded) gate.capDepth
            (cap.rights.mem .grant) st).2 epId e) = some S := by
          rw [schedLockSet_endpointSendOnCore_congr_objects hObj₁]; exact hSched
        refine footprintCoversWrites_trans S (st₂ := (resolveExtraCaps gate.cspaceRoot
            (Architecture.SyscallArgDecode.decodeExtraCapAddrs decoded) gate.capDepth
            (cap.rights.mem .grant) st).2)
          (footprintCoversWrites_of_scheduler_eq S hTable hSch₁) ?_
        refine footprintCoversWrites_trans S (st₂ := st₂) ?_
          (footprintCoversWrites_trans S (st₂ := st₃)
            (footprintCoversWrites_of_scheduler_eq S hTable
              (clearWokenReceiverStash_scheduler_eq _ _ _ hClr))
            (footprintCoversWrites_of_scheduler_eq S hTable
              (Architecture.stageWokenDelivery_scheduler_eq _ _ _)))
        rw [← show _ = st₂ from congrArg Prod.fst hSend]
        exact schedLockSet_endpointSendOnCore_coversWrites ctx epId tid _ cap.rights
          decoded.capRecvSlot e _ S hObjInv₁ hS₁
  -- ---- `.call` ------------------------------------------------------------
  case call =>
    cases hT : cap.target <;> rw [hT] at hOps <;> simp only [Option.some.injEq, reduceCtorEq] at hOps
    rename_i epId
    subst hOps
    simp only [schedLockSetForSyscall, Option.bind_some] at hSched
    rw [hTcb] at hSched
    simp only [Option.bind_some] at hSched
    rw [hRoot] at hSched
    simp only [Option.bind_some] at hSched
    rw [hT] at hDisp
    subst hGateEq
    simp only at hDisp
    simp only [abiEntryMessage] at hSched
    split at hDisp
    · rename_i st₂ summary x hCallC
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hDisp
      subst hDisp
      have hSch₁ := (resolveExtraCaps_objects_scheduler_eq tcb.cspaceRoot
        (Architecture.SyscallArgDecode.decodeExtraCapAddrs decoded) rootCn.depth
        (cap.rights.mem .grant) st).2
      have hObjInv₁ : (resolveExtraCaps tcb.cspaceRoot
          (Architecture.SyscallArgDecode.decodeExtraCapAddrs decoded) rootCn.depth
          (cap.rights.mem .grant) st).2.objects.invExt := by
        rw [(resolveExtraCaps_objects_scheduler_eq tcb.cspaceRoot
          (Architecture.SyscallArgDecode.decodeExtraCapAddrs decoded) rootCn.depth
          (cap.rights.mem .grant) st).1]
        exact hObjInv
      unfold endpointCallCrossCoreDispatchChecked at hCallC
      split at hCallC
      · refine footprintCoversWrites_trans S (st₂ := (resolveExtraCaps tcb.cspaceRoot
            (Architecture.SyscallArgDecode.decodeExtraCapAddrs decoded) rootCn.depth
            (cap.rights.mem .grant) st).2)
          (footprintCoversWrites_of_scheduler_eq S hTable hSch₁) ?_
        refine footprintCoversWrites_trans S (st₂ := st₂) ?_
          (footprintCoversWrites_of_scheduler_eq S hTable
            (Architecture.stageWokenDelivery_scheduler_eq _ _ _))
        rw [← show _ = st₂ from congrArg Prod.fst hCallC]
        exact schedLockSet_endpointCallOnCore_coversWrites epId tid _ cap.rights
          decoded.capRecvSlot e _ S hObjInv₁ hSched
      · exact absurd (congrArg Prod.snd hCallC) (by simp)
    · exact absurd hDisp (by simp)
  -- ---- `.receive` ---------------------------------------------------------
  case receive =>
    cases hT : cap.target <;> rw [hT] at hOps <;> simp only [reduceCtorEq] at hOps
    rename_i epId
    split at hOps
    · exact absurd hOps (by simp)
    · rename_i replyId? hRR
      injection hOps with hOps
      subst hOps
      simp only [schedLockSetForSyscall, Option.bind_some] at hSched
      rw [hTcb] at hSched
      simp only [Option.bind_some] at hSched
      rw [hT] at hDisp
      simp only at hDisp
      split at hDisp
      · exact absurd hDisp (by simp)
      · rw [hRR] at hDisp
        simp only at hDisp
        split at hDisp
        · rename_i st₁ dequeued summary sgi hLeg
          split at hDisp
          · exact absurd hDisp (by simp)
          · rename_i stDon hHand
            simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hDisp
            subst hDisp
            subst hGateEq
            simp only at hLeg
            refine footprintCoversWrites_trans S (st₂ := stDon) ?_
              (footprintCoversWrites_of_scheduler_eq S hTable
                (by rw [Architecture.stageDeliveredMessage_scheduler_eq,
                  Architecture.stageWokenSendCompletion_scheduler_eq]))
            exact schedLockSet_endpointReceiveOnCore_coversWrites epId tid replyId? tcb.cspaceRoot
              decoded.capRecvSlot e st st₁ stDon dequeued summary sgi S hObjInv hHeads hSched hLeg
              hHand
        · exact absurd hDisp (by simp)
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
        rw [replyTransferOnCoreChecked_eq_unchecked_of_flow_allowed ctx tid callerTid _ _ _ e st
          hFlow] at hDisp
        exact schedLockSet_replyTransferOnCore_coversWrites tid callerTid decoded.msgInfo
          decoded.msgRegs _ e st st' S hObjInv hSched hDisp
      · exact absurd hDisp (by simp)
  -- ---- `.replyRecv` -------------------------------------------------------
  case replyRecv =>
    cases hT : cap.target <;> rw [hT] at hOps <;> simp only [reduceCtorEq] at hOps
    rename_i epId
    split at hOps
    · exact absurd hOps (by simp)
    · rename_i rid prev replyBadge hRRR
      injection hOps with hOps
      subst hOps
      simp only [schedLockSetForSyscall, Option.bind_some] at hSched
      rw [resolveReplyRecvReply_answered gate decoded st rid prev replyBadge hRRR] at hSched
      simp only [Option.bind_some] at hSched
      rw [hTcb] at hSched
      simp only [Option.bind_some] at hSched
      rw [hT] at hDisp
      simp only at hDisp
      split at hDisp
      · exact absurd hDisp (by simp)
      · rw [hRRR] at hDisp
        simp only at hDisp
        split at hDisp
        · split at hDisp
          · rename_i summary st₁ hStep
            simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hDisp
            subst hDisp
            subst hGateEq
            simp only at hStep
            refine footprintCoversWrites_trans S ?_ (footprintCoversWrites_of_scheduler_eq S hTable
              (Architecture.stageDeliveredMessage_scheduler_eq _ _ _))
            exact schedLockSet_endpointReplyRecvOnCore_coversWrites epId tid rid prev _
              tcb.cspaceRoot decoded.capRecvSlot e st st₁ summary S hObjInv hSched hStep
          · exact absurd hDisp (by simp)
        · exact absurd hDisp (by simp)

/-- **The checked dispatcher is covered**: `dispatchSyscallChecked` refuses
unless the caller is the executing core's current thread, builds its gate from
the caller's TCB and root CNode (the two lookups `abiEntryGate` made), runs the
rights-gated lookup (or the resolve-only one for the two target-first audit
arms, neither of which declares a footprint), dispatches, and applies the taint
plan — which writes neither the store nor the scheduler. -/
theorem dispatchSyscallChecked_coversWrites (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (e : CoreId)
    (st st' : SystemState) (ops : Concurrency.SyscallLockOperands) (S : LockSet)
    (hObjInv : st.objects.invExt) (hHeads : queueHeadBlockedConsistent st)
    (hOps : abiEntryLockOperands decoded tid st = some ops)
    (hSched : schedLockSetForSyscall decoded.syscallId ops e st = some S)
    (hDisp : dispatchSyscallChecked ctx decoded tid e st = .ok ((), st')) :
    footprintCoversWrites S st st' := by
  obtain ⟨tcb, gate, cap, hGate, hLk⟩ := abiEntryLockOperands_gate_lookup decoded tid st ops hOps
  obtain ⟨hTcb, rootCn, hRoot, hGateEq⟩ := abiEntryGate_components decoded tid st tcb gate hGate
  have hTcbObj : st.getObject? tid.toObjId = some (.tcb tcb) :=
    (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb
  have hRootObj : st.getObject? tcb.cspaceRoot = some (.cnode rootCn) :=
    (SystemState.getCNode?_eq_some_iff st _ rootCn).mp hRoot
  have hRes : syscallResolveCap gate st = .ok (cap, st) := syscallLookupCap_resolve gate st cap hLk
  have key : ∀ stPost, dispatchWithCapChecked ctx decoded tid e gate cap st = .ok ((), stPost) →
      footprintCoversWrites S st (applySyscallTaint (syscallTaintPlan st tid decoded) st stPost) :=
    fun stPost hD => footprintCoversWrites_trans S
      (dispatchWithCapChecked_coversWrites ctx decoded tid e tcb gate cap st stPost ops S hObjInv
        hHeads hGate hLk hOps hSched hD)
      (footprintCoversWrites_of_objects_scheduler_eq S (applySyscallTaint_objects _ _ _)
        (applySyscallTaint_scheduler _ _ _))
  unfold dispatchSyscallChecked at hDisp
  split at hDisp
  · exact absurd hDisp (by simp)
  · rw [hTcbObj] at hDisp
    simp only at hDisp
    rw [hRootObj] at hDisp
    simp only at hDisp
    rw [← hGateEq] at hDisp
    by_cases hTF : syscallChecksTargetFirst decoded.syscallId = true
    · rw [if_pos hTF] at hDisp
      simp only [syscallInvokeResolved, hRes] at hDisp
      split at hDisp
      · exact absurd hDisp (by simp)
      · rename_i stPost hD
        simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hDisp
        subst hDisp
        exact key stPost hD
    · rw [if_neg hTF] at hDisp
      simp only [syscallInvoke, hLk] at hDisp
      split at hDisp
      · exact absurd hDisp (by simp)
      · rename_i stPost hD
        simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hDisp
        subst hDisp
        exact key stPost hD

-- ============================================================================
-- §3  The ABI syscall seam
-- ============================================================================

/-- **The live ABI syscall step is covered by the unified footprint it declares.**

The seam's pre-state invariant is the object-store invariant with the
queue-head consistency the receive arm's chain walk reads; both transport
across the seam's register spill (a TCB rewrite that keeps every `ipcState`)
and IPC-buffer fill (per-core TLB alone).  On a successful dispatch the step is
the covered dispatcher followed by the covered commit tail; on a refused one it
is the recorded refusal — scheduler-inert — followed by the same tail.  The
capability-fault delivery is unreachable: the operands resolved, so the rights
gated lookup of the decode's capability succeeded at the dispatch state, and
the fault builder re-runs that resolution at the spilled state, whose object
store is the same. -/
theorem syscallDispatchCrossCoreStep_coversWrites (ctx : LabelingContext) (e : CoreId)
    (syscallId : UInt32) (x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64)
    (st : SystemState) (U : LockSet)
    (hInv : st.objects.invExt ∧ queueHeadBlockedConsistent st)
    (hU : declaredUnifiedLockSetForAbiEntry ctx e syscallId x0 x1 x2 x3 x4 x5 st = some U) :
    footprintCoversWrites U st
      (syscallDispatchCrossCoreStep ctx e syscallId x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr
        spEl0 x30 st).2 := by
  obtain ⟨hObjInv, hHeads⟩ := hInv
  unfold declaredUnifiedLockSetForAbiEntry at hU
  cases hPlan : abiEntryPlan ctx e syscallId x0 x1 x2 x3 x4 x5 st with
  | none => rw [hPlan] at hU; exact absurd hU (by simp)
  | some triple =>
  obtain ⟨tid, decoded, stFilled⟩ := triple
  rw [hPlan] at hU
  simp only at hU
  cases hOps : abiEntryLockOperands decoded tid stFilled with
  | none => rw [hOps] at hU; exact absurd hU (by simp)
  | some ops =>
  rw [hOps] at hU
  simp only [Option.bind_some] at hU
  obtain ⟨S, hSched⟩ := unifiedLockSetForSyscall_some_imp_sched _ _ _ _ _ hU
  have hTable : (LockKey.objStore, AccessMode.write) ∈ U.pairs :=
    mem_unifiedLockSetForSyscall_objStore _ _ _ _ _ hU
  have hRunE : (LockKey.runQueue e, AccessMode.write) ∈ U.pairs :=
    mem_unifiedLockSetForSyscall_executingCore _ _ _ _ _ hU
  obtain ⟨_, tcb, hTcbRegs, hDec, hFilled⟩ :=
    abiEntryPlan_components ctx e syscallId x0 x1 x2 x3 x4 x5 st tid decoded stFilled hPlan
  obtain ⟨t, ht⟩ := Architecture.tlbFillIpcBufferOnCore_eq_setPerCoreTlb
    (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) e tid
    decoded.overflowCount
  have hRegsSch := Platform.FFI.writeFfiRegistersToTcb_scheduler st tid syscallId x0 x1 x2 x3 x4 x5
  have hFillObj : stFilled.objects
      = (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5).objects := by
    rw [hFilled, ht]
  have hFillSch : stFilled.scheduler
      = (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5).scheduler := by
    rw [hFilled, ht]
  have hRegsObjInv :
      (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5).objects.invExt :=
    SystemState.updateTcb_preserves_objects_invExt _ _ _ hObjInv
  have hFillObjInv : stFilled.objects.invExt := by rw [hFillObj]; exact hRegsObjInv
  have hRegsHeads :
      queueHeadBlockedConsistent
        (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) :=
    queueHeadBlockedConsistent_updateTcb_of_ipcState_eq st tid _ hObjInv (fun _ => rfl) hHeads
  have hFillHeads : queueHeadBlockedConsistent stFilled :=
    queueHeadBlockedConsistent_of_getElem_eq (fun oid => by rw [hFillObj]) hRegsHeads
  have hD := abiEntryPlan_dispatches ctx e syscallId x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr
    spEl0 x30 st tid decoded stFilled hPlan
  cases hDisp : dispatchSyscallChecked ctx decoded tid e stFilled with
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
    exact unifiedLockSetForSyscall_coversWrites _ _ _ _ S U stFilled st' hSched hU
      (dispatchSyscallChecked_coversWrites ctx decoded tid e stFilled st' ops S hFillObjInv
        hFillHeads hOps hSched hDisp)
  | error ke =>
    rw [hDisp] at hD
    simp only at hD
    have hNoFault : Platform.FFI.syscallCapFaultOf SeLe4n.arm64DefaultLayout
        (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) tid ke
          = none := by
      obtain ⟨tcbF, gate, cap, hGate, hLk⟩ :=
        abiEntryLockOperands_gate_lookup decoded tid stFilled ops hOps
      obtain ⟨hTcbF, rootCn, hRoot, hGateEq⟩ :=
        abiEntryGate_components decoded tid stFilled tcbF gate hGate
      have hTcbRegs' :
          (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5).objects[tid.toObjId]?
            = some (.tcb tcb) := hTcbRegs
      have hTcbF' := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTcbF
      rw [hFillObj, hTcbRegs'] at hTcbF'
      simp only [Option.some.injEq, KernelObject.tcb.injEq] at hTcbF'
      subst hTcbF'
      have hRootRegs :
          (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5).objects[tcb.cspaceRoot]?
            = some (.cnode rootCn) := by
        rw [← hFillObj]; exact (SystemState.getCNode?_eq_some_iff _ _ _).mp hRoot
      have hResolve := syscallResolveCap_congr_objects gate stFilled _ cap hFillObj
        (syscallLookupCap_resolve gate stFilled cap hLk)
      subst hGateEq
      cases hPhase : Platform.FFI.capFaultReceivePhase? decoded.syscallId with
      | none =>
        exact Platform.FFI.syscallCapFaultOf_none_of_no_fault_phase SeLe4n.arm64DefaultLayout _ tid
          ke tcb decoded hTcbRegs' hDec hPhase
      | some inRecv =>
        exact Platform.FFI.syscallCapFaultOf_none_of_resolve_ok SeLe4n.arm64DefaultLayout _ tid ke
          tcb decoded inRecv rootCn cap hTcbRegs' hDec hPhase hRootRegs hResolve
    rw [hNoFault] at hD
    simp only at hD
    rw [syscallDispatchCrossCoreStep_of_ok hD]
    dsimp only
    refine footprintCoversWrites_trans U (footprintCoversWrites_trans U
      (footprintCoversWrites_of_scheduler_eq U hTable hRegsSch)
      (footprintCoversWrites_of_scheduler_eq U hTable
        (Platform.FFI.recordSyscallRefusal_scheduler_eq ctx e syscallId tid ke x0 _)))
      (syscallCommitTail_coversWrites U e _ _ _ hTable hRunE)

-- ============================================================================
-- §4  The raw suspend seam
-- ============================================================================

/-- **The raw suspend seam's action is covered by the unified footprint it
declares**: the suspend on the executing core (the arm's own containment) and
the executing core's local successor; a refused suspend commits nothing.

Stated over the action's state half exactly as `suspendThreadCrossCoreStep`
writes it, so the bracket WS-LS LS2.4 puts at that seam discharges its
`covers` field with this theorem and nothing else. -/
theorem suspendSeamAction_coversWrites (caller : SeLe4n.ThreadId)
    (vtid : SeLe4n.ValidThreadId) (execCore : CoreId) (s : SystemState) (U : LockSet)
    (hU : unifiedLockSetForSyscall .tcbSuspend (.ofThreadTarget caller vtid.val) execCore s
      = some U) :
    footprintCoversWrites U s
      (match Lifecycle.Suspend.suspendThreadOnCore s vtid execCore with
       | .ok (s', _) =>
           PriorityInheritance.scheduleLocalSuccessorFrom (s.scheduler.currentOnCore execCore)
             s' execCore
       | .error _ => s) := by
  obtain ⟨S, hSched⟩ := unifiedLockSetForSyscall_some_imp_sched _ _ _ _ _ hU
  have hTable := mem_unifiedLockSetForSyscall_objStore _ _ _ _ _ hU
  have hRunE := mem_unifiedLockSetForSyscall_executingCore _ _ _ _ _ hU
  have hS : LockSet.ofList? (schedLockSet_suspendThreadOnCore s vtid execCore) = some S := by
    simpa [schedLockSetForSyscall, Concurrency.SyscallLockOperands.ofThreadTarget,
      validThreadId_val_toValid?] using hSched
  split
  · rename_i s' sgi hStep
    exact footprintCoversWrites_trans U
      (unifiedLockSetForSyscall_coversWrites _ _ _ _ S U s s' hSched hU
        (schedLockSet_suspendThreadOnCore_coversWrites s s' vtid execCore sgi S hStep hS))
      (scheduleLocalSuccessorFrom_coversWrites U execCore _ s' hTable hRunE)
  · exact footprintCoversWrites_refl U s

end SeLe4n.Kernel
