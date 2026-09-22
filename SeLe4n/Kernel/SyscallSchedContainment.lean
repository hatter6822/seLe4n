-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
-- STATUS: staged for WS-RR RR8.12 Cut C6a — the syscall arms' scheduler-domain
-- write-set containment.  Staged because every proof here consumes an SM8.B
-- confinement theorem and those live in `InformationFlow/NonInterferenceCrossCore`,
-- which is staged; a proof links into no image, and CI builds this module on
-- every PR through `Platform.Staged`.  The reschedule seam's counterpart
-- (`perCoreRescheduleStep_coversWrites`) is production for the mirror-image
-- reason — the switch's frames are.
import SeLe4n.Kernel.SyscallSchedFootprint
import SeLe4n.Kernel.SchedLockBracket
import SeLe4n.Kernel.InformationFlow.NonInterferenceCrossCore

/-!
# WS-RR RR8.12 Cut C6a — the non-donating arms' footprints are not false

A footprint that omits an object the transition writes is **false**, and
everything built on it — the 2PL serialisation results, `boundedWait_under_2pl`,
the CC-5 contention bound — is then *silent* about that object rather than
conservative.  That is the standing rule this project applies to the object
domain, and `UncoveredLockDomain.syscallSeamSchedulerDomain` is the register
entry saying the scheduler domain has not yet met it at the syscall seam.

Cut C4 gave every declared arm a footprint and Cut C4b wired the ABI entry to
the resolver.  What neither did is prove the footprints **cover** — and the
numbering rule's semantic half says the coverage lands before the bracket, not
after it, because a bracket that acquires a footprint nobody proved covers the
writes hands out exclusion the runtime never established.

## The split, and why it is semantic rather than convenient

`schedFootprintCoversWrites`'s replenish clause is a different *proposition* for
the two halves of the family.  Where an arm's replenish segment is `[]` — it
moves no scheduling context — the clause is a **whole-state frame**: the
transition writes no core's replenishment at all.  Where the segment names
cores, the clause is an **exactness** claim: unchanged outside exactly those.
This module holds the first group, and the arms whose segment names cores
(`.receive`, `.call`, `.reply`, `.replyRecv`, `.tcbSetAffinity`,
`.schedContextConfigure`, `.schedContextUnbind`, `.lifecycleRetype`) are Cut
C6b's, together with the `_ne` frames they need.

`.tcbSuspend` is here despite a non-empty segment, because WS-RR RR8.12's
fourth cut already built its exactness frame
(`suspendThreadOnCore_replenishQueueOnCore_ne`).

## How each proof goes

One application of `schedFootprintCoversWrites_of_cores` (`SchedLockBracket.lean`),
which discharges the object clause structurally — a canonical footprint always
names the object-store table write lock — and reduces the other two to the arm's
own SM8.B confinement result and its own replenish frame.  Both exist for every
arm below; none of them is re-derived here.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId AccessMode)

-- ============================================================================
-- §1  The confinement bridge
-- ============================================================================

/-- **WS-RR RR8.12 Cut C6a**: SM8.B confinement supplies the run-queue clause.

`observableSlotsConfinedToCores` covers six per-core slots and
`schedFootprintCoversWrites`'s run-queue clause asks for three of them, so the
bridge is a projection — stated once rather than spelled at every arm, and the
reason the replenish clause is *not* here: the replenish queue is not one of the
six, which is exactly why every donating arm carries a frame of its own. -/
theorem schedFootprintCoversWrites_of_confined (S : SchedLockSet)
    (runCores replenishCores : List CoreId) (st st' : SystemState)
    (hS : S.pairs = schedFootprintOfCores runCores replenishCores)
    (hConf : observableSlotsConfinedToCores st st' runCores)
    (hRepl : ∀ d : CoreId, d ∉ replenishCores →
      st'.scheduler.replenishQueueOnCore d = st.scheduler.replenishQueueOnCore d) :
    schedFootprintCoversWrites S st st' :=
  schedFootprintCoversWrites_of_cores S runCores replenishCores st st' hS
    (fun d hd => ⟨hConf.runQueue d hd, hConf.current d hd, hConf.activeDomain d hd⟩)
    hRepl

-- ============================================================================
-- §2  The two notification arms
-- ============================================================================

/-- **Cut C6a**: `.notificationWait`'s footprint covers its writes.

The simplest arm in the family and the shape of every proof below: the run
segment is the executing core alone, the replenish segment is empty because a
wait moves no scheduling context, and both halves are the arm's own theorems. -/
theorem schedLockSet_notificationWaitOnCore_coversWrites
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) (executingCore : CoreId)
    (st : SystemState) (S : SchedLockSet)
    (hS : SchedLockSet.ofList? (schedLockSet_notificationWaitOnCore executingCore) = some S) :
    schedFootprintCoversWrites S st
      (notificationWaitOnCore notificationId waiter executingCore st).1 :=
  schedFootprintCoversWrites_of_confined S [executingCore] [] st _
    (SchedLockSet.ofList?_pairs hS)
    (notificationWaitOnCore_confinedToCores notificationId waiter executingCore st)
    (fun d _ => notificationWaitOnCore_replenishQueueOnCore notificationId waiter
      executingCore st d)

/-- **Cut C6a**: `.notificationSignal`'s footprint covers its writes.

Stated of the **bound** arm, which is the one the live dispatch routes to and the
one `schedLockSetForSyscall` names (Cut 7); the bare signal's footprint is
registered as superseded in `SchedFootprintCensus` and its coverage would be a
claim about a transition no syscall reaches. -/
theorem schedLockSet_notificationSignalBoundOnCore_coversWrites
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) (S : SchedLockSet) (hObjInv : st.objects.invExt)
    (hS : SchedLockSet.ofList? (schedLockSet_notificationSignalBoundOnCore st notificationId)
      = some S) :
    schedFootprintCoversWrites S st
      (notificationSignalBoundOnCore notificationId badge executingCore st).1 :=
  schedFootprintCoversWrites_of_confined S (notificationSignalBoundWriteSet st notificationId)
    [] st _ (SchedLockSet.ofList?_pairs hS)
    (notificationSignalBoundOnCore_confinedToCores notificationId badge executingCore st hObjInv)
    (fun d _ => notificationSignalBoundOnCore_replenishQueueOnCore notificationId badge
      executingCore st d)

-- ============================================================================
-- §3  The send arm
-- ============================================================================

/-- **Cut C6a**: `.send`'s footprint covers its writes.

A send rendezvous wakes a receiver on the receiver's home core and may park the
sender on its own, which is the two-element run segment; it moves no scheduling
context, so the replenish segment is empty and the frame is whole-state. -/
theorem schedLockSet_endpointSendOnCore_coversWrites (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) (S : SchedLockSet)
    (hObjInv : st.objects.invExt)
    (hS : SchedLockSet.ofList? (schedLockSet_endpointSendOnCore st endpointId executingCore)
      = some S) :
    schedFootprintCoversWrites S st
      (endpointSendCrossCoreDispatchChecked ctx endpointId sender msg endpointRights
        receiverSlotBase executingCore st).1 :=
  schedFootprintCoversWrites_of_confined S (endpointSendWriteSet st endpointId executingCore)
    [] st _ (SchedLockSet.ofList?_pairs hS)
    (endpointSendCrossCoreDispatchChecked_confinedToCores ctx endpointId sender msg
      endpointRights receiverSlotBase executingCore st hObjInv)
    (fun d _ => endpointSendCrossCoreDispatchChecked_replenishQueueOnCore ctx endpointId sender
      msg endpointRights receiverSlotBase executingCore st _ d rfl)

-- ============================================================================
-- §4  The three TCB-control arms
-- ============================================================================

/-- **Cut C6a**: `.tcbResume`'s footprint covers its writes. -/
theorem schedLockSet_resumeThreadOnCore_coversWrites (st st' : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind)) (S : SchedLockSet)
    (hStep : Lifecycle.Suspend.resumeThreadOnCore st vtid executingCore = .ok (st', sgi))
    (hS : SchedLockSet.ofList? (schedLockSet_resumeThreadOnCore st vtid executingCore)
      = some S) :
    schedFootprintCoversWrites S st st' :=
  schedFootprintCoversWrites_of_confined S (resumeThreadOnCoreWriteSet st vtid executingCore)
    [] st st' (SchedLockSet.ofList?_pairs hS)
    (resumeThreadOnCore_confinedToCores st st' vtid executingCore sgi hStep)
    (fun d _ => resumeThreadOnCore_replenishQueueOnCore st st' vtid executingCore sgi d hStep)

/-- **Cut C6a**: `.tcbSetPriority`'s footprint covers its writes.

The priority arms share `schedLockSet_priorityControlOnCore`, because the two
transitions write the same slots: `.tcbSetMCPriority`'s ceiling change can move
the target's effective band exactly as `.tcbSetPriority`'s base change can. -/
theorem schedLockSet_setPriorityOnCore_coversWrites (st st' : SystemState)
    (vCallerTid vTargetTid : SeLe4n.ValidThreadId) (newPriority : SeLe4n.Priority)
    (executingCore : CoreId) (sgi : Option (CoreId × Concurrency.SgiKind))
    (S : SchedLockSet)
    (hStep : SchedContext.PriorityManagement.setPriorityOnCore st vCallerTid vTargetTid
      newPriority executingCore = .ok (st', sgi))
    (hS : SchedLockSet.ofList?
      (schedLockSet_priorityControlOnCore st vTargetTid.val executingCore) = some S) :
    schedFootprintCoversWrites S st st' :=
  schedFootprintCoversWrites_of_confined S
    (priorityControlWriteSet st vTargetTid.val executingCore) [] st st'
    (SchedLockSet.ofList?_pairs hS)
    (setPriorityOnCore_confinedToCores st st' vCallerTid vTargetTid newPriority executingCore
      sgi hStep)
    (fun d _ => setPriorityOnCore_replenishQueueOnCore st st' vCallerTid vTargetTid newPriority
      executingCore sgi d hStep)

/-- **Cut C6a**: `.tcbSetMCPriority`'s footprint covers its writes. -/
theorem schedLockSet_setMCPriorityOnCore_coversWrites (st st' : SystemState)
    (vCallerTid vTargetTid : SeLe4n.ValidThreadId) (newMCP : SeLe4n.Priority)
    (executingCore : CoreId) (sgi : Option (CoreId × Concurrency.SgiKind))
    (S : SchedLockSet) (hObjInv : st.objects.invExt)
    (hStep : SchedContext.PriorityManagement.setMCPriorityOnCore st vCallerTid vTargetTid
      newMCP executingCore = .ok (st', sgi))
    (hS : SchedLockSet.ofList?
      (schedLockSet_priorityControlOnCore st vTargetTid.val executingCore) = some S) :
    schedFootprintCoversWrites S st st' :=
  schedFootprintCoversWrites_of_confined S
    (priorityControlWriteSet st vTargetTid.val executingCore) [] st st'
    (SchedLockSet.ofList?_pairs hS)
    (setMCPriorityOnCore_confinedToCores st st' vCallerTid vTargetTid newMCP executingCore
      sgi hObjInv hStep)
    (fun d _ => setMCPriorityOnCore_replenishQueueOnCore st st' vCallerTid vTargetTid newMCP
      executingCore sgi d hStep)

-- ============================================================================
-- §5  The bind arm
-- ============================================================================

/-- **Cut C6a**: `.schedContextBind`'s footprint covers its writes.

The bind moves no replenishment, which is the divergence from seL4-MCS this
tree's register keeps (`schedContext_bindTCB` ends in `SCHED_ENQUEUE`): it
re-buckets only a thread already queued on its home core.  So the replenish
clause is a whole-state frame today, and the row that closes that divergence is
the one that will have to widen this footprint. -/
theorem schedLockSet_schedContextBindOnCore_coversWrites (st st' : SystemState)
    (vScId : SeLe4n.ValidObjId) (vThreadId : SeLe4n.ValidThreadId) (S : SchedLockSet)
    (hObjInv : st.objects.invExt)
    (hStep : SchedContextOps.schedContextBind vScId vThreadId st = .ok ((), st'))
    (hS : SchedLockSet.ofList? (schedLockSet_schedContextBindOnCore st vThreadId.val)
      = some S) :
    schedFootprintCoversWrites S st st' :=
  schedFootprintCoversWrites_of_confined S (schedContextBindWriteSet st vThreadId.val) []
    st st' (SchedLockSet.ofList?_pairs hS)
    (schedContextBind_confinedToCores vScId vThreadId st st' hObjInv hStep)
    (fun d _ => schedContextBind_replenishQueueOnCore st st' vScId vThreadId d hStep)

-- ============================================================================
-- §6  The suspend arm
-- ============================================================================

/-- **Cut C6a**: `.tcbSuspend`'s footprint covers its writes.

Here despite a non-empty replenish segment, because WS-RR RR8.12's fourth cut
built the exactness frame this needs — `suspendThreadOnCore_replenishQueueOnCore_ne`,
over the seven stages of the pipeline, two of which move a reservation and five
of which frame every replenish queue.  The other arms with a non-empty segment
are Cut C6b's, with the frames they need. -/
theorem schedLockSet_suspendThreadOnCore_coversWrites (st st' : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind)) (S : SchedLockSet)
    (hStep : Lifecycle.Suspend.suspendThreadOnCore st vtid executingCore = .ok (st', sgi))
    (hS : SchedLockSet.ofList? (schedLockSet_suspendThreadOnCore st vtid executingCore)
      = some S) :
    schedFootprintCoversWrites S st st' :=
  schedFootprintCoversWrites_of_confined S (suspendThreadOnCoreWriteSet st vtid executingCore)
    (suspendThreadReplenishCores st vtid executingCore) st st'
    (SchedLockSet.ofList?_pairs hS)
    (suspendThreadOnCore_confinedToCores st st' vtid executingCore sgi hStep)
    (fun d hd => suspendThreadOnCore_replenishQueueOnCore_ne st st' vtid executingCore sgi d
      hd hStep)

-- ============================================================================
-- §10  The IPC arms
-- ============================================================================

/-- **WS-RR RR8.12 Cut C6c**: `.call`'s footprint covers its writes.

Stated of the **unchecked** dispatch, which is what the write set and the
confinement result are stated at and what the checked arm equals wherever its
flow gate admits; a denied flow commits nothing, so the covered set is the same
one either way.

The replenish segment's branch structure and the dispatch's are the *same*
structure by construction (Cut C3a), which is what makes the exactness frame one
case split rather than a second reading of the transition. -/
theorem schedLockSet_endpointCallOnCore_coversWrites (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (S : SchedLockSet) (hObjInv : st.objects.invExt)
    (hS : SchedLockSet.ofList? (schedLockSet_endpointCallOnCore endpointId caller msg
      endpointRights receiverSlotBase executingCore st) = some S) :
    schedFootprintCoversWrites S st
      (endpointCallCrossCoreDispatch endpointId caller msg endpointRights receiverSlotBase
        executingCore st).1 :=
  schedFootprintCoversWrites_of_confined S
    (endpointCallDispatchWriteSet endpointId caller msg endpointRights receiverSlotBase
      executingCore st)
    (endpointCallDispatchReplenishCores endpointId caller msg endpointRights receiverSlotBase
      executingCore st) st _ (SchedLockSet.ofList?_pairs hS)
    (endpointCallCrossCoreDispatch_confinedToCores endpointId caller msg endpointRights
      receiverSlotBase executingCore st hObjInv)
    (fun d hd => endpointCallCrossCoreDispatch_replenishQueueOnCore_ne endpointId caller msg
      endpointRights receiverSlotBase executingCore st d hd)

-- ============================================================================
-- §7  What the obligation refuses
-- ============================================================================
--
-- Eight coverage theorems above, and none of them could be *wrong* — they are
-- proved.  What they could be is **vacuous**, if `schedFootprintCoversWrites`
-- held of any footprint whatever.  These two say it does not, one clause each,
-- and they are what makes the eight claims measurements rather than notation.

/-- **Cut C6a**: an under-declared run segment is REFUTED by a step that moved
that core's run queue.

The direction the whole family exists for: a footprint that omits a core the
transition writes is false, and everything built on it — the 2PL serialisation
results, `boundedWait_under_2pl`, the CC-5 contention bound — is then *silent*
about that core rather than conservative. -/
theorem not_schedFootprintCoversWrites_of_runQueue_moved (S : SchedLockSet)
    (st st' : SystemState) (d : CoreId)
    (hAbsent : (SchedLockId.runQueue ⟨d⟩, AccessMode.write) ∉ S.pairs)
    (hMoved : st'.scheduler.runQueueOnCore d ≠ st.scheduler.runQueueOnCore d) :
    ¬ schedFootprintCoversWrites S st st' :=
  fun h => hMoved (h.2.1 d hAbsent).1

/-- **Cut C6a**: and an under-declared replenish segment is refuted the same way.

Stated separately because it is the clause SM8.B's confinement cannot supply —
`observableSlotsConfinedToCores` covers six per-core slots and the replenish
queue is not one of them — so an arm whose replenish frame were missing would
have no route to the obligation at all rather than a weaker one. -/
theorem not_schedFootprintCoversWrites_of_replenish_moved (S : SchedLockSet)
    (st st' : SystemState) (d : CoreId)
    (hAbsent : (SchedLockId.replenishQueue ⟨d⟩, AccessMode.write) ∉ S.pairs)
    (hMoved : st'.scheduler.replenishQueueOnCore d ≠ st.scheduler.replenishQueueOnCore d) :
    ¬ schedFootprintCoversWrites S st st' :=
  fun h => hMoved (h.2.2 d hAbsent)

-- ============================================================================
-- §8  The SchedContext arms
-- ============================================================================
--
-- The first arms whose replenish segment names a core, so the clause is an
-- **exactness** claim rather than a whole-state frame.  Each is one application
-- of the bridge, because RR8.12's own `_ne` frames are keyed on the footprint's
-- segment: a resolution-keyed frame answers a different question that every
-- consumer would then have to case-split to reach, which is the duplication this
-- family exists to avoid.

/-- **WS-RR RR8.12 Cut C6b**: `.schedContextConfigure`'s footprint covers its
writes.

A reconfiguration rewrites the reservation and re-queues its replenishment on the
bound thread's home, and nothing else — and the unresolved arm is not a gap but a
refusal, since the transition's own branch errors there. -/
theorem schedLockSet_schedContextConfigureOnCore_coversWrites (st st' : SystemState)
    (vScId : SeLe4n.ValidObjId) (budget period priority deadline domain : Nat)
    (S : SchedLockSet) (hObjInv : st.objects.invExt)
    (hStep : SchedContextOps.schedContextConfigure vScId budget period priority deadline
      domain st = .ok ((), st'))
    (hS : SchedLockSet.ofList? (schedLockSet_schedContextConfigureOnCore st vScId.val)
      = some S) :
    schedFootprintCoversWrites S st st' :=
  schedFootprintCoversWrites_of_confined S (schedContextWriteSet st vScId.val)
    (schedContextConfigureReplenishCores st vScId.val) st st'
    (SchedLockSet.ofList?_pairs hS)
    (schedContextConfigure_confinedToCores vScId budget period priority deadline domain st st'
      hObjInv hStep)
    (fun d hd => schedContextConfigure_replenishQueueOnCore_ne st st' vScId budget period
      priority deadline domain d hd hStep)

/-- **Cut C6b**: `.schedContextUnbind`'s footprint covers its writes.

Three resolutions, and the third is why the segment can be `allCores`: a
SchedContext bound to a thread the store no longer holds has no `cpuAffinity`
left to read, so the unbind sweeps every core's replenishment and the footprint
declares every core's lock. -/
theorem schedLockSet_schedContextUnbindOnCore_coversWrites (st st' : SystemState)
    (vScId : SeLe4n.ValidObjId) (executingCore : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind)) (S : SchedLockSet)
    (hStep : SchedContextOps.schedContextUnbindOnCore vScId executingCore st = .ok (st', sgi))
    (hS : SchedLockSet.ofList?
      (schedLockSet_schedContextUnbindOnCore st vScId.val executingCore) = some S) :
    schedFootprintCoversWrites S st st' :=
  schedFootprintCoversWrites_of_confined S
    (schedContextUnbindOnCoreWriteSet st vScId.val executingCore)
    (schedContextUnbindReplenishCores st vScId.val) st st'
    (SchedLockSet.ofList?_pairs hS)
    (schedContextUnbindOnCore_confinedToCores vScId executingCore st st' sgi hStep)
    (fun d hd => schedContextUnbindOnCore_replenishQueueOnCore_ne st st' vScId executingCore
      sgi d hd hStep)

-- ============================================================================
-- §9  The affinity arm
-- ============================================================================

/-- **Cut C6b**: `.tcbSetAffinity`'s footprint covers its writes.

Two cores in the segment when the thread holds a reservation — the home it leaves
and the one it is pinned to — and none when it holds none.  The unpin request is
`affinity = none`, whose destination is the boot core, so the segment names that
core rather than reading "no core" as "no move". -/
theorem schedLockSet_setThreadCpuAffinityOnCore_coversWrites (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (affinity : Option CoreId) (executingCore : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind)) (S : SchedLockSet)
    (hObjInv : st.objects.invExt)
    (hStep : setThreadCpuAffinityWithMigration st tid affinity executingCore = .ok (st', sgi))
    (hS : SchedLockSet.ofList? (schedLockSet_setThreadCpuAffinityOnCore st tid affinity)
      = some S) :
    schedFootprintCoversWrites S st st' :=
  schedFootprintCoversWrites_of_confined S (setThreadCpuAffinityWriteSet st tid affinity)
    (setThreadCpuAffinityReplenishCores st tid affinity) st st'
    (SchedLockSet.ofList?_pairs hS)
    (setThreadCpuAffinityWithMigration_confinedToCores st st' tid affinity executingCore sgi
      hObjInv hStep)
    (fun d hd => setThreadCpuAffinityWithMigration_replenishQueueOnCore_ne st st' tid affinity
      executingCore sgi d hObjInv hd hStep)

end SeLe4n.Kernel
