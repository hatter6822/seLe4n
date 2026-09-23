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

The bind moves no replenishment — a reservation changes owner, and its
replenishments were already on the home core the binding names — so the
replenish clause is a whole-state frame, on all **three** of the arm's branches
since WS-RR RR8.12 Cut B2 (`v0.35.182`) made it place a parked runnable thread.

That cut is the one this docstring used to say *"will have to widen this
footprint"*, and it did not: the run segment is
`[determineTargetCore st tid]`, which is the core the placement inserts on and
the core the re-bucket already wrote.  A declaration written for the operation
rather than for the branch it happened to take is what makes a behavioural
widening free here. -/
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

/-- **WS-RR RR8.12 Cut C6d**: `.reply`'s footprint covers its writes — of the
**arm**, `replyTransferOnCore`, not of the dispatch beneath it.

That distinction is the whole content of this theorem.  The arm's **post-state**
is not the dispatch's: on an unfaulted caller it is the dispatch's plus the
delivered-message staging, and on a faulted one the dispatch's plus the decoded
outcome — a restart frame, or an abandon that *deschedules* the faulted thread.
A coverage claim proved at the dispatch is therefore a claim about a different
state, and until this theorem the arm's declared footprint
(`schedLockSet_replyTransferOnCore`, `IPC/CrossCore/Fault.lean` §6) had nothing
behind it.

Both halves are keyed on the seam's own predicate `threadHasPendingFault`, so
the footprint and the transition cannot disagree about which caller is faulted.
What the abandon's core costs is measured rather than assumed: it is
`determineTargetCore st' faulted`, and every successful dispatch already names
`determineTargetCore st target`, so on this tree the append is a duplicate
(`tests/FaultHandlingSuite.lean` §7c). The declaration is derived from the arm
anyway, because one tightened to that coincidence would become false the moment
either side moved. -/
theorem schedLockSet_replyTransferOnCore_coversWrites (replier callerTid : SeLe4n.ThreadId)
    (mi : MessageInfo) (regs : Array SeLe4n.RegValue) (msg : IpcMessage)
    (executingCore : CoreId) (st st' : SystemState) (S : SchedLockSet)
    (hObjInv : st.objects.invExt)
    (hS : SchedLockSet.ofList? (schedLockSet_replyTransferOnCore replier callerTid mi regs
      msg executingCore st) = some S)
    (hStep : replyTransferOnCore replier callerTid mi regs msg executingCore st
      = .ok ((), st')) :
    schedFootprintCoversWrites S st st' :=
  schedFootprintCoversWrites_of_confined S
    (replyTransferWriteSet replier callerTid mi regs msg executingCore st)
    (replyTransferReplenishCores replier callerTid msg executingCore st) st st'
    (SchedLockSet.ofList?_pairs hS)
    (replyTransferOnCore_confinedToCores replier callerTid mi regs msg executingCore st st'
      hObjInv hStep)
    (fun d hd => replyTransferOnCore_replenishQueueOnCore_ne replier callerTid mi regs msg
      executingCore st st' d hd hStep)

/-- **WS-RR RR8.12 Cut C6e**: `.replyRecv`'s footprint covers its writes.

The arm whose footprint covers its **whole** body: `replyRecvBodyWriteSet` re-runs
the spine to the state each of the two chain walks starts from and appends
`pipChainWriteSet` there (Cut C2), so the walked members' run queues are static
members rather than a dynamically declared extension — which is what makes this a
complete coverage claim and not a claim about a prefix.  `.receive` is the one
declared arm whose walk sits outside its run segment.

The replenish half is the four-stage composition: the pop's pair, the block path's
pair, the re-donation's pair, each read at the state its own stage runs on, with
the tail writing no replenish queue at all. -/
theorem schedLockSet_endpointReplyRecvOnCore_coversWrites (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId)
    (msg : IpcMessage) (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st st' : SystemState) (summary : CapTransferSummary)
    (S : SchedLockSet) (hObjInv : st.objects.invExt)
    (hS : SchedLockSet.ofList? (schedLockSet_endpointReplyRecvOnCore endpointId receiver replyId
      prevCaller msg receiverCspaceRoot receiverSlotBase executingCore st) = some S)
    (hStep : replyRecvBody endpointId receiver replyId prevCaller msg receiverCspaceRoot
        receiverSlotBase executingCore st = .ok (summary, st')) :
    schedFootprintCoversWrites S st st' :=
  schedFootprintCoversWrites_of_confined S
    (replyRecvBodyWriteSet endpointId receiver replyId prevCaller msg receiverCspaceRoot
      receiverSlotBase executingCore st)
    (replyRecvHandoffReplenishCores endpointId receiver replyId prevCaller msg receiverCspaceRoot
      receiverSlotBase executingCore st) st st' (SchedLockSet.ofList?_pairs hS)
    (replyRecvBody_confinedToCores endpointId receiver replyId prevCaller msg receiverCspaceRoot
      receiverSlotBase executingCore st st' summary hObjInv hStep)
    (fun d hd => replyRecvBody_replenishQueueOnCore_ne endpointId receiver replyId prevCaller msg
      receiverCspaceRoot receiverSlotBase executingCore st st' summary d hObjInv hd hStep)

/-- **WS-RR RR8.12 Cut C6f**: `.receive`'s footprint covers its writes — the leg
composed with WS-OD OD3.6's donation, which is what that footprint bounds.

**Not the chain walk**, and that is the arm's own design rather than a gap here:
`.receive` is the one declared arm whose walk sits outside its run segment
(`endpointReceiveDualWriteSet` is the leg's), because the walk's cores are
state-discovered and are declared dynamically through `pipChainSchedFootprint`
under the `pipChainStart_endpointReceive` obligation.  A bracket acquires the two
together; a coverage claim stated at the whole hand-off would be *false* of this
footprint, which is why the unit here is the leg and the donation.

The run half is free: the donation is per-core silent (it moves a budget, not a
scheduling decision), so the composition is confined to the leg's own set.  The
replenish half is the arm's three shapes under one keyed frame. -/
theorem schedLockSet_endpointReceiveOnCore_coversWrites (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st st1 stDon : SystemState) (dequeued : SeLe4n.ThreadId)
    (summary : CapTransferSummary) (sgi : Option (CoreId × Concurrency.SgiKind)) (S : SchedLockSet)
    (hObjInv : st.objects.invExt) (hHeads : queueHeadBlockedConsistent st)
    (hS : SchedLockSet.ofList? (schedLockSet_endpointReceiveOnCore st endpointId receiver
      executingCore) = some S)
    (hLeg : endpointReceiveDualWithCapsOnCore endpointId receiver replyId receiverCspaceRoot
      receiverSlotBase executingCore st = (st1, .ok (dequeued, summary, sgi)))
    (hDon : applyReceiveRendezvousDonation st1 receiver dequeued = .ok stDon) :
    schedFootprintCoversWrites S st stDon :=
  schedFootprintCoversWrites_of_confined S
    (endpointReceiveDualWriteSet st endpointId executingCore)
    (endpointReceiveHandoffReplenishCores st endpointId receiver) st stDon
    (SchedLockSet.ofList?_pairs hS)
    (observableSlotsConfinedToCores_mono (fun _ hm => by simpa using hm)
      (observableSlotsConfinedToCores_trans
        (by
          have h := endpointReceiveDualWithCapsOnCore_confinedToCores endpointId receiver replyId
            receiverCspaceRoot receiverSlotBase executingCore st hObjInv
          rw [hLeg] at h
          exact h)
        (applyReceiveRendezvousDonation_confinedToCores st1 stDon receiver dequeued hDon)))
    (fun d hd => endpointReceiveLegAndDonation_replenishQueueOnCore_ne endpointId receiver replyId
      receiverCspaceRoot receiverSlotBase executingCore st st1 stDon dequeued summary sgi d
      hObjInv hHeads hd hLeg hDon)

-- ============================================================================
-- §7  What the obligation refuses
-- ============================================================================
--
-- Every coverage theorem above is *proved*, so none of them can be wrong.  What
-- they could all be is **vacuous**, if `schedFootprintCoversWrites` held of any
-- footprint whatever.  These two say it does not, one clause each, and they are
-- what makes the claims above measurements rather than notation.  (No count here:
-- a hand-kept figure beside a growing family drifts on contact, and this one
-- already had — it read `eight` at fourteen.)

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

-- ============================================================================
-- §11  The retype arm
-- ============================================================================

/-- **Cut C6g**: `.lifecycleRetype`'s footprint covers its writes.

The last arm, and the one whose two segments are read at the **pre**-state for a
reason no other arm has: the object the retype destroys is gone from the
post-state, so a post-state reading of either segment would name the empty set on
exactly the transition the segments exist for.  Both `lifecycleRetypeWriteSet`
and `lifecycleRetypeReplenishCores` therefore take `st`, which is what the
bracket needs anyway — it resolves a footprint before the transition runs.

Stated of the arm the syscall dispatches, `lifecycleRetypeDirectWithCleanup\
ShootdownPerCoreIcache`, rather than of the retype core: the two cached-structure
layers over it (the `.aside1` shootdown round with the initiator's own TLB drain,
and the domain-wide `IC IALLUIS`) each write kernel state, and a coverage claim
taken at the core would be a claim about a program the arm does not run.  Both
layers are scheduler-silent — `retypeInitiatorDrain_scheduler` and
`Architecture.withIcacheBroadcast_frame`'s third conjunct — so the exactness
frame descends through them without a case analysis of its own. -/
theorem schedLockSet_lifecycleRetypeOnCore_coversWrites (executingCore : CoreId)
    (authCap : Capability) (target : SeLe4n.ObjId) (newObj : KernelObject)
    (st st' : SystemState) (S : SchedLockSet)
    (hStep : lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache executingCore authCap
      target newObj st = .ok ((), st'))
    (hS : SchedLockSet.ofList? (schedLockSet_lifecycleRetypeOnCore st target) = some S) :
    schedFootprintCoversWrites S st st' :=
  schedFootprintCoversWrites_of_confined S (lifecycleRetypeWriteSet st target)
    (lifecycleRetypeReplenishCores st target) st st'
    (SchedLockSet.ofList?_pairs hS)
    (lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_confinedToCores executingCore
      authCap target newObj st st' hStep)
    (fun d hd => lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_replenishQueueOnCore_ne
      executingCore authCap target newObj st st' d hd hStep)

end SeLe4n.Kernel
