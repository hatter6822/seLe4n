/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under the GNU General Public License v3.0 or later.

WS-SM SM8.B — per-core non-interference at the *genuinely* cross-core
transitions.

`NonInterferencePerCore` proves `crossCoreNonInterference` and lifts the
thirty-five single-core operations, every one of which is confined to the boot
core. That leaves the theorem's interesting direction — a transition running on
core `c'` observed from a different core `c` — without an instantiation at a
transition that actually writes a remote core. This module supplies them.
-/


import SeLe4n.Kernel.InformationFlow.NonInterferencePerCore
import SeLe4n.Kernel.SlotConfinement
import SeLe4n.Kernel.IPC.Invariant.ReplyBindingPairFrame

/-!
# WS-SM SM8.B — non-interference at the cross-core transitions

WS-SM SM8 §3.3, sub-tasks SM8.B.2 / SM8.B.3.

## What this module adds that SM6 does not

The SM6 phases already prove per-core non-interference for their own cross-core
transitions — `endpointCallOnCore_call_path_NI_smp`,
`notificationSignalOnCore_signal_path_NI_smp`,
`endpointReplyOnCore_reply_path_NI_smp` and siblings.
Every one of those is **label-conditional on the per-core half**: they route
through `wakeThread_preserves_projectionOnCore`, whose `hHighThread` hypothesis
says the woken thread is *not observable*. Under that hypothesis the run-queue
insert is invisible because the filter drops it, on the woken thread's own core
as much as anywhere else.

`crossCoreNonInterference` says something different and strictly stronger for a
*remote* observer: waking a **fully visible** thread on core `c'` is invisible on
core `c ≠ c'`, because core `c`'s six observable slots did not move. No label
hypothesis is needed for the per-core half at all — only for the shared half,
which is what the object writes touch.

That is the practical SMP guarantee: a core learns nothing from scheduling
activity on another core, whatever the clearances of the threads involved.

## Where the write sets come from

Each theorem is `crossCoreNonInterference_ofCores` applied at a transition
that genuinely writes a remote core, with the per-core premise supplied by
that transition's `*_confinedToCores` theorem from the production
`SeLe4n.Kernel.SlotConfinement` modules: a write set computed from the
pre-state, proved sound (every core outside it is untouched), never tight.
The live arms' statements come first, in the order of the confinement
modules; §6 holds the below-API instantiations, §6b the data-carrying
declassification, §7 the coverage data.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)
open SeLe4n.Kernel.Lifecycle.Suspend
open SeLe4n.Kernel.PriorityInheritance

-- ============================================================================
-- §5 The live arms
-- ============================================================================

/-- SM8.B.2 (**the live `.call` non-interference**): the syscall arm the kernel
really runs on a cross-core `Call` is invisible to any core outside its write
set — receiver's home core, caller's own core, and the priority-inheritance
chain's home cores — with no hypothesis on the clearance of the caller, the
receiver, or any boosted server. -/
theorem endpointCallCrossCoreDispatch_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (payload : SendPayload)
    (executingCore : CoreId) (st : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hne : c ∉ endpointCallDispatchWriteSet endpointId caller payload
      executingCore st)
    (hShared : sharedViewUnchanged ctx observer st
      (endpointCallCrossCoreDispatch endpointId caller payload
        executingCore st).1) :
    projectStateOnCore ctx observer
        (endpointCallCrossCoreDispatch endpointId caller payload
          executingCore st).1 c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (endpointCallCrossCoreDispatch_confinedToCores endpointId caller payload
      executingCore st hObjInv)
    hShared

/-- SM8.B.2 (**the live `.reply` non-interference**): the syscall arm the kernel
really runs on a cross-core `Reply` is invisible to any core outside its write
set — the answered caller's home core, the recorded server's own core, and the
reverted priority-inheritance chain's home cores — with no hypothesis on the
clearance of the replier, the caller, or any chain member. -/
theorem endpointReplyCrossCoreDispatch_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hne : c ∉ endpointReplyDispatchWriteSet replier target msg executingCore st)
    (hShared : sharedViewUnchanged ctx observer st
      (endpointReplyCrossCoreDispatch replier target msg executingCore st).1) :
    projectStateOnCore ctx observer
        (endpointReplyCrossCoreDispatch replier target msg executingCore st).1 c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (endpointReplyCrossCoreDispatch_confinedToCores replier target msg executingCore st
      hObjInv)
    hShared

/-- SM8.B.2 (**the live `.replyRecv` non-interference**): the syscall arm the
kernel really runs on a cross-core `ReplyRecv` is invisible to any core outside
its write set, with no hypothesis on the clearance of the answered caller, the
rendezvousing sender, the recorded server or any chain member. -/
theorem endpointReplyRecvOnCore_crossCoreNonInterference (ctx : LabelingContext)
    {answer : Option Architecture.FaultReplyOutcome}
    (observer : IfObserver) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage) (grant : Bool)
    (executingCore : CoreId) (st st' : SystemState) (summary : CapTransferSummary) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReplyRecvAnsweringOnCore answer endpointId receiver replyId prevCaller msg grant executingCore st
      = .ok (summary, st'))
    (hne : c ∉ endpointReplyRecvAnsweringWriteSet answer endpointId receiver replyId prevCaller msg grant executingCore st)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (endpointReplyRecvOnCore_confinedToCores endpointId receiver replyId prevCaller msg grant executingCore st st' summary hObjInv hStep)
    hShared

/-- The `.replyRecv` arm's transition at the answer its caller's fault record
selects: a faulted caller's restart or abandon lands on the cores
`replyRecvTransferWriteSet` names, so it too is invisible outside them. -/
theorem replyRecvTransferOnCore_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId) (label : Nat) (msg : IpcMessage)
    (grant : Bool) (executingCore : CoreId) (st st' : SystemState) (summary : CapTransferSummary)
    (c : CoreId) (hObjInv : st.objects.invExt)
    (hStep : replyRecvTransferOnCore endpointId receiver replyId prevCaller label msg grant executingCore st = .ok (summary, st'))
    (hne : c ∉ replyRecvTransferWriteSet endpointId receiver replyId prevCaller label msg grant executingCore st)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  endpointReplyRecvOnCore_crossCoreNonInterference ctx observer endpointId receiver replyId
    prevCaller _ grant executingCore st st' summary c hObjInv hStep
    hne hShared

/-- SM8.B.2 (**the live `.tcbSuspend` non-interference**): the syscall arm the
kernel really runs on a cross-core `TCBSuspend` is invisible to any core outside
its write set, with no hypothesis on the clearance of the victim or of any
priority-inheritance chain member. -/
theorem suspendThreadOnCore_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (st st' : SystemState) (vtid : SeLe4n.ValidThreadId)
    (executingCore : CoreId) (sgi : Option (CoreId × Concurrency.SgiKind)) (c : CoreId)
    (hStep : suspendThreadOnCore st vtid executingCore = .ok (st', sgi))
    (hne : c ∉ suspendThreadOnCoreWriteSet st vtid executingCore)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (suspendThreadOnCore_confinedToCores st st' vtid executingCore sgi hStep)
    hShared

/-- SM8.B.2 (**the live `.tcbResume` non-interference**): resuming a thread onto
its home core is invisible to any core outside that set, with no hypothesis on
the resumed thread's clearance. -/
theorem resumeThreadOnCore_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (st st' : SystemState) (vtid : SeLe4n.ValidThreadId)
    (executingCore : CoreId) (sgi : Option (CoreId × Concurrency.SgiKind)) (c : CoreId)
    (hStep : Lifecycle.Suspend.resumeThreadOnCore st vtid executingCore = .ok (st', sgi))
    (hne : c ∉ resumeThreadOnCoreWriteSet st vtid executingCore)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (resumeThreadOnCore_confinedToCores st st' vtid executingCore sgi hStep)
    hShared

/-- SM8.B.2 (**the live unchecked `.send` non-interference**): a cross-core send is
invisible on every core outside `endpointSendWriteSet`, with no hypothesis on the
clearance of the sender or of the woken receiver. -/
theorem endpointSendDualWithCapsOnCore_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (payload : SendPayload)
    (executingCore : CoreId) (st : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hne : c ∉ endpointSendWriteSet st endpointId executingCore)
    (hShared : sharedViewUnchanged ctx observer st
      (endpointSendDualWithCapsOnCore endpointId sender payload
        executingCore st).1) :
    projectStateOnCore ctx observer
        (endpointSendDualWithCapsOnCore endpointId sender payload
          executingCore st).1 c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (endpointSendDualWithCapsOnCore_confinedToCores endpointId sender payload
      executingCore st hObjInv)
    hShared

/-- SM8.B.2 (**the live checked `.send` non-interference**). -/
theorem endpointSendCrossCoreDispatchChecked_crossCoreNonInterference
    (ctx : LabelingContext) (observer : IfObserver) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (payload : SendPayload)
    (executingCore : CoreId) (st : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hne : c ∉ endpointSendWriteSet st endpointId executingCore)
    (hShared : sharedViewUnchanged ctx observer st
      (endpointSendCrossCoreDispatchChecked ctx endpointId sender payload
        executingCore st).1) :
    projectStateOnCore ctx observer
        (endpointSendCrossCoreDispatchChecked ctx endpointId sender payload
          executingCore st).1 c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (endpointSendCrossCoreDispatchChecked_confinedToCores ctx endpointId sender payload
      executingCore st hObjInv)
    hShared

/-- SM8.B.2 (**the live `.schedContextUnbind` non-interference**): unbinding is
invisible on every core outside the subject's home core and the core running
it, with no hypothesis on the subject's clearance. -/
theorem schedContextUnbind_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (vScId : SeLe4n.ValidObjId) (st st' : SystemState) (c : CoreId)
    (hStep : SchedContextOps.schedContextUnbind vScId st = .ok ((), st'))
    (hne : c ∉ schedContextUnbindWriteSet st vScId.val)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (schedContextUnbind_confinedToCores vScId st st' hStep) hShared

/-- SM8.B.2 (**the live `.tcbSetAffinity` non-interference**): a migration is
invisible on every core outside the pair it moves the thread between, with no
hypothesis on that thread's clearance.

The strongest of the cross-core instantiations in the sense that matters here:
the operation genuinely writes *two* remote cores, and the bound is exact — a
core that is neither the old home nor the new one sees nothing. -/
theorem setThreadCpuAffinityWithMigration_crossCoreNonInterference
    (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (targetTid : SeLe4n.ThreadId)
    (affinity : Option CoreId) (executingCore : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind)) (c : CoreId)
    (hInv : st.objects.invExt)
    (hStep : setThreadCpuAffinityWithMigration st targetTid affinity executingCore
      = .ok (st', sgi))
    (hne : c ∉ setThreadCpuAffinityWriteSet st targetTid affinity)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (setThreadCpuAffinityWithMigration_confinedToCores st st' targetTid affinity
      executingCore sgi hInv hStep) hShared

/-- SM8.B.2 (**the live `.schedContextBind` non-interference**): binding is
invisible on every core outside the bound thread's home core, with no hypothesis
on that thread's clearance. -/
theorem schedContextBind_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (vScId : SeLe4n.ValidObjId) (vThreadId : SeLe4n.ValidThreadId)
    (st st' : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hStep : SchedContextOps.schedContextBind vScId vThreadId st = .ok ((), st'))
    (hne : c ∉ schedContextBindWriteSet st vThreadId.val)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (schedContextBind_confinedToCores vScId vThreadId st st' hObjInv hStep) hShared

/-- SM8.B.2 (**the `.schedContextConfigure` transition's non-interference**): a
configure is invisible on every core outside its subject's home core and the
cores of the inheritance chain it re-walks. -/
theorem schedContextConfigure_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (vScId : SeLe4n.ValidObjId)
    (budget period : Nat) (extraRefills badge flags : UInt64) (st st' : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hStep : SchedContextOps.schedContextConfigure vScId budget period extraRefills badge flags st
      = .ok ((), st'))
    (hne : c ∉ schedContextConfigureWriteSet st vScId.val)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (schedContextConfigure_confinedToCores vScId budget period extraRefills badge flags
      st st' hObjInv hStep) hShared

/-- WS-ZA ZA6.4 (**the live `.schedContextConfigure` non-interference**): a
configure through core `core`'s control is invisible on every core outside the
configure's write set and, on a move, the bound thread's old home and the
control's core (`schedControlConfigureWriteSet`). -/
theorem schedControlConfigure_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (core : CoreId) (vScId : SeLe4n.ValidObjId)
    (budget period : Nat) (extraRefills badge flags : UInt64) (st st' : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hStep : SchedContextOps.schedControlConfigure core vScId budget period extraRefills badge flags
       st = .ok ((), st'))
    (hne : c ∉ schedControlConfigureWriteSet st core vScId.val)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (schedControlConfigure_confinedToCores core vScId budget period extraRefills badge flags
      st st' hObjInv hStep) hShared

/-- SM8.B.3 (**the live `.schedContextUnbind` arm, cross-core**): an unbind is
invisible on every core outside its write set — including the core the demoted
thread was running on, when that is not the observer's.  The arm is seL4-MCS's
`SchedContext_Unbind`: the thread unbind, then the notification unbind and the
reply-stack unlink, which write no core's slot. -/
theorem schedContextUnbindAllOnCore_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (vScId : SeLe4n.ValidObjId) (executingCore : CoreId)
    (st st' : SystemState) (c : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (hStep : SchedContextOps.schedContextUnbindAllOnCore vScId executingCore st
      = .ok (st', sgi))
    (hne : c ∉ schedContextUnbindWriteSet st vScId.val)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (schedContextUnbindAllOnCore_confinedToCores vScId executingCore st st' sgi hStep) hShared

/-- WS-SX SX8.3 (**the live `.schedContextUnbindObject` arm, cross-core**): the
thread path is invisible on every core outside the thread unbind's write set;
the notification path writes no core
(`schedContextUnbindNotificationObject_confinedToCores`). -/
theorem schedContextUnbindThreadObjectOnCore_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (vScId : SeLe4n.ValidObjId) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) (st st' : SystemState) (c : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (hStep : SchedContextOps.schedContextUnbindThreadObjectOnCore vScId tid executingCore st
      = .ok (st', sgi))
    (hne : c ∉ schedContextUnbindWriteSet st vScId.val)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (schedContextUnbindThreadObjectOnCore_confinedToCores vScId tid executingCore st st' sgi hStep)
    hShared

/-- SM8.B.3 (**the live `.tcbSetPriority` arm, cross-core**): a priority change is
invisible on every core outside the target's home and the executing core. -/
theorem setPriorityOnCore_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (st st' : SystemState)
    (vCallerTid vTargetTid : SeLe4n.ValidThreadId) (newPriority : SeLe4n.Priority)
    (executingCore c : CoreId) (sgi : Option (CoreId × Concurrency.SgiKind))
    (hObjInv : st.objects.invExt)
    (hStep : SchedContext.PriorityManagement.setPriorityOnCore st vCallerTid vTargetTid
      newPriority executingCore = .ok (st', sgi))
    (hne : c ∉ priorityControlWriteSet st vTargetTid.val executingCore)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (setPriorityOnCore_confinedToCores st st' vCallerTid vTargetTid newPriority
      executingCore sgi hObjInv hStep) hShared

/-- SM8.B.3 (**the live `.tcbSetMCPriority` arm, cross-core**): a ceiling change is
invisible on every core outside the target's home and the executing core. -/
theorem setMCPriorityOnCore_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (st st' : SystemState)
    (vCallerTid vTargetTid : SeLe4n.ValidThreadId) (newMCP : SeLe4n.Priority)
    (executingCore c : CoreId) (sgi : Option (CoreId × Concurrency.SgiKind))
    (hObjInv : st.objects.invExt)
    (hStep : SchedContext.PriorityManagement.setMCPriorityOnCore st vCallerTid vTargetTid
      newMCP executingCore = .ok (st', sgi))
    (hne : c ∉ priorityControlWriteSet st vTargetTid.val executingCore)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (setMCPriorityOnCore_confinedToCores st st' vCallerTid vTargetTid newMCP
      executingCore sgi hObjInv hStep) hShared

/-- SM8.B.3 (**the live `.vspaceMap` arm, cross-core**): a map is invisible on
every core. -/
theorem vspaceMapPageCheckedWithShootdownFromStatePerCore_crossCoreNonInterference
    (ctx : LabelingContext) (observer : IfObserver) (executingCore : CoreId)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (perms : PagePermissions) (st st' : SystemState) (c : CoreId)
    (hStep : Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore executingCore
      asid vaddr paddr perms st = .ok ((), st'))
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer (by simp)
    (vspaceMapPageCheckedWithShootdownFromStatePerCore_confinedToCores executingCore asid
      vaddr paddr perms st st' hStep) hShared

/-- **WS-BP BP7.1**: the live `.vspaceMap` arm, cross-core — a frame mapping, or
a remap of the address the frame capability records (the unmap of that address
followed by the fresh mapping), is invisible on every core, stated at the
definition the arm runs. -/
theorem vspaceMapOrRemapFromFrameCap_crossCoreNonInterference
    (ctx : LabelingContext) (observer : IfObserver)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (args : Architecture.SyscallArgDecode.VSpaceMapArgs) (st st' : SystemState) (c : CoreId)
    (hStep : vspaceMapOrRemapFromFrameCap tid executingCore args st = .ok ((), st'))
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer (by simp)
    (vspaceMapOrRemapFromFrameCap_confinedToCores tid executingCore args st st' hStep) hShared

/-- SM8.B.3 (**the live `.vspaceUnmap` arm, cross-core**): an unmap is invisible
on **every** core — the strongest form of the cross-core statement, and the
reason this arm needs no exception. -/
theorem vspaceUnmapPageWithShootdownAndIcacheBroadcast_crossCoreNonInterference
    (ctx : LabelingContext) (observer : IfObserver) (executingCore : CoreId)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (st st' : SystemState) (c : CoreId)
    (hStep : Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast executingCore
      asid vaddr st = .ok ((), st'))
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer (by simp)
    (vspaceUnmapPageWithShootdownAndIcacheBroadcast_confinedToCores executingCore asid vaddr
      st st' hStep) hShared

/-- WS-BP BP7.1 (`v0.36.7`), WS-ZA ZA5.4 part 23 (**the live `.cspaceDelete`
arm, cross-core**): a finalising delete is invisible on every core outside
`cspaceDeleteSlotFinalisingCores` — on every core when it destroys no final
capability or one naming an object whose destroy writes no core, since only the
finalisation of the kinds `finalObjectWritesCores` names wakes, suspends or
unbinds threads on their own cores. -/
theorem cspaceDeleteSlotFinalising_crossCoreNonInterference
    (ctx : LabelingContext) (observer : IfObserver) (executingCore : CoreId)
    (addr : CSpaceAddr) (st st' : SystemState) (c : CoreId)
    (hInv : st.objects.invExt)
    (hStep : cspaceDeleteSlotFinalising executingCore addr st = .ok ((), st'))
    (hne : c ∉ cspaceDeleteSlotFinalisingCores st addr)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (cspaceDeleteSlotFinalising_confinedToCores executingCore addr st st' hInv hStep) hShared

/-- WS-ZA ZA5.4 part 26 (**the live `.cspaceDelete` arm, the zombie delete,
cross-core**): invisible on every core outside `cspaceDeleteSlotFinalisingCores`
(`cspaceDeleteSlotZombie_confinedToCores`). -/
theorem cspaceDeleteSlotZombie_crossCoreNonInterference
    (ctx : LabelingContext) (observer : IfObserver) (executingCore : CoreId)
    (addr : CSpaceAddr) (st st' : SystemState) (c : CoreId)
    (hInv : st.objects.invExt)
    (hStep : cspaceDeleteSlotZombie executingCore addr st = .ok ((), st'))
    (hne : c ∉ cspaceDeleteSlotFinalisingCores st addr)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (cspaceDeleteSlotZombie_confinedToCores executingCore addr st st' hInv hStep) hShared

/-- WS-BP BP7.1 (`v0.36.7`), WS-ZA ZA5.4 part 23 (**the live `.cspaceRevoke`
arm, cross-core**): each delete of a finalising revocation may wake the waiters
of an endpoint or notification whose final capability it destroys, on their
own cores, so the revocation declares every core
(`cspaceRevokeCdtFinalising_confinedToCores`); outside it, it is invisible. -/
theorem cspaceRevokeCdtFinalising_crossCoreNonInterference
    (ctx : LabelingContext) (observer : IfObserver) (executingCore : CoreId)
    (addr : CSpaceAddr) (st st' : SystemState) (c : CoreId)
    (hStep : cspaceRevokeCdtFinalising executingCore addr st = .ok ((), st'))
    (hne : c ∉ Concurrency.allCores)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (cspaceRevokeCdtFinalising_confinedToCores executingCore addr st st' hStep) hShared

/-- WS-ZA ZA5.4 part 14 (**the live `.untypedRetype` arm, cross-core**): the
carve — every kernel object is made this way — is invisible on every core.  It
takes the executing core only to read the domain a carved thread starts in, and
writes the object store and the CDT alone, once per object of its window. -/
theorem untypedRetypeFromCap_crossCoreNonInterference
    (ctx : LabelingContext) (observer : IfObserver) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) (srcAddr : SeLe4n.CPtr) (root? : Option SeLe4n.CPtr)
    (args? : Except KernelError Architecture.SyscallArgDecode.UntypedRetypeArgs)
    (st st' : SystemState) (c : CoreId) (hInv : st.objects.invExt)
    (hStep : untypedRetypeFromCap tid executingCore srcAddr root? args? st = .ok ((), st'))
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c := by
  have hConf : observableSlotsConfinedToCores st st' [] :=
    (untypedRetypeFromCap_chain hStep).rel (P := fun s => s.objects.invExt)
      (R := fun a b => observableSlotsConfinedToCores a b [])
      (fun s => observableSlotsConfinedToCores_refl s [])
      (fun h1 h2 => observableSlotsConfinedToCores_trans h1 h2)
      (fun hP hC => untypedRetypeObject_preserves_objects_invExt hP hC)
      (fun hP hC => untypedRetypeObject_confinedToCores _ _ _ _ _ _ hP hC) hInv
  exact crossCoreNonInterference_ofCores ctx observer (by simp) hConf hShared

/-- WS-ZA ZA5.4 part 26 (**the live `.tcbSetSpace` arm, through the zombie
delete, cross-core**): invisible on every core outside
`copyThreadSpacesZombieCores` — every core when the old CSpace root is the last
capability to a CNode holding capabilities, whose zombie loop may wake waiters
on their own cores (`copyThreadSpacesZombie_confinedToCores`). -/
theorem copyThreadSpacesZombie_crossCoreNonInterference
    (ctx : LabelingContext) (observer : IfObserver) (executingCore : CoreId)
    (vtid : SeLe4n.ValidThreadId) (cnSrc vrSrc : CSpaceAddr) (cnData : UInt64) (fhSrc : CSpaceAddr)
    (st st' : SystemState) (c : CoreId) (hInv : st.objects.invExt)
    (hStep : copyThreadSpacesZombie executingCore st vtid cnSrc vrSrc cnData fhSrc = .ok st')
    (hne : c ∉ copyThreadSpacesZombieCores st vtid)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (copyThreadSpacesZombie_confinedToCores executingCore st st' vtid cnSrc vrSrc cnData fhSrc hInv
      hStep) hShared

/-- WS-SX SX6.6 (**the live `.tcbSetIPCBuffer` arm, cross-core**): invisible
on every core — the buffer slot's set and the address write touch the object
store and the CDT alone (`setIPCBufferOp_confinedToCores`). -/
theorem setIPCBufferOp_crossCoreNonInterference
    (ctx : LabelingContext) (observer : IfObserver) (executingCore : CoreId)
    (vtid : SeLe4n.ValidThreadId) (callerTid : SeLe4n.ThreadId) (bufferCap? : Option SeLe4n.CPtr)
    (addr : SeLe4n.VAddr) (st st' : SystemState) (c : CoreId)
    (hStep : Architecture.IpcBufferValidation.setIPCBufferOp executingCore st vtid callerTid
      bufferCap? addr = .ok st')
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer (by simp)
    (setIPCBufferOp_confinedToCores executingCore st st' vtid callerTid bufferCap? addr hStep) hShared

/-- WS-ZA ZA6.32: **the bind's copy writes no core** — the node slot's capability
and its derivation edge are the object store and the CDT. -/
theorem cspaceCopy_confinedToCores {src dst : CSpaceAddr} {mask : AccessRightSet} {st st' : SystemState}
    (hStep : cspaceCopy src dst mask st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' [] := by
  obtain ⟨cap, st2, -, -, hIns, -, rfl⟩ := cspaceCopy_ok_decompose hStep
  exact observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (by rw [untypedSourceSetFull_scheduler, SystemState.cdtAddChild_scheduler,
      cspaceInsertSlot_preserves_scheduler st st2 dst _ hIns])
    (by rw [untypedSourceSetFull_machine, SystemState.cdtAddChild_machine,
      cspaceInsertSlot_preserves_machine st st2 dst _ hIns])

/-- WS-ZA ZA6.32 (**the live `.irqHandlerClear` arm, cross-core**): the clear is
the node slot's zombie delete, so it is invisible on every core outside
`cspaceDeleteSlotFinalisingCores` of that slot — every core when the slot holds
the last capability to a notification whose finalisation wakes waiters. -/
theorem irqHandlerClear_crossCoreNonInterference
    (ctx : LabelingContext) (observer : IfObserver) (executingCore : CoreId)
    (line : Nat) (st st' : SystemState) (c : CoreId)
    (hInv : st.objects.invExt)
    (hStep : irqHandlerClear executingCore line st = .ok ((), st'))
    (hne : c ∉ cspaceDeleteSlotFinalisingCores st (irqNodeAddr line))
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  cspaceDeleteSlotZombie_crossCoreNonInterference ctx observer executingCore _ st st' c hInv
    (irqHandlerClear_ok hStep).2 hne hShared

/-- WS-ZA ZA6.32 (**the live `.irqHandlerSetNotification` arm, cross-core**): the
bind is the node slot's zombie delete then the copy into it, and the copy writes
no core (`cspaceCopy_confinedToCores`), so the bind is invisible on every core
outside the delete's `cspaceDeleteSlotFinalisingCores`. -/
theorem irqHandlerSetNotificationFromCap_crossCoreNonInterference
    (ctx : LabelingContext) (observer : IfObserver) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) (line : Nat)
    (args? : Except KernelError Architecture.SyscallArgDecode.IrqHandlerSetNotificationArgs)
    (st st' : SystemState)
    (c : CoreId) (hInv : st.objects.invExt)
    (hStep : irqHandlerSetNotificationFromCap tid executingCore line args? st = .ok ((), st'))
    (hne : c ∉ cspaceDeleteSlotFinalisingCores st (irqNodeAddr line))
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c := by
  obtain ⟨_, _, -, hB⟩ := irqHandlerSetNotificationFromCap_ok tid executingCore line args? st st' hStep
  obtain ⟨_, st1, -, -, -, hZ, hC⟩ := irqHandlerSetNotification_ok_cases hB
  have hK : observableSlotsConfinedToCores st1 st' [] := by
    rcases hC with hC | rfl
    · exact cspaceCopy_confinedToCores hC
    · exact observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
        (cspaceCopyPerform_scheduler _ _ _ _) (cspaceCopyPerform_machine _ _ _ _)
  exact crossCoreNonInterference_ofCores ctx observer
    (by simpa using hne)
    (observableSlotsConfinedToCores_trans
      (cspaceDeleteSlotZombie_confinedToCores executingCore _ st st1 hInv hZ) hK) hShared

-- ============================================================================
-- §6 The non-interference instantiations
-- ============================================================================
--
-- Each of these is `crossCoreNonInterference_ofCores` applied at a transition
-- that genuinely writes a remote core, so `c'` here is a real other core rather
-- than `bootCoreId`. Read the hypotheses: `hne` is membership in a write set
-- computed from the pre-state, and `hShared` is the object-level premise.
-- **There is no hypothesis about the labels of the threads being woken or
-- descheduled** — that is the content.

/-- SM8.B.2 (SM6.B): a cross-core notification signal is invisible to any core
that is not the woken waiter's home core, given only that the shared half is
unchanged. -/
theorem notificationSignalOnCore_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (executingCore : CoreId) (st : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hne : c ∉ notificationSignalWriteSet st notificationId)
    (hShared : sharedViewUnchanged ctx observer st
      (notificationSignalOnCore notificationId badge executingCore st).1) :
    projectStateOnCore ctx observer
        (notificationSignalOnCore notificationId badge executingCore st).1 c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (notificationSignalOnCore_confinedToCores notificationId badge executingCore st hObjInv)
    hShared

/-- SM8.B.2 (SM6.B): a notification wait is invisible to every core but the
caller's own — **unconditionally on the per-core side**, and with the shared
half as the only premise. -/
theorem notificationWaitOnCore_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (executingCore : CoreId) (st : SystemState) (c : CoreId)
    (hne : c ≠ executingCore)
    (hShared : sharedViewUnchanged ctx observer st
      (notificationWaitOnCore notificationId waiter executingCore st).1) :
    projectStateOnCore ctx observer
        (notificationWaitOnCore notificationId waiter executingCore st).1 c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer (by simpa using hne)
    (notificationWaitOnCore_confinedToCores notificationId waiter executingCore st) hShared

/-- WS-ZA ZA4.3 (**the live `.yield` arm, cross-core**): a yield is invisible to
every core but the caller's own — unconditionally on the per-core side, with
the shared half as the only premise. -/
theorem yieldOnCore_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (executingCore c : CoreId) (st st' : SystemState)
    (hStep : yieldOnCore st executingCore = .ok st')
    (hne : c ≠ executingCore)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer (by simpa using hne)
    (yieldOnCore_confinedToCores st st' executingCore hStep) hShared

/-- WS-ZA ZA6.9 (**the live `.schedContextConsumed` arm, cross-core**): the
Consumed invocation is invisible to every core — it writes no per-core slot —
with the shared half as the only premise. -/
theorem schedContextConsumedOnCore_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (s : SeLe4n.SchedContextId) (executingCore c : CoreId)
    (st st' : SystemState)
    (hStep : schedContextConsumedOnCore s executingCore st = .ok st')
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer (by simp)
    (schedContextConsumedOnCore_confinedToCores s executingCore st st' hStep) hShared

/-- WS-ZA ZA6.29 (**the live `.schedContextYieldTo` arm, cross-core**): the
yieldTo invocation is invisible on every core outside its write set — the
executing core and the bound thread's home core, where the resume places the
context and the unlinked branch re-queues the thread at its band's head — with
the shared half as the only premise. -/
theorem schedContextYieldToOnCore_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (scObjId : SeLe4n.ObjId) (executingCore c : CoreId)
    (st st' : SystemState) (hInv : st.objects.invExt)
    (hStep : SchedContextOps.schedContextYieldToOnCore (SeLe4n.SchedContextId.ofObjId scObjId)
      executingCore st = .ok st')
    (hne : c ∉ schedContextYieldToWriteSet st scObjId executingCore)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (schedContextYieldToOnCore_confinedToCores scObjId executingCore st st' hInv hStep) hShared

/-- SM8.B.2 (SM6.A, **the two-core case**): a cross-core endpoint call is
invisible to any core that is neither the receiver's home core nor the caller's
own core. -/
theorem endpointCallOnCore_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (payload : SendPayload) (executingCore : CoreId) (st : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hne : c ∉ endpointCallWriteSet st endpointId executingCore)
    (hShared : sharedViewUnchanged ctx observer st
      (endpointCallOnCore endpointId caller payload executingCore st).1) :
    projectStateOnCore ctx observer
        (endpointCallOnCore endpointId caller payload executingCore st).1 c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (endpointCallOnCore_confinedToCores endpointId caller payload executingCore st hObjInv)
    hShared

/-- SM8.B.2 (SM6.C): a cross-core reply is invisible to any core that is not the
answered caller's home core. -/
theorem endpointReplyOnCore_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hne : c ≠ determineTargetCore st target)
    (hShared : sharedViewUnchanged ctx observer st
      (endpointReplyOnCore replier target msg executingCore st).1) :
    projectStateOnCore ctx observer
        (endpointReplyOnCore replier target msg executingCore st).1 c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer (by simpa using hne)
    (endpointReplyOnCore_confinedToCores replier target msg executingCore st hObjInv) hShared

/-- SM8.B.2 (SM6.C): a cross-core **receive** — the `replyRecv` receive leg — is
invisible to any core outside its write set: the woken sender's home core on a
rendezvous, the receiver's own core when it blocks. -/
theorem endpointReceiveDualOnCore_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) (executingCore : CoreId) (st : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hne : c ∉ endpointReceiveDualWriteSet st endpointId executingCore)
    (hShared : sharedViewUnchanged ctx observer st
      (endpointReceiveDualOnCore endpointId receiver replyId executingCore st).1) :
    projectStateOnCore ctx observer
        (endpointReceiveDualOnCore endpointId receiver replyId executingCore st).1 c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (endpointReceiveDualOnCore_confinedToCores endpointId receiver replyId executingCore st
      hObjInv)
    hShared

/-- **The receive with seL4-MCS `receiveIPC`'s return before its leg**: the
return writes no observable slot of any core
(`receiveReturnSchedContext_confinedToCores`), so the receive is invisible to
any core outside its leg's write set, read on the state the return leaves.
The frame the live `.receive` arm's leg runs on (`receiveLegState`), and, with
`blocks := true`, the frame `.replyRecv`'s receive leg runs on: the inventory's
`.endpointReceiveDualWithCaps` entry names it, because a live entry names the
function the dispatch calls (SM8.B.2, PR #873 round 7) and since WS-SX SX8.2 both
receive-shaped arms run the return before `endpointReceiveDualWithCapsOnCore`. -/
theorem receiveWithReturn_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) (executingCore : CoreId) (blocks : Bool)
    (st : SystemState) (c : CoreId) (hObjInv : st.objects.invExt)
    (hne : c ∉ endpointReceiveDualWriteSet (receiveReturnSchedContext blocks st receiver)
      endpointId executingCore)
    (hShared : sharedViewUnchanged ctx observer st
      (endpointReceiveDualWithCapsOnCore endpointId receiver replyId executingCore
        (receiveReturnSchedContext blocks st receiver)).1) :
    projectStateOnCore ctx observer
        (endpointReceiveDualWithCapsOnCore endpointId receiver replyId executingCore
          (receiveReturnSchedContext blocks st receiver)).1 c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer (cs := [] ++ _)
    (by simpa only [List.nil_append] using hne)
    (observableSlotsConfinedToCores_trans
      (receiveReturnSchedContext_confinedToCores blocks st receiver)
      (endpointReceiveDualWithCapsOnCore_confinedToCores endpointId receiver replyId executingCore
        _ (receiveReturnSchedContext_objects_invExt blocks st receiver hObjInv)))
    hShared

/-- SM8.B.2 (SM6.B, **the live `.signal` bound-delivery arm**): a bound-aware
signal is invisible to any core that is neither the bound TCB's home core (when
the badge is delivered directly) nor the plain signal's waiter home core. -/
theorem notificationSignalBoundOnCore_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (executingCore : CoreId) (st : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hne : c ∉ notificationSignalBoundWriteSet st notificationId)
    (hShared : sharedViewUnchanged ctx observer st
      (notificationSignalBoundOnCore notificationId badge executingCore st).1) :
    projectStateOnCore ctx observer
        (notificationSignalBoundOnCore notificationId badge executingCore st).1 c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (notificationSignalBoundOnCore_confinedToCores notificationId badge executingCore st hObjInv)
    hShared

/-- SM8.B.2 (SM6.E), re-keyed at WS-RR RR8.6: a cross-core deschedule is
invisible to any core that is not the one the state places the victim on. -/
theorem descheduleThread_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (tid : SeLe4n.ThreadId) (executingCore : CoreId)
    (st : SystemState) (c : CoreId)
    (hne : c ∉ descheduleAtPlacementCores st tid)
    (hShared : sharedViewUnchanged ctx observer st (descheduleThread st tid executingCore).1) :
    projectStateOnCore ctx observer (descheduleThread st tid executingCore).1 c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (descheduleThread_confinedToCores st tid executingCore) hShared

/-- SM8.B.2 (SM6.E, composed), re-keyed at WS-RR RR8.6 and `v0.35.158`: a
cross-core IPC-blocking cancellation is invisible to any core that is neither
the one the pre-state places the victim on nor the one the reclaim's holder
deschedule writes. -/
theorem cancelIpcBlockingOnCore_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (victim : SeLe4n.ThreadId) (tcb : TCB)
    (executingCore : CoreId) (st : SystemState) (c : CoreId) (hInv : st.objects.invExt)
    (hne : c ∉ descheduleAtPlacementCores st victim)
    (hHolder : cancelUnboundHolderCore? st (cancelIpcBlockingMigrated victim tcb st)
      victim tcb ≠ some c)
    (hShared : sharedViewUnchanged ctx observer st
      (cancelIpcBlockingOnCore victim tcb executingCore st).1) :
    projectStateOnCore ctx observer
        (cancelIpcBlockingOnCore victim tcb executingCore st).1 c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer
    (by
      -- `v0.35.158`: `c` is neither the victim's placed core nor the core the
      -- reclaim's holder deschedule writes.
      intro hMem
      rcases List.mem_append.mp hMem with hw | hd
      · cases hW : cancelUnboundHolderCore? st (cancelIpcBlockingMigrated victim tcb st)
            victim tcb with
        | none => rw [hW] at hw; simp at hw
        | some w =>
          rw [hW] at hw
          simp only [Option.toList, List.mem_singleton] at hw
          exact hHolder (by rw [hw, hW])
      · exact hne hd)
    (cancelIpcBlockingOnCore_confinedToCores victim tcb executingCore st hInv) hShared

/-- SM8.B.2 (**the headline, and the thing SM6 cannot say**): waking a thread on
a remote core is invisible to a third core *whatever that thread's label*.

`wakeThread_preserves_projectionOnCore` (SM6.A) proves a wake invisible on
**every** core, but only under `hHighThread` — the woken thread must be outside
the observer's view, so the run-queue insert is dropped by the filter. Here the
woken thread may be **fully visible** to the observer: the wake is still
invisible on core `c`, because the insert lands in a different core's run queue
and core `c`'s six slots are untouched.

The object write (`enqueueRunnableOnCore` sets the woken TCB `.ready`) still has
to be accounted for, which is what `hShared` does — and that is the honest
division of labour: labels govern the *shared* half, core identity governs the
*per-core* half. -/
theorem wakeThread_crossCoreNonInterference_of_visible_thread (ctx : LabelingContext)
    (observer : IfObserver) (tid : SeLe4n.ThreadId) (executingCore : CoreId)
    (st : SystemState) (c : CoreId)
    (hne : c ≠ determineTargetCore st tid)
    (hShared : sharedViewUnchanged ctx observer st (wakeThread st tid executingCore).1) :
    projectStateOnCore ctx observer (wakeThread st tid executingCore).1 c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer (by simpa using hne)
    (wakeThread_confinedToCores st tid executingCore) hShared

-- ============================================================================
-- §6b WS-SM SM9.C.5 / SM9.C.6 — the data-carrying declassification
-- ============================================================================

/-! ## The authorized effect footprint, and what it does **not** say

WS-SM SM9.C is the tree's first deliberately *visible* flow: every other
transition in this module is proven invisible to observers, and this one is
proven to make a difference the observer may see — bounded, and recorded.

That changes what a bound has to be. For an invisible transition a write set is
a *safety* statement ("nothing outside this moved"). Here it is that **and** a
scope statement: it says which parts of the state the syscall is permitted to
change, so an auditor can check that a downgrade the policy authorized landed
where the policy expected it to land and nowhere else.

The distinction the sub-phase turns on, and the one
`footprint_receiver_at_notification_label` below makes a theorem rather than a
remark: **naming a sink in the footprint says where writes land, not that they
are permitted.** The footprint is computed from the *state* — which
notification, which receiver, which home core — and consults no policy at all.
The caller's hop is a separate policy decision, and the receiver is admissible
for a reason outside the footprint: the two-way wait and bind gates and the
boot's label check put only threads of the notification's own label there.
Conflating the two would be exactly the SM6.B badge-leak class one abstraction
up: "the delivery targets this TCB" read as "the delivery to this TCB is
allowed". -/

/-- WS-SM SM9.C.5: **the authorized effect footprint of a declassifying signal.**

Three components, because a data-carrying declassification touches three kinds
of thing and an auditor needs all three:

* `notification` — the object the badge is written into. Always present: it is
  the capability's own target.
* `receiver` — the thread the badge is delivered onward to, resolved from the
  *pre-state* by `declassifiedSignalReceiver?` (the bound TCB, else the head
  waiter). `none` when the signal only accumulates a badge with nobody to
  deliver it to.
* `cores` — the scheduler slots and register banks the delivery may write,
  which is the live signal's own `sendSignalWriteSet`: SM6.B's
  `notificationSignalBoundWriteSet` and, since WS-SX SX8.2, the home core of
  the thread the notification's context is donated to. Sharing that
  definition rather than restating it is deliberate: the dispatch *is* the
  ordinary bound signal plus a trail append
  (`notificationSignalDeclassifiedOnCore_frame`) plus seL4's donation, so a
  footprint naming different cores than the signal's write set would be
  describing a transition the kernel does not run.

The audit trail is **not** a component. It is written on every authorized
downgrade, and it is deliberately outside `ObservableState` — so it is not part
of what the footprint bounds for an observer, and the property that covers it is
recording (`declassifiedSignal_never_unaudited`), not confinement. -/
structure DeclassificationEffectFootprint where
  /-- The notification object the badge is written into. -/
  notification : SeLe4n.ObjId
  /-- The thread the badge is delivered onward to, if any. -/
  receiver : Option SeLe4n.ThreadId
  /-- The cores whose scheduler slots and register banks the delivery may
  write. -/
  cores : List CoreId
  deriving Repr

/-- WS-SM SM9.C.5: the footprint of a declassifying signal, computed from the
pre-state alone.

**Takes no `DeclassificationPolicy` and no `LabelingContext`**: the footprint
cannot carry an authorization, because it reads nothing an authorization is
decided from. -/
def declassifiedSignalEffectFootprint (st : SystemState) (notificationId : SeLe4n.ObjId) :
    DeclassificationEffectFootprint :=
  { notification := notificationId
    receiver := declassifiedSignalReceiver? st notificationId
    cores := sendSignalWriteSet st notificationId }

/-- WS-SM SM9.C.5: the footprint's receiver is the transition's own pre-state
resolution — the same function the delivery and the label theorem below read.

Load-bearing rather than a restatement: the two must name the same thread, or a
footprint could bound the writes to one TCB while the label fact held of
another. That is the confused-deputy shape one level up from the v0.32.97
capability-target finding, and this is where it is excluded. -/
@[simp] theorem declassifiedSignalEffectFootprint_receiver (st : SystemState)
    (notificationId : SeLe4n.ObjId) :
    (declassifiedSignalEffectFootprint st notificationId).receiver =
      declassifiedSignalReceiver? st notificationId := rfl

/-- WS-SM SM9.C.5: the footprint's cores are the live signal's write set, so
the information-flow bound and the delivery's own scheduling effects cannot name
different cores. -/
@[simp] theorem declassifiedSignalEffectFootprint_cores (st : SystemState)
    (notificationId : SeLe4n.ObjId) :
    (declassifiedSignalEffectFootprint st notificationId).cores =
      sendSignalWriteSet st notificationId := rfl

/-- WS-SM SM9.C.6 (**the footprint's receiver is admissible by label, not by
being named**): on a state whose notification labels agree (the agreement every
kernel entry carries, WS-SX SX21), a receiver inside the
authorized effect footprint carries the notification's own domain, so the
delivery to it is the identity flow and owes no authorization.

The footprint says *where* the writes land and carries no authorization: what
makes the receiver admissible is that the checked wait and bind admit a thread
to a notification only at its label (`notificationFlowGate`) and the boot
refuses a configuration that does otherwise (`notificationLabelsCoherent`).  A
reader who took the footprint itself as the permission would have nothing to
point at on a state where those gates had been bypassed — which is why the
coherence is this theorem's hypothesis rather than its conclusion. -/
theorem footprint_receiver_at_notification_label (ctx : LabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hAgree : notificationLabelsAgree ctx st)
    (hIn : (declassifiedSignalEffectFootprint st notificationId).receiver = some receiver) :
    (liftLegacyContext ctx).objectDomainOf notificationId =
        (liftLegacyContext ctx).threadDomainOf receiver ∧
      declassifiedSignalHopAuthorization (liftLegacyContext ctx) declPolicy
        ((liftLegacyContext ctx).objectDomainOf notificationId)
        ((liftLegacyContext ctx).threadDomainOf receiver) = .ok .ordinary :=
  declassifiedSignalReceiver_flow_ordinary_of_coherent ctx declPolicy st notificationId receiver
    hAgree (by simpa using hIn)

/-- WS-SM SM9.C.6: and the converse half — **authorization does not widen the
footprint.**

Whatever the policy decides, a successful declassifying signal writes no
scheduler slot and no register bank outside `footprint.cores`. The two halves
together are the independence the sub-phase claims: policy decides *whether*,
the footprint decides *where*, and neither leaks into the other.

Rides `notificationSignalDeclassifiedOnCore_frame` — the post-state is SM6.B's
with `declassificationAuditLog` replaced, and that field is neither a scheduler
slot nor a register bank — so SM6.B's own confinement carries verbatim. -/
theorem notificationSignalDeclassifiedOnCore_confinedToCores
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st st' : SystemState) (sgi : Option (CoreId × Concurrency.SgiKind))
    (hObjInv : st.objects.invExt)
    (hStep : notificationSignalDeclassifiedOnCore ctx declPolicy notificationId badge
      executingCore st = (st', .ok sgi)) :
    observableSlotsConfinedToCores st st'
      (declassifiedSignalEffectFootprint st notificationId).cores := by
  rw [declassifiedSignalEffectFootprint_cores]
  refine observableSlotsConfinedToCores_of_framed_suffix ?_ ?_
    (observableSlotsConfinedToCores_mono (fun x hx => List.mem_append.mpr (Or.inl hx))
      (notificationSignalBoundOnCore_confinedToCores notificationId badge executingCore st hObjInv))
  · rw [notificationSignalDeclassifiedOnCore_frame ctx declPolicy notificationId badge
      executingCore st st' sgi hStep]
  · rw [notificationSignalDeclassifiedOnCore_frame ctx declPolicy notificationId badge
      executingCore st st' sgi hStep]

/-- WS-SM SM9.C.6 (**`declassificationRelativeNonInterference`**): the phase's
headline, and the first theorem in the tree that bounds a flow instead of
forbidding one.

Three conjuncts, and each is doing separate work:

1. **Confinement.** On every core outside the footprint, the observer's
   per-core view is literally unchanged. This is ordinary non-interference,
   restricted to the complement of the authorized footprint — the "relative" in
   the name.
2. **Recording.** Every difference the observer *may* see beyond an ordinary
   flow was authorized by `declassificationDecision` and appended to the trail,
   with the originating core and the policy basis on each entry. A downgrade
   that happened without a record is excluded, which is what makes the bound
   auditable rather than merely stated.
3. **No widening of the object effect.** The object store is exactly the
   ordinary bound signal's, so the visible difference in the shared half is the
   *delivery* and nothing more — the syscall does not take the opportunity to
   write anything else while it holds the authority to write something.

The `hShared` premise is the same division of labour every theorem in this
module uses: labels govern the shared half, core identity governs the per-core
half. It is *not* vacuous here — the delivery genuinely changes the shared half
for an observer cleared to see the receiver, which is the point of the phase —
and conjunct 3 is what bounds that change. -/
theorem declassificationRelativeNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (gctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (executingCore : CoreId) (st st' : SystemState)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (hObjInv : st.objects.invExt)
    (hStep : notificationSignalDeclassifiedOnCore gctx declPolicy notificationId badge
      executingCore st = (st', .ok sgi))
    (hShared : sharedViewUnchanged ctx observer st st') :
    (∀ c, c ∉ (declassifiedSignalEffectFootprint st notificationId).cores →
      projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c) ∧
    (∃ appended : DeclassificationAuditLog,
      st'.declassificationAuditLog = st.declassificationAuditLog ++ appended ∧
      ∀ e ∈ appended,
        declassificationDecision gctx declPolicy e.srcDomain e.dstDomain = .ok () ∧
        e.originatingCore = executingCore ∧ e.authorizationBasis = .policyRule) ∧
    st'.objects = (notificationSignalBoundOnCore notificationId badge executingCore st).1.objects := by
  refine ⟨fun c hne => crossCoreNonInterference_ofCores ctx observer hne
      (notificationSignalDeclassifiedOnCore_confinedToCores gctx declPolicy notificationId badge
        executingCore st st' sgi hObjInv hStep) hShared,
    declassifiedSignal_no_invented_edge gctx declPolicy notificationId badge executingCore
      st st' sgi hStep,
    ?_⟩
  rw [notificationSignalDeclassifiedOnCore_frame gctx declPolicy notificationId badge
    executingCore st st' sgi hStep]

/-- WS-SM SM9.C.6 (**the live `.declassifySignal` arm's post-state**): the
confinement of the state the checked dispatch actually commits.

The PR #870 round-4 rule applied to this arm: an inventory entry citing only the
transition would stay green if the arm drifted onto something an observer reads.
The arm commits `notificationSignalDeclassifiedCrossCoreDispatch`'s state and
nothing else (`dispatchWithCapChecked_declassifySignal_delegates`): the
declassifying signal, then (WS-SX SX8.2) seL4's donation of the notification's
context to the thread it woke, which writes that thread's home core alone
(`maybeDonateSchedContext_confinedToCores`) — a core the footprint names, read on
the entry state because neither the wake nor the trail append moves a link the
donation's guard reads (`notificationSignalBoundOnCore_signalDonationCores_eq`). -/
theorem declassifiedSignalDispatch_confinedToCores
    (gctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st stT : SystemState) (sgi : Option (CoreId × Concurrency.SgiKind))
    (hObjInv : st.objects.invExt)
    (hStep : notificationSignalDeclassifiedCrossCoreDispatch gctx declPolicy notificationId badge
      executingCore st = (stT, .ok sgi)) :
    observableSlotsConfinedToCores st stT
      (declassifiedSignalEffectFootprint st notificationId).cores := by
  unfold notificationSignalDeclassifiedCrossCoreDispatch at hStep
  generalize hD : notificationSignalDeclassifiedOnCore gctx declPolicy notificationId badge
    executingCore st = d at hStep
  obtain ⟨stD, r⟩ := d
  cases r with
  | error e => cases hStep
  | ok sgi' =>
    simp only [Prod.mk.injEq] at hStep
    obtain ⟨rfl, -⟩ := hStep
    have h1 := notificationSignalDeclassifiedOnCore_confinedToCores gctx declPolicy notificationId
      badge executingCore st stD sgi' hObjInv hD
    have hF := notificationSignalDeclassifiedOnCore_frame gctx declPolicy notificationId badge
      executingCore st stD sgi' hD
    unfold donateToSignalledFlowingGeneric
    cases hW : signalWokenThread? st notificationId with
    | none => exact h1
    | some t =>
      have hInvW := notificationSignalBoundOnCore_preserves_objects_invExt notificationId badge
        executingCore st hObjInv
      have hInvD : stD.objects.invExt := by rw [hF]; exact hInvW
      have hC : signalDonationCores stD notificationId t = signalDonationCores st notificationId t := by
        have hA : signalDonationCores stD notificationId t =
            signalDonationCores (notificationSignalBoundOnCore notificationId badge executingCore st).1
              notificationId t := by
          have hO : stD.objects =
              (notificationSignalBoundOnCore notificationId badge executingCore st).1.objects :=
            (congrArg SystemState.objects hF).trans rfl
          unfold signalDonationCores
          rw [signalDonationGuard_congr (n := notificationId) (tid := t) (st' := stD)
            (st := (notificationSignalBoundOnCore notificationId badge executingCore st).1)
            (by unfold SystemState.getNotification?; rw [hO])
            (fun s => by unfold SystemState.getSchedContext?; rw [hO])
            (by unfold SystemState.getTcb?; rw [hO])]
          unfold determineTargetCore SystemState.getTcb?
          rw [hO]
        exact hA.trans (notificationSignalBoundOnCore_signalDonationCores_eq notificationId badge
          executingCore st hObjInv t)
      have h2 : observableSlotsConfinedToCores stD
          (maybeDonateSchedContextFlowingGeneric gctx stD notificationId t)
          (signalDonationCores stD notificationId t) :=
        maybeDonateSchedContextFlowingGeneric_induct
          (fun s => observableSlotsConfinedToCores stD s (signalDonationCores stD notificationId t))
          gctx stD notificationId t (observableSlotsConfinedToCores_refl stD _)
          (maybeDonateSchedContext_confinedToCores stD notificationId t hInvD)
      rw [hC] at h2
      refine observableSlotsConfinedToCores_mono ?_ (observableSlotsConfinedToCores_trans h1 h2)
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hx
      · rw [declassifiedSignalEffectFootprint_cores, sendSignalWriteSet]
        refine List.mem_append.mpr (Or.inr ?_)
        simpa [signalWakeDonationCores, hW] using hx

/-- WS-SM SM9.C.6 (**the inventory's citation**): the live `.declassifySignal`
arm's committed post-state is invisible on every core outside the authorized
effect footprint.

This is the theorem `crossCoreNiTheorem` maps `.declassifySignalDispatch` to.
It names the *whole arm*, not the transition, for the round-4 reason; and it is
the one entry in the inventory whose write set is genuinely a *permission*
boundary rather than only a safety one, which is why the footprint it quantifies
over is `declassifiedSignalEffectFootprint` rather than a bare `List CoreId`. -/
theorem declassifiedSignalDispatch_crossCoreNonInterference
    (ctx : LabelingContext) (observer : IfObserver) (gctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st stT : SystemState) (sgi : Option (CoreId × Concurrency.SgiKind)) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hStep : notificationSignalDeclassifiedCrossCoreDispatch gctx declPolicy notificationId badge
      executingCore st = (stT, .ok sgi))
    (hne : c ∉ (declassifiedSignalEffectFootprint st notificationId).cores)
    (hShared : sharedViewUnchanged ctx observer st stT) :
    projectStateOnCore ctx observer stT c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (declassifiedSignalDispatch_confinedToCores gctx declPolicy notificationId badge
      executingCore st stT sgi hObjInv hStep) hShared

/-- WS-SX SX8.2 (**the live `.notificationSignal` arm**): the checked seL4-MCS `sendSignal`
(`sendSignalOnCoreFlowing`) writes no core outside its write set: the wake's
(`notificationSignalBoundOnCore_confinedToCores`) and the donation's, the home
core of the thread it woke where seL4's guard and the context-label check hold
(`maybeDonateSchedContext_confinedToCores`), read on the entry state.  Where the
context-label check refuses, nothing is donated and the write set
over-approximates the wake's. -/
theorem sendSignalOnCoreFlowing_confinedToCores (fctx : LabelingContext)
    (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) :
    observableSlotsConfinedToCores st
      (sendSignalOnCoreFlowing fctx notificationId badge executingCore st).1
      (sendSignalWriteSet st notificationId) := by
  have hW := notificationSignalBoundOnCore_confinedToCores notificationId badge executingCore st
    hObjInv
  refine sendSignalOnCoreFlowing_induct (fun s => observableSlotsConfinedToCores st s _) fctx
    notificationId badge executingCore st
    (observableSlotsConfinedToCores_mono (fun x hx => List.mem_append.mpr (Or.inl hx)) hW) ?_
  intro t _ hT _
  have h2 := maybeDonateSchedContext_confinedToCores _ notificationId t
    (notificationSignalBoundOnCore_preserves_objects_invExt notificationId badge executingCore st
      hObjInv)
  rw [notificationSignalBoundOnCore_signalDonationCores_eq notificationId badge executingCore st
    hObjInv t] at h2
  have hE : signalWakeDonationCores st notificationId = signalDonationCores st notificationId t := by
    simp [signalWakeDonationCores, hT]
  unfold sendSignalWriteSet
  rw [hE]
  exact observableSlotsConfinedToCores_trans hW h2

/-- WS-SX SX8.2 (**the inventory's citation for the live `.notificationSignal`
arm**): the checked seL4 `sendSignal`, which the arm runs
(`notificationSignalBoundCrossCoreDispatchChecked` runs `sendSignalOnCoreFlowing`
once its flow gates pass), is invisible
to any core outside its write set: the bound TCB's or the waiter's home core,
and the home core of the thread the notification's context is donated to. -/
theorem sendSignalOnCoreFlowing_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (executingCore : CoreId) (st : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hne : c ∉ sendSignalWriteSet st notificationId)
    (hShared : sharedViewUnchanged ctx observer st
      (sendSignalOnCoreFlowing ctx notificationId badge executingCore st).1) :
    projectStateOnCore ctx observer
      (sendSignalOnCoreFlowing ctx notificationId badge executingCore st).1 c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (sendSignalOnCoreFlowing_confinedToCores ctx notificationId badge executingCore st hObjInv)
    hShared

/-- WS-SX SX8.2: **the cores the live `.wait` arm writes**, read on its entry
state: the executing core the wait blocks on and the donation's where the
notification holds a word (`waitDonationCores`) — the run segment of the arm's
scheduler footprint.  A blocked wait's return writes no observable slot
(`maybeReturnSchedContext_confinedToCores`), so it adds no core. -/
def waitArmWriteSet (st : SystemState) (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) : List CoreId :=
  executingCore :: waitDonationCores st (some n) tid

/-- WS-SX SX8.2: **the live `.wait` arm writes only its write set**: the wait
writes the executing core; a consumed wait's badge frame writes no core and its
donation the donation's, read on the entry state
(`completeSignalArm_signalDonationCores_eq`); a blocked wait's return writes no
observable slot. -/
theorem completeSignalArm_confinedToCores (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (n : SeLe4n.ObjId) (executingCore : CoreId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (h : completeSignalArm ctx tid n executingCore st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' (waitArmWriteSet st n tid executingCore) := by
  have hJoin : ∀ {a b : SystemState}, observableSlotsConfinedToCores a b
      (waitArmWriteSet st n tid executingCore ++ waitArmWriteSet st n tid executingCore) →
      observableSlotsConfinedToCores a b (waitArmWriteSet st n tid executingCore) :=
    observableSlotsConfinedToCores_mono fun x hx => by
      rcases List.mem_append.mp hx with h | h <;> exact h
  have hE : executingCore ∈ waitArmWriteSet st n tid executingCore := List.mem_cons_self
  unfold completeSignalArm at h
  split at h
  · rename_i st1 badge hW
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
    subst h
    have hW' := notificationWaitCrossCoreDispatchChecked_ok_inner hW
    have hWait := notificationWaitOnCore_confinedToCores n tid executingCore st
    simp only [hW'] at hWait
    have hFr := observableSlotsConfinedToCores_of_framed_suffix
      (Architecture.writeReturnFrameToTcb_scheduler_eq _ tid (Architecture.badgeReturnFrame st1 tid badge))
      (Architecture.writeReturnFrameToTcb_machine_eq _ tid _) hWait
    have hD := maybeDonateSchedContextFlowing_confinedToCores (ctx := ctx) _ n tid
      (completeSignalArm_donationPre_objects_invExt hObjInv hW')
    rw [completeSignalArm_signalDonationCores_eq n hObjInv hW'] at hD
    have hPend := notificationWaitOnCore_notificationPending hW'
    simp only [Option.isSome_some] at hPend
    refine hJoin (observableSlotsConfinedToCores_trans
      (observableSlotsConfinedToCores_mono (fun x hx => ?_) hFr)
      (observableSlotsConfinedToCores_mono (fun x hx => ?_) hD))
    · rw [List.mem_singleton] at hx; subst hx; exact hE
    · simp only [waitArmWriteSet, waitDonationCores, Option.map_some, Option.getD_some, hPend,
        ↓reduceIte, List.mem_cons]
      exact Or.inr hx
  · rename_i st1 hW
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
    subst h
    have hW' := notificationWaitCrossCoreDispatchChecked_ok_inner hW
    have hWait := notificationWaitOnCore_confinedToCores n tid executingCore st
    simp only [hW'] at hWait
    have hR := maybeReturnSchedContext_confinedToCores st1 n tid
    refine hJoin (observableSlotsConfinedToCores_trans
      (observableSlotsConfinedToCores_mono (fun x hx => ?_) hWait)
      (observableSlotsConfinedToCores_mono (fun x hx => ?_) hR))
    · rw [List.mem_singleton] at hx; subst hx; exact hE
    · cases hx
  · cases h

/-- WS-SX SX8.2 (**the inventory's citation for the live `.wait` arm**): the arm
(`completeSignalArm`: the checked wait, then seL4-MCS's `completeSignal`
donation or `receiveSignal` return) is invisible to any core outside its write
set. -/
theorem completeSignalArm_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (tid : SeLe4n.ThreadId) (n : SeLe4n.ObjId)
    (executingCore : CoreId) (st st' : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (h : completeSignalArm ctx tid n executingCore st = .ok ((), st'))
    (hne : c ∉ waitArmWriteSet st n tid executingCore)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (completeSignalArm_confinedToCores ctx tid n executingCore st st' hObjInv h) hShared

-- ============================================================================
-- §7 Coverage
-- ============================================================================

/-- SM8.C.9 (**the live `.declassify` bound**): the declassification writes
**no core**.

Its entire state effect is one entry appended to
`SystemState.declassificationAuditLog` — not a scheduler slot, not a register
bank, not any per-core field. The sharpest bound the inventory can express, and
an honest one: `authorizeDeclassificationOnCore_frame` says the post-state is the
pre-state with that one field replaced. -/
theorem declassifyObjectFromCore_confinedToCores
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (targetId : SeLe4n.ObjId) (st st' : SystemState)
    (hStep : declassifyObjectFromCore ctx declPolicy c targetId st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' [] := by
  refine observableSlotsConfinedToCores_nil_of_framed ?_
  unfold declassifyObjectFromCore at hStep
  obtain ⟨cur, hCur⟩ : ∃ x, st.scheduler.currentOnCore c = x := ⟨_, rfl⟩
  rw [hCur] at hStep
  cases cur with
  | none => exact absurd hStep (by simp)
  | some tid =>
    obtain ⟨ty, hTy⟩ : ∃ t, st.getObjectType? targetId = t := ⟨_, rfl⟩
    rw [hTy] at hStep
    cases ty with
    | none => exact absurd hStep (by simp)
    | some _ =>
      obtain ⟨hSt', -, -⟩ := authorizeDeclassificationOnCore_frame ctx declPolicy c
        (declassificationActorOf ctx tid) (ctx.threadDomainOf tid) (ctx.objectDomainOf targetId)
        targetId st st' hStep
      subst hSt'
      exact ⟨rfl, rfl⟩

/-- SM8.C.9 (**the live `.declassify` arm, cross-core**): a declassification is
invisible on every core.

The audit trail is deliberately outside `ObservableState`
(`declassificationAudit_write_preserves_projection`), so this is not merely
"writes no scheduler slot" — it is that the one field it does write is one no
observer reads. See the field's docstring for why projecting it would open a
channel out of exactly the boundary the audit exists to police. -/
theorem declassifyObjectFromCore_crossCoreNonInterference
    (ctx : LabelingContext) (observer : IfObserver) (gctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (executingCore : CoreId)
    (targetId : SeLe4n.ObjId) (st st' : SystemState) (c : CoreId)
    (hStep : declassifyObjectFromCore gctx declPolicy executingCore targetId st = .ok ((), st'))
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer (by simp)
    (declassifyObjectFromCore_confinedToCores gctx declPolicy executingCore targetId st st'
      hStep) hShared

/-- SM9.A.10 (**the live `.auditRead` bound**): a trail read writes **no core**,
and in fact writes nothing at all.

The sharpest bound the inventory can express, and here it is not merely sharp
but exact: `auditReadFromCore_frame` says the post-state *is* the pre-state. -/
theorem auditReadFromCore_confinedToCores
    (ctx : GenericLabelingContext) (monitorClearance : Option SecurityDomain)
    (c : CoreId) (op : AuditReadOp) (st : SystemState) (w : Nat) (st' : SystemState)
    (hStep : auditReadFromCore ctx monitorClearance c op st = .ok (w, st')) :
    observableSlotsConfinedToCores st st' [] := by
  have hEq := auditReadFromCore_frame ctx monitorClearance c op st w st' hStep
  subst hEq
  exact observableSlotsConfinedToCores_nil_of_framed ⟨rfl, rfl⟩

/-- SM9.A.10 (**the live `.auditRead` arm, cross-core**): a trail read is
invisible on every core.

Trivially, because it writes nothing — but the entry is not decorative. The
per-core routing gate demands a cross-core entry for every arm that takes an
executing core, and this arm takes one (to resolve the *reader's* clearance from
the running subject). Without the entry there would be nothing bounding what
the arm writes remotely, and "obviously nothing" is exactly the claim the
inventory exists to make checkable. -/
theorem auditReadFromCore_crossCoreNonInterference
    (ctx : LabelingContext) (observer : IfObserver) (gctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (executingCore : CoreId)
    (op : AuditReadOp) (st : SystemState) (w : Nat) (st' : SystemState) (c : CoreId)
    (hStep : auditReadFromCore gctx monitorClearance executingCore op st = .ok (w, st'))
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer (by simp)
    (auditReadFromCore_confinedToCores gctx monitorClearance executingCore op st w st' hStep)
    hShared

/-- SM9.A.10 (**the live `.auditDrain` bound**): a drain writes **no core**.

Its whole state effect is the trail and its epoch — neither a scheduler slot nor
a register bank on any core. Unlike the read this genuinely *is* a write, so
the bound is the substantive one: `auditDrain_frame` says the post-state is the
pre-state with exactly those two fields replaced. -/
theorem auditDrainVisiblePrefix_confinedToCores
    (ctx : GenericLabelingContext) (monitorClearance : Option SecurityDomain)
    (c : CoreId) (count : Nat) (st : SystemState) (n : Nat) (st' : SystemState)
    (hStep : auditDrainVisiblePrefix ctx monitorClearance c count st = .ok (n, st')) :
    observableSlotsConfinedToCores st st' [] := by
  obtain ⟨hSt', -, -⟩ := auditDrain_frame ctx monitorClearance c count st n st' hStep
  subst hSt'
  exact observableSlotsConfinedToCores_nil_of_framed ⟨rfl, rfl⟩

/-- SM9.A.10 (**the live `.auditDrain` arm, cross-core**): a drain is invisible
on every core.

Like the declassification it is built beside, this is not merely "writes no
scheduler slot": the field it does write, the audit ring holding the trail and
the epoch, is one no observer reads
(`declassificationAudit_write_preserves_projection`). The epoch's exclusion
is the sharper of the two — it *counts* entries, including entries a partial
reader may not see. -/
theorem auditDrainVisiblePrefix_crossCoreNonInterference
    (ctx : LabelingContext) (observer : IfObserver) (gctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (executingCore : CoreId) (count : Nat)
    (st : SystemState) (n : Nat) (st' : SystemState) (c : CoreId)
    (hStep : auditDrainVisiblePrefix gctx monitorClearance executingCore count st
      = .ok (n, st'))
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer (by simp)
    (auditDrainVisiblePrefix_confinedToCores gctx monitorClearance executingCore count st n st'
      hStep) hShared

/-- SM9.A.10 (PR #870 round 4): the live `.auditRead` arm's **full** effect —
the transition *and* the WS-RA return-frame staging.

The checked dispatch does not stop at `auditReadFromCore`: on success it
writes the returned word into the caller's TCB
(`Architecture.writeReturnFrameToTcb`, per the delegates equation
`dispatchWithCapChecked_auditRead_delegates`), and an inventory entry citing
only the transition would stay green if that second stage drifted onto
something an observer reads. The staging write touches no scheduler slot and
no machine register bank (`writeReturnFrameToTcb_scheduler_eq` /
`_machine_eq`), so the composed step is confined to no core at all — exactly
as the transition alone is. -/
theorem auditReadDispatch_confinedToCores
    (gctx : GenericLabelingContext) (monitorClearance : Option SecurityDomain)
    (executingCore : CoreId) (op : AuditReadOp) (st : SystemState) (w : Nat)
    (st' : SystemState) (tid : SeLe4n.ThreadId)
    (frame : Architecture.SyscallReturnFrame)
    (hStep : auditReadFromCore gctx monitorClearance executingCore op st = .ok (w, st')) :
    observableSlotsConfinedToCores st
      (Architecture.writeReturnFrameToTcb st' tid frame) [] := by
  have hEq := auditReadFromCore_frame gctx monitorClearance executingCore op st w st' hStep
  subst hEq
  exact observableSlotsConfinedToCores_nil_of_framed
    ⟨Architecture.writeReturnFrameToTcb_scheduler_eq st' tid frame,
     Architecture.writeReturnFrameToTcb_machine_eq st' tid frame⟩

/-- SM9.A.10 (PR #870 round 4, **the live `.auditRead` arm's post-state,
cross-core**): the state the checked dispatch actually commits — transition
plus staged return frame — is invisible on every core.

This is the theorem the inventory maps `.auditReadDispatch` to. The staged
frame lands in the caller TCB's `registerContext`, which WS-H12c strips from
every projection, so the shared-view premise is exactly as dischargeable for
the composed step as for the bare transition
(`writeReturnFrameToTcb_preserves_projection` is the whole-projection form). -/
theorem auditReadDispatch_crossCoreNonInterference
    (ctx : LabelingContext) (observer : IfObserver) (gctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (executingCore : CoreId)
    (op : AuditReadOp) (st : SystemState) (w : Nat) (st' : SystemState)
    (tid : SeLe4n.ThreadId) (frame : Architecture.SyscallReturnFrame) (c : CoreId)
    (hStep : auditReadFromCore gctx monitorClearance executingCore op st = .ok (w, st'))
    (hShared : sharedViewUnchanged ctx observer st
      (Architecture.writeReturnFrameToTcb st' tid frame)) :
    projectStateOnCore ctx observer (Architecture.writeReturnFrameToTcb st' tid frame) c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer (by simp)
    (auditReadDispatch_confinedToCores gctx monitorClearance executingCore op st w st'
      tid frame hStep) hShared

/-- SM9.A.10 (PR #870 round 4): the live `.auditDrain` arm's **full** effect —
the drain *and* the staged new-visible-length word
(`dispatchWithCapChecked_auditDrain_delegates` is the arm-level equation). -/
theorem auditDrainDispatch_confinedToCores
    (gctx : GenericLabelingContext) (monitorClearance : Option SecurityDomain)
    (executingCore : CoreId) (count : Nat) (st : SystemState) (n : Nat)
    (st' : SystemState) (tid : SeLe4n.ThreadId)
    (frame : Architecture.SyscallReturnFrame)
    (hStep : auditDrainVisiblePrefix gctx monitorClearance executingCore count st
      = .ok (n, st')) :
    observableSlotsConfinedToCores st
      (Architecture.writeReturnFrameToTcb st' tid frame) [] := by
  obtain ⟨hSt', -, -⟩ := auditDrain_frame gctx monitorClearance executingCore count st n st'
    hStep
  subst hSt'
  exact observableSlotsConfinedToCores_nil_of_framed
    ⟨Architecture.writeReturnFrameToTcb_scheduler_eq _ tid frame,
     Architecture.writeReturnFrameToTcb_machine_eq _ tid frame⟩

/-- SM9.A.10 (PR #870 round 4, **the live `.auditDrain` arm's post-state,
cross-core**): the committed state — trail dropped, epoch advanced, length
staged — is invisible on every core. The theorem the inventory maps
`.auditDrainDispatch` to. -/
theorem auditDrainDispatch_crossCoreNonInterference
    (ctx : LabelingContext) (observer : IfObserver) (gctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (executingCore : CoreId) (count : Nat)
    (st : SystemState) (n : Nat) (st' : SystemState)
    (tid : SeLe4n.ThreadId) (frame : Architecture.SyscallReturnFrame) (c : CoreId)
    (hStep : auditDrainVisiblePrefix gctx monitorClearance executingCore count st
      = .ok (n, st'))
    (hShared : sharedViewUnchanged ctx observer st
      (Architecture.writeReturnFrameToTcb st' tid frame)) :
    projectStateOnCore ctx observer (Architecture.writeReturnFrameToTcb st' tid frame) c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer (by simp)
    (auditDrainDispatch_confinedToCores gctx monitorClearance executingCore count st n st'
      tid frame hStep) hShared

/-- SM8.B.2: the cross-core transitions this module instantiates
`crossCoreNonInterference` at, one per SM6 sub-phase that has one.

Recorded as data so the count is checkable and so a reader can see at a glance
what is *not* here. The exhaustive-match tripwire lives on `KernelOperation`
(`NonInterferencePerCore` §5); this list is the cross-core companion, and its
entries name theorems in this file. -/
inductive CrossCoreTransition where
  /-- SM5.C — the wake primitive, target = the woken thread's home core. -/
  | wake
  /-- SM6.A — the endpoint call; the first **two-core** write set. -/
  | endpointCall
  /-- SM6.A — the **live** `.call` arm: the call, the donation, and the
  priority-inheritance chain walk on each boosted server's home core. -/
  | endpointCallDispatch
  /-- SM6 — the **live** `.send` arm: the WithCaps cross-core send. Added in
  PR #861 review round 10, which found the arm still routed to the boot-pinned
  `endpointSendDualWithCaps`. -/
  | endpointSendDispatch
  /-- SM8.B — the **live** `.schedContextUnbind` arm: clear-and-requeue on the
  bound thread's home core. Added in PR #861 review round 14, after this cut's
  own home-core routing made it a remote writer. -/
  | schedContextUnbindDispatch
  /-- SM8.B — the **live** `.schedContextBind` arm: re-bucket on the bound
  thread's home core. Its write set reads the thread from the *argument*, not
  from the SC — bind rejects an already-bound SC. -/
  | schedContextBindDispatch
  /-- SM8.B — the **live** `.tcbSetAffinity` arm: migrate a thread between two
  home cores. The only entry whose write set names *two* remote cores, and the
  one that finally replaced this arm's routing-allowlist exception with a
  proof. -/
  | setThreadCpuAffinityDispatch
  /-- SM8.B — the **live** `.schedContextConfigure` arm: configure through a
  core's scheduling control, moving a thread homed elsewhere to that core, and
  re-bucket the bound thread on its home core when a reconfigure changes its
  priority. -/
  | schedContextConfigureDispatch
  /-- SM6.B — the notification signal. -/
  | notificationSignal
  /-- SM6.B — the bound-aware signal, covering bound delivery: the wake seL4's
  `sendSignal` makes, a below-API transition since WS-SX SX8.2. -/
  | notificationSignalBound
  /-- WS-SX SX8.2 — the **live** `.signal` arm: seL4-MCS `sendSignal`, the
  bound-aware wake then the donation of the notification's context to the
  thread it woke, under the context-label check (`sendSignalOnCoreFlowing`). -/
  | sendSignalDispatch
  /-- SM6.B — the notification wait: the wait alone, a below-API leg of the
  live `.wait` arm since WS-SX SX8.2. -/
  | notificationWait
  /-- WS-SX SX8.2 — the **live** `.wait` arm: the checked wait, then seL4-MCS's
  `completeSignal` donation where it consumed a word or `receiveSignal`'s
  `maybeReturnSchedContext` where it blocked (`completeSignalArm`). -/
  | waitDispatch
  /-- SM6.C — the reply. -/
  | endpointReply
  /-- SM6.C — the **live** `.reply` arm: reply, donation return, PIP reversion. -/
  | endpointReplyDispatch
  /-- SM6.C — the bare cross-core receive, below both live receive-shaped arms. -/
  | endpointReceiveDual
  /-- SM6.C — the **live** receive: the form that installs a parked send's
  capabilities, which `.receive` reaches directly and `.replyRecv` reaches as its
  second leg (PR #873 rounds 6 and 7). -/
  | endpointReceiveDualWithCaps
  /-- SM6.C — the **live** `.replyRecv` arm, `replyRecvTransferOnCore`: both legs,
  the donation pop and re-donation, the priority hand-off, and a faulted caller's
  fault answer.  (Audit IPC-2,
  `v0.36.49`: the separate entry for a two-leg composite below the donation is
  gone with that composite, which no arm ran.) -/
  | endpointReplyRecvDispatch
  /-- SM6.E — the deschedule primitive. -/
  | deschedule
  /-- SM6.E — the *composed* IPC-blocking cancellation (teardown + deschedule). -/
  | cancelIpcBlocking
  /-- SM6.E — the **live** `.tcbSuspend` arm: the whole suspend pipeline. -/
  | suspendThreadDispatch
  /-- SM5.F.6 — the **live** `.tcbResume` arm: ready-restore, home-core enqueue,
  and the reschedule. Added in PR #861 review round 10, which found the arm
  still routed to the boot-pinned `resumeThread`. -/
  | resumeThreadDispatch
  | setPriorityDispatch
  | setMCPriorityDispatch
  /-- SM8.B — the **live** `.vspaceMap` arm. The first of the three entries
  added in PR #861 review round 35 to empty the per-core routing allowlist: it
  takes an executing core, so the gate demands an entry, and its write set is
  **empty** — page tables, the scalar TLB, the shootdown round, the initiator's
  own per-core view and the I-cache ledger are none of them a scheduler slot or
  a register bank on any core. Until this entry existed the inventory had no way
  to *say* "writes no core", which is the only reason the arm held a waiver. -/
  | vspaceMapDispatch
  /-- SM8.B — the **live** `.vspaceUnmap` arm. Empty write set, same reasons. -/
  | vspaceUnmapDispatch
  /-- WS-BP BP7.1 (`v0.36.7`) — the **live** `.cspaceDelete` arm.  Takes an
  executing core since the delete finalises a frame capability — its recorded
  mapping is removed through the `.vspaceUnmap` arm's own transition — and writes
  no core. -/
  | cspaceDeleteDispatch
  /-- WS-BP BP7.1 (`v0.36.7`) — the **live** `.cspaceRevoke` arm.  Same reason:
  every frame capability it destroys is finalised. -/
  | cspaceRevokeDispatch
  /-- WS-ZA ZA5.4 part 14 — the **live** `.untypedRetype` arm, the carve every
  kernel object is made by.  Takes an executing core (a carved thread's domain
  and affinity are that core's) and writes no core: the untyped's record, the
  child, the free index, the new capability and its derivation edge are the
  object store and the CDT. -/
  | untypedRetypeDispatch
  /-- WS-ZA ZA5.4 part 22 — the **live** `.tcbSetSpace` arm.  Takes an executing
  core since the slot replace retires what each slot's old capability took with
  it (a root with its acknowledged ASID round), and writes no core: the slot
  copies and the retire are the object store, the CDT and the TLB state. -/
  | tcbSetSpaceDispatch
  /-- WS-SX SX6.6 — the **live** `.tcbSetIPCBuffer` arm.  Takes an executing
  core since the buffer slot's replace retires what its old capability took
  with it, and writes no core: the slot copy, the retire and the address are
  the object store and the CDT. -/
  | setIPCBufferDispatch
  /-- SM8.C.9 — the **live** `.declassify` arm. Takes an executing core (to
  resolve the running subject whose domain the downgrade is attributed to) and
  writes **no** core: its whole state effect is one entry appended to the
  declassification audit trail, which is not a per-core field at all. -/
  | declassifyDispatch
  /-- SM9.C.8 — the **live** `.declassifySignal` arm: the data-carrying
  declassification. The inventory's **only** entry whose write set is a
  permission boundary as well as a safety one — every other transition here is
  proven invisible, and this one is proven visible-but-bounded-and-recorded.
  Its cores are SM6.B's own `notificationSignalBoundWriteSet`, because the
  transition *is* the ordinary bound signal plus a trail append. -/
  | declassifySignalDispatch
  /-- SM9.A.10 — the **live** `.auditRead` arm. Takes an executing core (to
  resolve the *reader's* clearance from the running subject) and writes **no**
  core — in fact writes nothing at all. Present because the routing gate
  demands an entry for every arm that takes a core, which is what makes
  "obviously nothing" a checkable claim rather than an assertion. -/
  | auditReadDispatch
  /-- SM9.A.10 — the **live** `.auditDrain` arm. Takes an executing core and
  writes no core: its whole state effect is the audit trail and its epoch,
  neither of which is a per-core field. -/
  | auditDrainDispatch
  /-- WS-ZA ZA4.3 — the **live** `.yield` arm, run by both dispatchers' guard
  ahead of the caller's CSpace lookup. Takes the executing core and writes only
  that core: the caller's charge and re-enqueue and the scheduling point there. -/
  | yieldDispatch
  /-- WS-ZA ZA6.9 — the **live** `.schedContextConsumed` arm. Takes the
  executing core (its current thread is the caller) and writes no core: its
  whole effect is the context's count and the caller's saved registers. -/
  | schedContextConsumedDispatch
  /-- WS-ZA ZA6.29 — the **live** `.schedContextYieldTo` arm. Takes the
  executing core and writes it and the bound thread's home core: the resume's
  placement and the head requeue there, or the linked branch's dequeue, head
  enqueues and scheduling point on the executing core. -/
  | schedContextYieldToDispatch
  /-- WS-SX SX8.3 — the **live** `.schedContextUnbindObject` arm.  Its thread
  path is the per-core thread unbind: clear-and-requeue on the bound thread's
  home core; its notification path writes no core. -/
  | schedContextUnbindObjectDispatch
  /-- WS-ZA ZA6.32 — the **live** `.irqHandlerSetNotification` arm.  Takes the
  executing core for the zombie delete that empties the line's node slot before
  the copy, and writes the cores that delete names: every core when the slot held
  the last capability to a notification whose finalisation wakes waiters. -/
  | irqHandlerSetNotificationDispatch
  /-- WS-ZA ZA6.32 — the **live** `.irqHandlerClear` arm: the node slot's zombie
  delete alone, with the same write set. -/
  | irqHandlerClearDispatch
  deriving DecidableEq, Repr

def CrossCoreTransition.all : List CrossCoreTransition :=
  [.wake, .endpointCall, .endpointCallDispatch, .endpointSendDispatch,
   .schedContextUnbindDispatch, .schedContextBindDispatch, .schedContextConfigureDispatch,
   .setThreadCpuAffinityDispatch,
   .notificationSignal, .notificationSignalBound, .sendSignalDispatch, .waitDispatch,
   .notificationWait, .endpointReply, .endpointReplyDispatch, .endpointReceiveDual,
   .endpointReceiveDualWithCaps,
   .endpointReplyRecvDispatch, .deschedule, .cancelIpcBlocking,
   .suspendThreadDispatch, .resumeThreadDispatch,
   .setPriorityDispatch, .setMCPriorityDispatch,
   .vspaceMapDispatch, .vspaceUnmapDispatch,
   .cspaceDeleteDispatch, .cspaceRevokeDispatch, .untypedRetypeDispatch, .tcbSetSpaceDispatch,
   .setIPCBufferDispatch,
   .declassifyDispatch, .declassifySignalDispatch,
   .auditReadDispatch, .auditDrainDispatch, .yieldDispatch, .schedContextConsumedDispatch,
   .schedContextYieldToDispatch, .irqHandlerSetNotificationDispatch, .irqHandlerClearDispatch,
   .schedContextUnbindObjectDispatch]

/-- SM8.B.2: **`all` really is all of them.**

Every count, the injectivity check and both evidence tallies quantify over this
hand-written list rather than over the type, so a constructor omitted from it
would leave a transition out of the audited surface with all of them still
green. The match-based tables are exhaustive by construction; this list is not,
and needs its own theorem.

Caught by PR #861 review round 11 — the identical fix had just been applied to
`CovertChannelId.all` two files away, and the sibling was missed in the same
commit. Enumerations that gates quantify over need this uniformly, not
case-by-case. -/
theorem CrossCoreTransition.mem_all (t : CrossCoreTransition) :
    t ∈ CrossCoreTransition.all := by
  cases t <;> decide

/-- SM8.B.2: and lists each exactly once, so the counts count transitions. -/
theorem CrossCoreTransition.all_nodup : CrossCoreTransition.all.Nodup := by decide

/-- SM8.B.2: the name of each covered transition's non-interference theorem,
compile-time-validated through `niName!` — a renamed or deleted theorem breaks
this table rather than leaving it naming something that no longer exists. -/
def crossCoreNiTheorem : CrossCoreTransition → String
  | .wake => niName! wakeThread_crossCoreNonInterference_of_visible_thread
  | .endpointCall => niName! endpointCallOnCore_crossCoreNonInterference
  | .endpointCallDispatch => niName! endpointCallCrossCoreDispatch_crossCoreNonInterference
  | .endpointSendDispatch =>
      niName! endpointSendDualWithCapsOnCore_crossCoreNonInterference
  | .schedContextUnbindDispatch =>
      niName! schedContextUnbindAllOnCore_crossCoreNonInterference
  | .schedContextBindDispatch =>
      niName! schedContextBind_crossCoreNonInterference
  | .setThreadCpuAffinityDispatch =>
      niName! setThreadCpuAffinityWithMigration_crossCoreNonInterference
  | .schedContextConfigureDispatch =>
      niName! schedControlConfigure_crossCoreNonInterference
  | .notificationSignal => niName! notificationSignalOnCore_crossCoreNonInterference
  | .notificationSignalBound => niName! notificationSignalBoundOnCore_crossCoreNonInterference
  | .sendSignalDispatch => niName! sendSignalOnCoreFlowing_crossCoreNonInterference
  | .waitDispatch => niName! completeSignalArm_crossCoreNonInterference
  | .notificationWait => niName! notificationWaitOnCore_crossCoreNonInterference
  | .endpointReply => niName! endpointReplyOnCore_crossCoreNonInterference
  | .endpointReplyDispatch =>
      niName! endpointReplyCrossCoreDispatch_crossCoreNonInterference
  | .endpointReceiveDual => niName! endpointReceiveDualOnCore_crossCoreNonInterference
  | .endpointReceiveDualWithCaps =>
      niName! receiveWithReturn_crossCoreNonInterference
  | .endpointReplyRecvDispatch => niName! endpointReplyRecvOnCore_crossCoreNonInterference
  | .deschedule => niName! descheduleThread_crossCoreNonInterference
  | .cancelIpcBlocking => niName! cancelIpcBlockingOnCore_crossCoreNonInterference
  | .suspendThreadDispatch => niName! suspendThreadOnCore_crossCoreNonInterference
  | .resumeThreadDispatch => niName! resumeThreadOnCore_crossCoreNonInterference
  | .setPriorityDispatch => niName! setPriorityOnCore_crossCoreNonInterference
  | .setMCPriorityDispatch => niName! setMCPriorityOnCore_crossCoreNonInterference
  | .vspaceMapDispatch =>
      niName! vspaceMapOrRemapFromFrameCap_crossCoreNonInterference
  | .vspaceUnmapDispatch =>
      niName! vspaceUnmapPageWithShootdownAndIcacheBroadcast_crossCoreNonInterference
  | .cspaceDeleteDispatch => niName! cspaceDeleteSlotZombie_crossCoreNonInterference
  | .cspaceRevokeDispatch => niName! cspaceRevokeCdtFinalising_crossCoreNonInterference
  | .untypedRetypeDispatch => niName! untypedRetypeFromCap_crossCoreNonInterference
  | .tcbSetSpaceDispatch => niName! copyThreadSpacesZombie_crossCoreNonInterference
  | .setIPCBufferDispatch => niName! setIPCBufferOp_crossCoreNonInterference
  | .declassifyDispatch =>
      niName! declassifyObjectFromCore_crossCoreNonInterference
  -- SM9.C.6: the DISPATCH-level composition, for the round-4 reason and one
  -- more: this arm's post-processing (the stash clear and both WS-RA stagers)
  -- runs on threads the delivery just woke, so a citation stopping at the
  -- transition would leave the arm's most delivery-adjacent writes unbounded.
  | .declassifySignalDispatch =>
      niName! declassifiedSignalDispatch_crossCoreNonInterference
  -- PR #870 round 4: the two audit entries map to the DISPATCH-level
  -- composition — transition PLUS return-frame staging — because these are
  -- the inventory's only word-returning arms: the checked dispatch continues
  -- past the transition and writes the returned word into the caller's TCB,
  -- and a citation stopping at the transition would stay green if that stage
  -- drifted onto something an observer reads.
  | .auditReadDispatch =>
      niName! auditReadDispatch_crossCoreNonInterference
  | .auditDrainDispatch =>
      niName! auditDrainDispatch_crossCoreNonInterference
  | .yieldDispatch => niName! yieldOnCore_crossCoreNonInterference
  | .schedContextConsumedDispatch =>
      niName! schedContextConsumedOnCore_crossCoreNonInterference
  | .schedContextYieldToDispatch =>
      niName! schedContextYieldToOnCore_crossCoreNonInterference
  | .schedContextUnbindObjectDispatch =>
      niName! schedContextUnbindThreadObjectOnCore_crossCoreNonInterference
  | .irqHandlerSetNotificationDispatch =>
      niName! irqHandlerSetNotificationFromCap_crossCoreNonInterference
  | .irqHandlerClearDispatch => niName! irqHandlerClear_crossCoreNonInterference

theorem crossCoreNiTheorem_count : CrossCoreTransition.all.length = 41 := by rfl

/-- SM8.B.2: **which entries are the arms the live syscall dispatch actually
reaches**, as opposed to the below-API transitions they are built from.

This distinction is the point of the three entries added in the fourth review
round: `.signal` on the bound-delivery path, `.receive` rendezvousing with a
blocked sender, and `.replyRecv` combining its legs are all live behaviour, and
an inventory that passed its count and injectivity checks without them was
reporting coverage it did not have.

**A live entry must name the function the dispatch calls, not one it is built
from** (PR #861 review round 5). Three entries failed that test and now have
wrapper entries of their own: `.reply` routes to `endpointReplyCrossCoreDispatch`
(which adds the donation return and the PIP reversion), `.replyRecv` to
`endpointReplyRecvOnCore` (which adds the donation pop and the post-receive donation),
and `.tcbSuspend` to
`suspendThreadOnCore` (which adds the chain reversion, the running-core dequeue
and a scheduling point). Each does strictly more per-core writing than the
below-API transition it wraps, so the narrower theorem never bounded it.

One entry is a different case and is *not* re-pointed, because its live arm
calls the `…OnCore` transition **directly**:
`notificationSignalBoundCrossCoreDispatchChecked` runs `sendSignalOnCoreFlowing
ctx … executingCore st` once its flow gates pass (seL4-MCS `sendSignal`: the
bound-aware wake, then the donation under the context-label check, WS-SX SX8.2). For it the `…OnCore` theorem is a statement about the
live arm already; the bound-aware wake on its own (`.notificationSignalBound`) is
a below-API leg.  The `.wait` arm runs `completeSignalArm` — the checked wait,
then seL4-MCS's `completeSignal` donation or `receiveSignal`'s
`maybeReturnSchedContext` — so its live entry is `.waitDispatch`, and the wait
alone (`.notificationWait`) is a below-API leg (WS-SX SX8.2).

**Being a leg does not stop something being a live arm** (PR #861 review round
8) — but it does not make something one either. `endpointReceiveDualOnCore` was
a second entry of that kind while the `.receive` arm invoked it directly; it is
not any more. Both receive-shaped live arms now reach
`endpointReceiveDualWithCapsOnCore` (`.receive` since PR #873 round 6,
`endpointReplyRecvOnCore`'s second leg since round 7), which installs a parked send's
capabilities and is therefore *not* the bare transition. So the bare receive
joins `.notificationSignal` and `.endpointReply` as a below-API entry and
`.endpointReceiveDualWithCaps` carries the live-arm claim — along with
`syscallDelegates_receive`, whose statement already names the WithCaps form.
Leaving the claim on the bare entry would have been the round-5 error exactly:
an inventory naming a theorem about a function the dispatch no longer calls. -/
def crossCoreTransitionIsLiveArm : CrossCoreTransition → Bool
  | .wake => false
  | .endpointCall => false
  | .endpointCallDispatch => true
  | .endpointSendDispatch => true
  | .schedContextUnbindDispatch => true
  | .schedContextBindDispatch => true
  | .schedContextConfigureDispatch => true
  | .setThreadCpuAffinityDispatch => true
  | .notificationSignal => false
  -- WS-SX SX8.2: the bound-aware wake is a leg of `sendSignalOnCoreFlowing` now
  | .notificationSignalBound => false
  | .sendSignalDispatch => true
  -- WS-SX SX8.2: the wait is a leg of `completeSignalArm` now
  | .notificationWait => false
  | .waitDispatch => true
  | .endpointReply => false
  | .endpointReplyDispatch => true
  -- PR #873 round 7: the bare receive is a below-API transition now — both
  -- receive-shaped live arms reach the WithCaps form.
  | .endpointReceiveDual => false
  | .endpointReceiveDualWithCaps => true
  | .endpointReplyRecvDispatch => true
  | .deschedule => false
  | .cancelIpcBlocking => false
  | .suspendThreadDispatch => true
  | .resumeThreadDispatch => true
  | .setPriorityDispatch => true
  | .setMCPriorityDispatch => true
  | .vspaceMapDispatch => true
  | .vspaceUnmapDispatch => true
  | .cspaceDeleteDispatch => true
  | .cspaceRevokeDispatch => true
  | .declassifyDispatch => true
  | .declassifySignalDispatch => true
  | .auditReadDispatch => true
  | .auditDrainDispatch => true
  | .untypedRetypeDispatch => true
  | .tcbSetSpaceDispatch => true
  | .setIPCBufferDispatch => true
  | .yieldDispatch => true
  | .schedContextConsumedDispatch => true
  | .schedContextYieldToDispatch => true
  | .irqHandlerSetNotificationDispatch => true
  | .irqHandlerClearDispatch => true
  | .schedContextUnbindObjectDispatch => true

theorem crossCoreTransitionIsLiveArm_count :
    (CrossCoreTransition.all.filter crossCoreTransitionIsLiveArm).length = 32 := by decide

-- The check is quadratic in the inventory and linear in each theorem name, and
-- round 35's three entries (one of them 76 characters) pushed it past the
-- default budget: 25 constructors is 600 disequalities to decide where 22 was
-- 463. Raising the budget rather than weakening the check — the statement is
-- the point, and a `Nodup`-on-the-image reformulation decides the same
-- comparisons.
set_option maxHeartbeats 1000000 in
theorem crossCoreNiTheorem_injective :
    ∀ t₁ t₂ : CrossCoreTransition, crossCoreNiTheorem t₁ = crossCoreNiTheorem t₂ → t₁ = t₂ := by
  intro t₁ t₂ h
  cases t₁ <;> cases t₂ <;>
    first
      | rfl
      | (exact absurd h (by simp only [crossCoreNiTheorem]; decide))

/-- SM8.B.2: **what backs a "this is the live arm" claim.**

Nine review rounds on PR #861 produced twenty-six findings, and the single
largest class — three separate rounds — was this inventory asserting that some
function is the arm the live dispatch reaches, wrongly. Round 4 found three
arms missing; round 5 found `.reply` / `.replyRecv` / `.tcbSuspend` naming the
below-API transition instead of the wrapper that does strictly more; round 8
found `.receive` classified a leg when the checked arm calls it directly.

The root cause is visible in `API.lean`: eight dispatch arms carry a
`dispatchWithCap_…_delegates` theorem, and **none of those eight ever drifted**.
The tie is not documentation — it is a theorem saying `dispatch S = f …`, so a
wrong entry fails to compile. The cross-core arms had no such theorem, and all
three drifts happened there.

**The first cut of this type recorded a theorem *name*, and round 11 correctly
rejected it**: `niName!` checks that a declaration by that name exists, not that
it proves anything about *this* transition, so `.receive` could have cited the
`tcbSuspend` theorem and counted as backed. That was the same defect one level
up — a claim held by a string rather than by a type.

So the evidence now carries a **proof of `syscallDelegates sid`**, a proposition
computed from the syscall in `API.lean`. `syscallDelegates .receive` and
`syscallDelegates .tcbSuspend` are different propositions, so a proof cannot be
borrowed between arms; and every syscall without a delegation theorem maps to
`False`, so evidence for it cannot be constructed at all. -/
inductive LiveArmEvidence where
  /-- A proof that this arm's syscall delegates to the named implementation.
  The proposition is indexed by `sid`, so the proof is not transferable. -/
  | delegationProof (sid : SyscallId) (proof : syscallDelegates sid)
  /-- No delegation theorem yet: the classification rests on reading the arm.
  Honest, and weaker — this is the state the three drifts happened in. -/
  | readOffTheArm (note : String)

/-- SM8.B.2: whether an entry is mechanically tied to the dispatch. -/
def LiveArmEvidence.isDelegationBacked : LiveArmEvidence → Bool
  | .delegationProof _ _ => true
  | .readOffTheArm _ => false

/-- SM8.B.2: the syscall a delegation-backed entry is tied to, so the tie can be
checked against the transition rather than taken on trust. -/
def LiveArmEvidence.syscall? : LiveArmEvidence → Option SyscallId
  | .delegationProof sid _ => some sid
  | .readOffTheArm _ => none

/-- SM8.B.2: the syscall each live arm belongs to — `none` for the below-API
transitions, which are not syscall arms at all. -/
def crossCoreLiveArmSyscall : CrossCoreTransition → Option SyscallId
  | .wake => none
  | .endpointCall => none
  | .endpointCallDispatch => some .call
  | .endpointSendDispatch => some .send
  | .schedContextUnbindDispatch => some .schedContextUnbind
  | .schedContextBindDispatch => some .schedContextBind
  | .setThreadCpuAffinityDispatch => some .tcbSetAffinity
  | .schedContextConfigureDispatch => some .schedContextConfigure
  | .notificationSignal => none
  | .notificationSignalBound => none
  | .sendSignalDispatch => some .notificationSignal
  | .notificationWait => none
  | .waitDispatch => some .notificationWait
  | .endpointReply => none
  | .endpointReplyDispatch => some .reply
  | .endpointReceiveDual => none
  | .endpointReceiveDualWithCaps => some .receive
  | .endpointReplyRecvDispatch => some .replyRecv
  | .deschedule => none
  | .cancelIpcBlocking => none
  | .suspendThreadDispatch => some .tcbSuspend
  | .resumeThreadDispatch => some .tcbResume
  | .setPriorityDispatch => some .tcbSetPriority
  | .setMCPriorityDispatch => some .tcbSetMCPriority
  | .vspaceMapDispatch => some .vspaceMap
  | .vspaceUnmapDispatch => some .vspaceUnmap
  | .cspaceDeleteDispatch => some .cspaceDelete
  | .cspaceRevokeDispatch => some .cspaceRevoke
  | .declassifyDispatch => some .declassify
  | .declassifySignalDispatch => some .declassifySignal
  | .auditReadDispatch => some .auditRead
  | .auditDrainDispatch => some .auditDrain
  | .untypedRetypeDispatch => some .untypedRetype
  | .tcbSetSpaceDispatch => some .tcbSetSpace
  | .setIPCBufferDispatch => some .tcbSetIPCBuffer
  | .yieldDispatch => some .yield
  | .schedContextConsumedDispatch => some .schedContextConsumed
  | .schedContextYieldToDispatch => some .schedContextYieldTo
  | .schedContextUnbindObjectDispatch => some .schedContextUnbindObject
  | .irqHandlerSetNotificationDispatch => some .irqHandlerSetNotification
  | .irqHandlerClearDispatch => some .irqHandlerClear

/-- SM8.B.2: the evidence backing each live-arm classification. -/
def crossCoreLiveArmEvidence : CrossCoreTransition → LiveArmEvidence
  | .wake => .readOffTheArm "below-API primitive, not a syscall arm"
  | .endpointCall => .readOffTheArm "below-API transition; live arm is .endpointCallDispatch"
  | .endpointCallDispatch =>
      .readOffTheArm "checked `.call` arm calls endpointCallCrossCoreDispatch; delegation theorem pending"
  | .endpointSendDispatch => .delegationProof .send syscallDelegates_send
  | .schedContextUnbindDispatch =>
      .delegationProof .schedContextUnbind syscallDelegates_schedContextUnbind
  | .schedContextBindDispatch =>
      .readOffTheArm "capability-only `.schedContextBind` arm; delegation theorem pending"
  | .setThreadCpuAffinityDispatch =>
      .readOffTheArm "capability-only `.tcbSetAffinity` arm; delegation theorem pending"
  | .schedContextConfigureDispatch =>
      .readOffTheArm "capability-only `.schedContextConfigure` arm; delegation theorem pending"
  | .notificationSignal => .readOffTheArm "below-API transition; live arm is .sendSignalDispatch"
  | .notificationSignalBound => .readOffTheArm "below-API transition; live arm is .sendSignalDispatch"
  | .sendSignalDispatch =>
      .readOffTheArm "checked `.signal` arm; wrapper runs sendSignalOnCoreFlowing; delegation theorem pending"
  | .notificationWait => .readOffTheArm "below-API transition; live arm is .waitDispatch"
  | .waitDispatch =>
      .readOffTheArm "checked `.wait` arm calls completeSignalArm; delegation theorem pending"
  | .endpointReply => .readOffTheArm "below-API transition; live arm is .endpointReplyDispatch"
  | .endpointReplyDispatch =>
      .readOffTheArm "checked `.reply` arm calls endpointReplyCrossCoreDispatch; delegation theorem pending"
  | .endpointReceiveDual =>
      .readOffTheArm "below-API transition; live arm is .endpointReceiveDualWithCaps"
  | .endpointReceiveDualWithCaps => .delegationProof .receive syscallDelegates_receive
  | .endpointReplyRecvDispatch =>
      .readOffTheArm "checked `.replyRecv` arm calls replyRecvTransferOnCore; delegation theorem pending"
  | .deschedule => .readOffTheArm "below-API primitive, not a syscall arm"
  | .cancelIpcBlocking => .readOffTheArm "below-API composite; live arm is .suspendThreadDispatch"
  | .suspendThreadDispatch => .delegationProof .tcbSuspend syscallDelegates_tcbSuspend
  | .resumeThreadDispatch => .delegationProof .tcbResume syscallDelegates_tcbResume
  | .setPriorityDispatch =>
      .delegationProof .tcbSetPriority syscallDelegates_tcbSetPriority
  | .setMCPriorityDispatch =>
      .delegationProof .tcbSetMCPriority syscallDelegates_tcbSetMCPriority
  | .vspaceMapDispatch => .delegationProof .vspaceMap syscallDelegates_vspaceMap
  | .vspaceUnmapDispatch => .delegationProof .vspaceUnmap syscallDelegates_vspaceUnmap
  | .cspaceDeleteDispatch => .delegationProof .cspaceDelete syscallDelegates_cspaceDelete
  | .cspaceRevokeDispatch => .delegationProof .cspaceRevoke syscallDelegates_cspaceRevoke
  | .declassifyDispatch => .delegationProof .declassify syscallDelegates_declassify
  | .declassifySignalDispatch =>
      .delegationProof .declassifySignal syscallDelegates_declassifySignal
  | .auditReadDispatch => .delegationProof .auditRead syscallDelegates_auditRead
  | .auditDrainDispatch => .delegationProof .auditDrain syscallDelegates_auditDrain
  | .untypedRetypeDispatch =>
      .delegationProof .untypedRetype syscallDelegates_untypedRetype
  | .tcbSetSpaceDispatch => .delegationProof .tcbSetSpace syscallDelegates_tcbSetSpace
  | .setIPCBufferDispatch =>
      .delegationProof .tcbSetIPCBuffer syscallDelegates_tcbSetIPCBuffer
  | .yieldDispatch => .delegationProof .yield syscallDelegates_yield
  | .schedContextConsumedDispatch =>
      .delegationProof .schedContextConsumed syscallDelegates_schedContextConsumed
  | .schedContextYieldToDispatch =>
      .delegationProof .schedContextYieldTo syscallDelegates_schedContextYieldTo
  | .schedContextUnbindObjectDispatch =>
      .delegationProof .schedContextUnbindObject syscallDelegates_schedContextUnbindObject
  | .irqHandlerSetNotificationDispatch =>
      .delegationProof .irqHandlerSetNotification syscallDelegates_irqHandlerSetNotification
  | .irqHandlerClearDispatch =>
      .delegationProof .irqHandlerClear syscallDelegates_irqHandlerClear

/-- SM8.B.2 (**the tie is checked, not assumed**): a delegation-backed entry
names the syscall its own transition belongs to. Round 11's example — the
`.receive` entry citing the `tcbSuspend` theorem — is now excluded twice over:
by the indexed proposition, and by this. -/
theorem crossCoreLiveArmEvidence_syscall_matches (t : CrossCoreTransition) :
    (crossCoreLiveArmEvidence t).syscall?.isSome = true →
      (crossCoreLiveArmEvidence t).syscall? = crossCoreLiveArmSyscall t := by
  cases t <;> simp [crossCoreLiveArmEvidence, crossCoreLiveArmSyscall,
    LiveArmEvidence.syscall?]

/-- SM8.B.2: **how many live arms are mechanically tied to the dispatch.**

`crossCoreLiveArmDelegationBacked_count` and
`crossCoreTransitionIsLiveArm_count` immediately below are the two halves, so
the ratio is read off machine-checked facts rather than restated here (a figure
this paragraph carried, "ten of eighteen", had gone stale by seven arms when
WS-BP BP7.1 `v0.36.7` deleted it).

The parenthetical this paragraph used to carry warned that "prose that repeats a
`decide` is prose that goes stale the next time the `decide` changes", and then
went stale: it said "seven of fourteen" while `crossCoreTransitionIsLiveArm_count`
already read 15, having moved when round 27 rerouted an arm. Round 35's three
entries — `.vspaceMap`, `.vspaceUnmap` and `.lifecycleRetype`, the three that
emptied the per-core routing allowlist — moved both halves again, and all three
arrive delegation-backed, so the ratio improved rather than merely grew. The
number above is therefore worth exactly what the two theorem names beside it are
worth; if it disagrees with them, believe them.

Stated so the gap is a tracked quantity closable only by adding delegation
theorems — not something a reader reconstructs by grepping. -/
def crossCoreLiveArmDelegationBacked : List CrossCoreTransition :=
  CrossCoreTransition.all.filter (fun t =>
    crossCoreTransitionIsLiveArm t && (crossCoreLiveArmEvidence t).isDelegationBacked)

theorem crossCoreLiveArmDelegationBacked_count :
    crossCoreLiveArmDelegationBacked.length = 24 := by decide

/-- SM8.B.2: and the residual — the live arms still resting on a human reading
of `API.lean`, which is the state every one of the three drifts occurred in. -/
theorem crossCoreLiveArm_readOffTheArm_count :
    (CrossCoreTransition.all.filter (fun t =>
      crossCoreTransitionIsLiveArm t
        && !(crossCoreLiveArmEvidence t).isDelegationBacked)).length = 8 := by decide

/-- SM8.B.2: **which transitions can write a core other than the executing
one.** Named for remote *writes*, not for wakes: a reply, a deschedule and a
cancellation all name a remote core without waking anything, and the earlier
`…WakesRemote` spelling described the wrong semantics (PR #861 review). A
reader checking "does this module actually exercise the cross-core direction"
can check this instead of reading eleven proofs. -/
def crossCoreTransitionWritesRemote : CrossCoreTransition → Bool
  | .wake => true
  | .endpointCall => true
  | .endpointCallDispatch => true
  | .endpointSendDispatch => true
  | .schedContextUnbindDispatch => true
  | .schedContextBindDispatch => true
  | .schedContextConfigureDispatch => true
  | .setThreadCpuAffinityDispatch => true
  | .notificationSignal => true
  | .notificationSignalBound => true
  | .sendSignalDispatch => true
  | .notificationWait => false
  | .waitDispatch => true
  | .endpointReply => true
  | .endpointReplyDispatch => true
  | .endpointReceiveDual => true
  | .endpointReceiveDualWithCaps => true
  | .endpointReplyRecvDispatch => true
  | .deschedule => true
  | .cancelIpcBlocking => true
  | .suspendThreadDispatch => true
  | .resumeThreadDispatch => true
  | .setPriorityDispatch => true
  | .setMCPriorityDispatch => true
  -- the two VSpace arms take an executing core and write **no** core with it
  | .vspaceMapDispatch => false
  | .vspaceUnmapDispatch => false
  -- WS-ZA ZA5.4: and the reset, which writes one capability's free index
  -- WS-BP BP7.1 (`v0.36.7`): the two finalising destroyers' teardown is the
  -- unmap's own transition, but (WS-ZA ZA5.4 part 23) the finalisation of a
  -- final capability's endpoint or notification wakes each waiter it cancels
  -- on the waiter's own core
  | .cspaceDeleteDispatch => true
  | .cspaceRevokeDispatch => true
  -- WS-ZA ZA5.4 part 14: and the carve, which writes the object store alone
  | .untypedRetypeDispatch => false
  -- WS-ZA ZA5.4 part 26: and the space change, whose old CSpace root, when it
  -- is the last capability to a CNode holding capabilities, is deleted by the
  -- zombie loop, whose finalisations wake waiters on their own cores
  | .tcbSetSpaceDispatch => true
  -- WS-SX SX6.6: and the buffer change, whose old capability is a frame's,
  -- whose retire wakes no waiter
  | .setIPCBufferDispatch => false
  -- SM8.C.9: and the declassification, for a different reason — the only field
  -- it writes is not per-core at all
  | .declassifyDispatch => false
  -- SM9.C.8: and the data-carrying declassification DOES write remotely — it
  -- wakes the receiver on its own home core, exactly as the ordinary bound
  -- signal it wraps. The one entry here whose remote write is a *deliberately
  -- visible* flow rather than an invisible one.
  | .declassifySignalDispatch => true
  | .auditReadDispatch => false
  | .auditDrainDispatch => false
  -- WS-ZA ZA4.3: the yield writes only the core it runs on
  | .yieldDispatch => false
  -- WS-ZA ZA6.9: the Consumed invocation writes no core at all
  | .schedContextConsumedDispatch => false
  -- WS-ZA ZA6.29: the yieldTo invocation writes the bound thread's home core
  | .schedContextYieldToDispatch => true
  -- WS-SX SX8.3: the unbind-object's thread path requeues on the thread's home
  | .schedContextUnbindObjectDispatch => true
  -- WS-ZA ZA6.32: the two interrupt-handler arms empty the line's node slot by
  -- the zombie delete, whose finalisations wake waiters on their own cores
  | .irqHandlerSetNotificationDispatch => true
  | .irqHandlerClearDispatch => true

theorem crossCoreTransitionWritesRemote_count :
    (CrossCoreTransition.all.filter crossCoreTransitionWritesRemote).length = 31 := by decide

end SeLe4n.Kernel
