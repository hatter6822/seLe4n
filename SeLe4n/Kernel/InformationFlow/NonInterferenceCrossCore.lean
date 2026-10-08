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
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hne : c ∉ endpointCallDispatchWriteSet endpointId caller msg endpointRights
      receiverSlotBase executingCore st)
    (hShared : sharedViewUnchanged ctx observer st
      (endpointCallCrossCoreDispatch endpointId caller msg endpointRights
        receiverSlotBase executingCore st).1) :
    projectStateOnCore ctx observer
        (endpointCallCrossCoreDispatch endpointId caller msg endpointRights
          receiverSlotBase executingCore st).1 c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (endpointCallCrossCoreDispatch_confinedToCores endpointId caller msg endpointRights
      receiverSlotBase executingCore st hObjInv)
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
    (observer : IfObserver) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage)
    (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st st' : SystemState) (summary : CapTransferSummary) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReplyRecvOnCore endpointId receiver replyId prevCaller msg receiverCspaceRoot
        receiverSlotBase executingCore st
      = .ok (summary, st'))
    (hne : c ∉ endpointReplyRecvWriteSet endpointId receiver replyId prevCaller msg
      receiverCspaceRoot receiverSlotBase executingCore st)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (endpointReplyRecvOnCore_confinedToCores endpointId receiver replyId prevCaller msg receiverCspaceRoot
      receiverSlotBase executingCore st st' summary hObjInv hStep)
    hShared

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
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hne : c ∉ endpointSendWriteSet st endpointId executingCore)
    (hShared : sharedViewUnchanged ctx observer st
      (endpointSendDualWithCapsOnCore endpointId sender msg endpointRights
        receiverSlotBase executingCore st).1) :
    projectStateOnCore ctx observer
        (endpointSendDualWithCapsOnCore endpointId sender msg endpointRights
          receiverSlotBase executingCore st).1 c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (endpointSendDualWithCapsOnCore_confinedToCores endpointId sender msg endpointRights
      receiverSlotBase executingCore st hObjInv)
    hShared

/-- SM8.B.2 (**the live checked `.send` non-interference**). -/
theorem endpointSendCrossCoreDispatchChecked_crossCoreNonInterference
    (ctx : LabelingContext) (observer : IfObserver) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hne : c ∉ endpointSendWriteSet st endpointId executingCore)
    (hShared : sharedViewUnchanged ctx observer st
      (endpointSendCrossCoreDispatchChecked ctx endpointId sender msg endpointRights
        receiverSlotBase executingCore st).1) :
    projectStateOnCore ctx observer
        (endpointSendCrossCoreDispatchChecked ctx endpointId sender msg endpointRights
          receiverSlotBase executingCore st).1 c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (endpointSendCrossCoreDispatchChecked_confinedToCores ctx endpointId sender msg
      endpointRights receiverSlotBase executingCore st hObjInv)
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

/-- SM8.B.2 (**the live `.schedContextConfigure` non-interference**): a configure
is invisible on every core outside its subject's home core and the cores of the
inheritance chain it re-walks. -/
theorem schedContextConfigure_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (vScId : SeLe4n.ValidObjId)
    (budget period priority deadline domain : Nat) (st st' : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hStep : SchedContextOps.schedContextConfigure vScId budget period priority deadline domain st
      = .ok ((), st'))
    (hne : c ∉ schedContextConfigureWriteSet st vScId.val)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (schedContextConfigure_confinedToCores vScId budget period priority deadline domain
      st st' hObjInv hStep) hShared

/-- SM8.B.3 (**the live `.schedContextUnbind` arm, cross-core**): an unbind is
invisible on every core outside its write set — including the core the demoted
thread was running on, when that is not the observer's. -/
theorem schedContextUnbindOnCore_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (vScId : SeLe4n.ValidObjId) (executingCore : CoreId)
    (st st' : SystemState) (c : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (hStep : SchedContextOps.schedContextUnbindOnCore vScId executingCore st
      = .ok (st', sgi))
    (hne : c ∉ schedContextUnbindOnCoreWriteSet st vScId.val executingCore)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (schedContextUnbindOnCore_confinedToCores vScId executingCore st st' sgi hStep) hShared

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

/-- **WS-BP BP7.1**: the live `.vspaceMap` arm, cross-core — a frame mapping is
invisible on every core, stated at the definition the arm runs. -/
theorem vspaceMapFromFrameCap_crossCoreNonInterference
    (ctx : LabelingContext) (observer : IfObserver)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (args : Architecture.SyscallArgDecode.VSpaceMapArgs) (st st' : SystemState) (c : CoreId)
    (hStep : vspaceMapFromFrameCap tid executingCore args st = .ok ((), st'))
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer (by simp)
    (vspaceMapFromFrameCap_confinedToCores tid executingCore args st st' hStep) hShared

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

/-- WS-BP BP7.1 (slice 3) (**the live `.untypedReset` arm, cross-core**): a
reset is invisible on **every** core. -/
theorem untypedReset_crossCoreNonInterference
    (ctx : LabelingContext) (observer : IfObserver) (executingCore : CoreId)
    (untypedId : SeLe4n.ObjId) (st st' : SystemState) (c : CoreId)
    (hStep : untypedReset executingCore untypedId st = .ok ((), st'))
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer (by simp)
    (untypedReset_confinedToCores executingCore untypedId st st' hStep) hShared

/-- **`v0.36.37`: the live `.untypedReset` arm, cross-core** — invisible on every
core, with its acknowledged ASID rounds. -/
theorem untypedResetWithShootdown_crossCoreNonInterference
    (ctx : LabelingContext) (observer : IfObserver) (executingCore : CoreId)
    (untypedId : SeLe4n.ObjId) (st st' : SystemState) (c : CoreId)
    (hStep : untypedResetWithShootdown executingCore untypedId st = .ok ((), st'))
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer (by simp)
    (untypedResetWithShootdown_confinedToCores executingCore untypedId st st' hStep) hShared

/-- WS-BP BP7.1 (`v0.36.7`) (**the live `.cspaceDelete` arm, cross-core**): a
finalising delete is invisible on **every** core. -/
theorem cspaceDeleteSlotFinalising_crossCoreNonInterference
    (ctx : LabelingContext) (observer : IfObserver) (executingCore : CoreId)
    (addr : CSpaceAddr) (st st' : SystemState) (c : CoreId)
    (hStep : cspaceDeleteSlotFinalising executingCore addr st = .ok ((), st'))
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer (by simp)
    (cspaceDeleteSlotFinalising_confinedToCores executingCore addr st st' hStep) hShared

/-- WS-BP BP7.1 (`v0.36.7`) (**the live `.cspaceRevoke` arm, cross-core**): a
finalising revocation is invisible on **every** core. -/
theorem cspaceRevokeCdtFinalising_crossCoreNonInterference
    (ctx : LabelingContext) (observer : IfObserver) (executingCore : CoreId)
    (addr : CSpaceAddr) (st st' : SystemState) (c : CoreId)
    (hStep : cspaceRevokeCdtFinalising executingCore addr st = .ok ((), st'))
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer (by simp)
    (cspaceRevokeCdtFinalising_confinedToCores executingCore addr st st' hStep) hShared

/-- SM8.B.3 (**the live `.lifecycleRetype` arm, cross-core**): a retype is
invisible on every core the destroyed object did not occupy.

Read the hypotheses: `hne` is membership in a set computed from the **pre-state**
(it has to be — the destroyed thread is gone from the post-state), and `hShared`
is the object-level premise. There is no hypothesis about the label of the
thread being destroyed.

The CSpaceAddr sibling `lifecycleRetypeWithCleanupShootdownPerCoreIcache` gets no
entry of its own because no syscall arm routes to it; if one ever does, the
per-core routing gate will ask for this proof at that form before the arm can
merge. -/
theorem lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_crossCoreNonInterference
    (ctx : LabelingContext) (observer : IfObserver) (executingCore : CoreId)
    (authCap : Capability) (target : SeLe4n.ObjId) (newObj : KernelObject)
    (st st' : SystemState) (c : CoreId)
    (hne : c ∉ lifecycleRetypeWriteSet st target)
    (hStep : lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache executingCore authCap
      target newObj st = .ok ((), st'))
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_confinedToCores executingCore
      authCap target newObj st st' hStep) hShared

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

/-- SM8.B.2 (SM6.A, **the two-core case**): a cross-core endpoint call is
invisible to any core that is neither the receiver's home core nor the caller's
own core. -/
theorem endpointCallOnCore_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (executingCore : CoreId) (st : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hne : c ∉ endpointCallWriteSet st endpointId executingCore)
    (hShared : sharedViewUnchanged ctx observer st
      (endpointCallOnCore endpointId caller msg executingCore st).1) :
    projectStateOnCore ctx observer
        (endpointCallOnCore endpointId caller msg executingCore st).1 c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (endpointCallOnCore_confinedToCores endpointId caller msg executingCore st hObjInv)
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

/-- SM8.B.2 (**the live `.receive` arm, and the `.replyRecv` receive leg**,
PR #873 round 7): the cross-core receive that *installs* the capabilities a
parked send was carrying is invisible to any core outside the same write set.

The entry the inventory needs, and it did not exist. Both receive-shaped live
arms route through `endpointReceiveDualWithCapsOnCore` — `.receive` since round 6,
`.replyRecv`'s leg since round 7 — while the inventory's `.endpointReceiveDual`
entry named the theorem about the *bare* transition, which the capability install
is not. It is the same "a live entry must name the function the dispatch calls"
rule three earlier rounds applied to `.reply`, `.replyRecv` and `.tcbSuspend`;
this is the receive's turn. The bound is unchanged, because the install writes
no core. -/
theorem endpointReceiveDualWithCapsOnCore_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) (receiverCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hne : c ∉ endpointReceiveDualWriteSet st endpointId executingCore)
    (hShared : sharedViewUnchanged ctx observer st
      (endpointReceiveDualWithCapsOnCore endpointId receiver replyId receiverCspaceRoot
        receiverSlotBase executingCore st).1) :
    projectStateOnCore ctx observer
        (endpointReceiveDualWithCapsOnCore endpointId receiver replyId receiverCspaceRoot
          receiverSlotBase executingCore st).1 c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (endpointReceiveDualWithCapsOnCore_confinedToCores endpointId receiver replyId
      receiverCspaceRoot receiverSlotBase executingCore st hObjInv)
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
    (executingCore : CoreId) (st : SystemState) (c : CoreId)
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
    (cancelIpcBlockingOnCore_confinedToCores victim tcb executingCore st) hShared

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

The distinction the sub-phase turns on, and the one `footprint_does_not_authorize`
below makes a theorem rather than a remark: **naming a sink in the footprint
says where writes land, not that they are permitted.** The footprint is
computed from the *state* — which notification, which receiver, which home core
— and consults no policy at all. Authorization is a separate, per-hop decision,
and a receiver that is squarely inside the footprint is refused when the policy
refuses it. Conflating the two would be exactly the SM6.B badge-leak class one
abstraction up: "the delivery targets this TCB" read as "the delivery to this
TCB is allowed". -/

/-- WS-SM SM9.C.5: **the authorized effect footprint of a declassifying signal.**

Three components, because a data-carrying declassification touches three kinds
of thing and an auditor needs all three:

* `notification` — the object the badge is written into. Always present: it is
  the capability's own target.
* `receiver` — the thread the badge is delivered onward to, resolved from the
  *pre-state* by `declassifiedSignalReceiver?` (the bound TCB, else the head
  waiter). `none` when the signal only accumulates a badge with nobody to
  deliver it to, which is also exactly when the second hop needs no
  authorization.
* `cores` — the scheduler slots and register banks the delivery may write,
  which is SM6.B's own `notificationSignalBoundWriteSet`. Sharing that
  definition rather than restating it is deliberate: the transition *is* the
  ordinary bound signal plus a trail append
  (`notificationSignalDeclassifiedOnCore_frame`), so a footprint naming
  different cores than SM6.B's write set would be describing a transition the
  kernel does not run.

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

**Takes no `DeclassificationPolicy` and no `LabelingContext`** — which is the
content of `footprint_does_not_authorize` stated at the level of the type
signature, and the reason that theorem is provable rather than merely
plausible. -/
def declassifiedSignalEffectFootprint (st : SystemState) (notificationId : SeLe4n.ObjId) :
    DeclassificationEffectFootprint :=
  { notification := notificationId
    receiver := declassifiedSignalReceiver? st notificationId
    cores := notificationSignalBoundWriteSet st notificationId }

/-- WS-SM SM9.C.5: the footprint's receiver is the transition's own pre-state
resolution — the same function the *authorization* consults for its second hop.

Load-bearing rather than a restatement: the two must name the same thread, or a
footprint could bound the writes to one TCB while the policy check ran against
another. That is the confused-deputy shape one level up from the v0.32.97
capability-target finding, and this is where it is excluded. -/
@[simp] theorem declassifiedSignalEffectFootprint_receiver (st : SystemState)
    (notificationId : SeLe4n.ObjId) :
    (declassifiedSignalEffectFootprint st notificationId).receiver =
      declassifiedSignalReceiver? st notificationId := rfl

/-- WS-SM SM9.C.5: the footprint's cores are SM6.B's write set, so the
information-flow bound and the delivery's own scheduling effects cannot name
different cores. -/
@[simp] theorem declassifiedSignalEffectFootprint_cores (st : SystemState)
    (notificationId : SeLe4n.ObjId) :
    (declassifiedSignalEffectFootprint st notificationId).cores =
      notificationSignalBoundWriteSet st notificationId := rfl

/-- WS-SM SM9.C.6 (**`footprint_does_not_authorize`**): a receiver inside the
authorized effect footprint is **still refused** when the policy refuses it.

The theorem the sub-phase exists to make checkable. Its hypotheses are the
receiver's own two denials — the base lattice says no and the declassification
policy says no — and its conclusion is that the plan errors at the *second* hop,
with the second hop's own discriminant, even though the first hop was
authorized and even though the receiver is exactly the thread the footprint
names.

Read the other way: `receiver ∈ footprint` carries no authorization content
whatsoever. A reader who took the footprint as a permission — "the delivery may
write this TCB, therefore the delivery to it is allowed" — would have re-opened
the badge leak SM6.B closed at v0.31.73, with stronger authority behind it. -/
theorem footprint_does_not_authorize (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (notificationId : SeLe4n.ObjId)
    (actorDomain : SecurityDomain) (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hIn : (declassifiedSignalEffectFootprint st notificationId).receiver = some receiver)
    (hFirst : ctx.policy.canFlow actorDomain (ctx.objectDomainOf notificationId) = true)
    (hDeny : ctx.policy.canFlow (ctx.objectDomainOf notificationId)
      (ctx.threadDomainOf receiver) = false)
    (hNoDecl : declPolicy.canDeclassify (ctx.objectDomainOf notificationId)
      (ctx.threadDomainOf receiver) = false) :
    declassifiedSignalPlan ctx declPolicy notificationId actorDomain st =
      .error .declassificationDeniedAtReceiver :=
  declassifiedSignalPlan_receiver_refused ctx declPolicy notificationId actorDomain st receiver
    hFirst (by simpa using hIn) hDeny hNoDecl

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
    (notificationSignalBoundOnCore_confinedToCores notificationId badge executingCore st hObjInv)
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
confinement of the state the checked dispatch actually commits — transition,
stash clear, and both WS-RA stagers.

The PR #870 round-4 rule applied to this arm: an inventory entry citing only the
transition would stay green if the post-processing drifted onto something an
observer reads. Neither the stash clear (one `storeObject`) nor either stager
(`writeReturnFrameToTcb`, which touches `registerContext` only) writes a
scheduler slot or a register bank, so the composed step is confined to exactly
the footprint the transition alone is. -/
theorem declassifiedSignalDispatch_confinedToCores
    (gctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st stT stS : SystemState) (sgi : Option (CoreId × Concurrency.SgiKind))
    (woken? plainWaiter? : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : notificationSignalDeclassifiedOnCore gctx declPolicy notificationId badge
      executingCore st = (stT, .ok sgi))
    (hStash : clearWokenReceiverStash woken? stT = .ok ((), stS)) :
    observableSlotsConfinedToCores st
      (Architecture.stageWokenDelivery
        (Architecture.stageWokenDelivery stS woken? 0) plainWaiter? 0)
      (declassifiedSignalEffectFootprint st notificationId).cores := by
  -- Step 1: the transition.
  have h1 := notificationSignalDeclassifiedOnCore_confinedToCores gctx declPolicy notificationId
    badge executingCore st stT sgi hObjInv hStep
  -- Step 2: the stash clear — one `storeObject`, scheduler- and machine-silent.
  have h2 : observableSlotsConfinedToCores st stS
      (declassifiedSignalEffectFootprint st notificationId).cores :=
    observableSlotsConfinedToCores_of_framed_suffix
      (clearWokenReceiverStash_scheduler_eq woken? stT ((), stS) hStash)
      (clearWokenReceiverStash_machine_eq woken? stT ((), stS) hStash) h1
  -- Step 3: the bound receiver's stager.
  have h3 : observableSlotsConfinedToCores st
      (Architecture.stageWokenDelivery stS woken? 0)
      (declassifiedSignalEffectFootprint st notificationId).cores :=
    observableSlotsConfinedToCores_of_framed_suffix
      (Architecture.stageWokenDelivery_scheduler_eq stS woken? 0)
      (Architecture.stageWokenDelivery_machine_eq stS woken? 0) h2
  -- Step 4: the plain waiter's stager.
  exact observableSlotsConfinedToCores_of_framed_suffix
    (Architecture.stageWokenDelivery_scheduler_eq _ plainWaiter? 0)
    (Architecture.stageWokenDelivery_machine_eq _ plainWaiter? 0) h3

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
    (st stT stS : SystemState) (sgi : Option (CoreId × Concurrency.SgiKind))
    (woken? plainWaiter? : Option SeLe4n.ThreadId) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hStep : notificationSignalDeclassifiedOnCore gctx declPolicy notificationId badge
      executingCore st = (stT, .ok sgi))
    (hStash : clearWokenReceiverStash woken? stT = .ok ((), stS))
    (hne : c ∉ (declassifiedSignalEffectFootprint st notificationId).cores)
    (hShared : sharedViewUnchanged ctx observer st
      (Architecture.stageWokenDelivery
        (Architecture.stageWokenDelivery stS woken? 0) plainWaiter? 0)) :
    projectStateOnCore ctx observer
        (Architecture.stageWokenDelivery
          (Architecture.stageWokenDelivery stS woken? 0) plainWaiter? 0) c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (declassifiedSignalDispatch_confinedToCores gctx declPolicy notificationId badge
      executingCore st stT stS sgi woken? plainWaiter? hObjInv hStep hStash) hShared

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
(`declassificationAuditLog_write_preserves_projection`), so this is not merely
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
scheduler slot": the two fields it does write are ones no observer reads
(`declassificationAuditLog_write_preserves_projection`,
`declassificationAuditEpoch_write_preserves_projection`). The epoch's exclusion
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
  /-- SM8.B — the **live** `.schedContextConfigure` arm: re-bucket the bound
  thread on its home core when a reconfigure changes its priority. -/
  | schedContextConfigureDispatch
  /-- SM6.B — the notification signal. -/
  | notificationSignal
  /-- SM6.B — the **live** `.signal` arm, covering bound delivery. -/
  | notificationSignalBound
  /-- SM6.B — the notification wait. -/
  | notificationWait
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
  /-- SM6.C — the **live** `.replyRecv` arm, `endpointReplyRecvOnCore`: both legs,
  the donation pop and re-donation, and the priority hand-off.  (Audit IPC-2,
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
  /-- WS-BP BP7.1 (slice 3) — the **live** `.untypedReset` arm.  Takes an
  executing core to initiate its unmaps' shootdown rounds, and writes no core:
  its unmap pass is the `.vspaceUnmap` arm's own transition, the retire and the
  rewind write the object table alone, and (`v0.36.37`) its acknowledged `.aside1`
  rounds write the TLB state alone (`untypedResetWithShootdown`). -/
  | untypedResetDispatch
  /-- WS-BP BP7.1 (`v0.36.7`) — the **live** `.cspaceDelete` arm.  Takes an
  executing core since the delete finalises a frame capability — its recorded
  mapping is removed through the `.vspaceUnmap` arm's own transition — and writes
  no core. -/
  | cspaceDeleteDispatch
  /-- WS-BP BP7.1 (`v0.36.7`) — the **live** `.cspaceRevoke` arm.  Same reason:
  every frame capability it destroys is finalised. -/
  | cspaceRevokeDispatch
  /-- SM8.B — the **live** `.lifecycleRetype` arm, and the one of the final three
  that genuinely writes scheduler state: destroying a TCB sweeps it out of every
  core's run queue and current slot, because a destroy has no home core to key
  on. Its write set is therefore the set of cores the destroyed thread
  *occupied* — sharp rather than the trivially-true `allCores`, and available
  only because review round 17 made the sweep's step guarded. -/
  | lifecycleRetypeDispatch
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
  deriving DecidableEq, Repr

def CrossCoreTransition.all : List CrossCoreTransition :=
  [.wake, .endpointCall, .endpointCallDispatch, .endpointSendDispatch,
   .schedContextUnbindDispatch, .schedContextBindDispatch, .schedContextConfigureDispatch,
   .setThreadCpuAffinityDispatch,
   .notificationSignal, .notificationSignalBound,
   .notificationWait, .endpointReply, .endpointReplyDispatch, .endpointReceiveDual,
   .endpointReceiveDualWithCaps,
   .endpointReplyRecvDispatch, .deschedule, .cancelIpcBlocking,
   .suspendThreadDispatch, .resumeThreadDispatch,
   .setPriorityDispatch, .setMCPriorityDispatch,
   .vspaceMapDispatch, .vspaceUnmapDispatch, .untypedResetDispatch,
   .cspaceDeleteDispatch, .cspaceRevokeDispatch, .lifecycleRetypeDispatch,
   .declassifyDispatch, .declassifySignalDispatch,
   .auditReadDispatch, .auditDrainDispatch]

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
      niName! schedContextUnbindOnCore_crossCoreNonInterference
  | .schedContextBindDispatch =>
      niName! schedContextBind_crossCoreNonInterference
  | .setThreadCpuAffinityDispatch =>
      niName! setThreadCpuAffinityWithMigration_crossCoreNonInterference
  | .schedContextConfigureDispatch =>
      niName! schedContextConfigure_crossCoreNonInterference
  | .notificationSignal => niName! notificationSignalOnCore_crossCoreNonInterference
  | .notificationSignalBound => niName! notificationSignalBoundOnCore_crossCoreNonInterference
  | .notificationWait => niName! notificationWaitOnCore_crossCoreNonInterference
  | .endpointReply => niName! endpointReplyOnCore_crossCoreNonInterference
  | .endpointReplyDispatch =>
      niName! endpointReplyCrossCoreDispatch_crossCoreNonInterference
  | .endpointReceiveDual => niName! endpointReceiveDualOnCore_crossCoreNonInterference
  | .endpointReceiveDualWithCaps =>
      niName! endpointReceiveDualWithCapsOnCore_crossCoreNonInterference
  | .endpointReplyRecvDispatch => niName! endpointReplyRecvOnCore_crossCoreNonInterference
  | .deschedule => niName! descheduleThread_crossCoreNonInterference
  | .cancelIpcBlocking => niName! cancelIpcBlockingOnCore_crossCoreNonInterference
  | .suspendThreadDispatch => niName! suspendThreadOnCore_crossCoreNonInterference
  | .resumeThreadDispatch => niName! resumeThreadOnCore_crossCoreNonInterference
  | .setPriorityDispatch => niName! setPriorityOnCore_crossCoreNonInterference
  | .setMCPriorityDispatch => niName! setMCPriorityOnCore_crossCoreNonInterference
  | .vspaceMapDispatch =>
      niName! vspaceMapFromFrameCap_crossCoreNonInterference
  | .vspaceUnmapDispatch =>
      niName! vspaceUnmapPageWithShootdownAndIcacheBroadcast_crossCoreNonInterference
  | .untypedResetDispatch => niName! untypedResetWithShootdown_crossCoreNonInterference
  | .cspaceDeleteDispatch => niName! cspaceDeleteSlotFinalising_crossCoreNonInterference
  | .cspaceRevokeDispatch => niName! cspaceRevokeCdtFinalising_crossCoreNonInterference
  | .lifecycleRetypeDispatch =>
      niName! lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_crossCoreNonInterference
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

theorem crossCoreNiTheorem_count : CrossCoreTransition.all.length = 32 := by rfl

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

Two entries are a different case and are *not* re-pointed, because their live arm
calls the `…OnCore` transition **directly**:
`notificationSignalBoundCrossCoreDispatch` and `notificationWaitCrossCoreDispatch`
are definitionally `…OnCore … executingCore st`. For those the
`…OnCore` theorem is a statement about the live arm already.

**Being a leg does not stop something being a live arm** (PR #861 review round
8) — but it does not make something one either. `endpointReceiveDualOnCore` was
a third entry of that kind while the `.receive` arm invoked it directly; it is
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
  | .notificationSignalBound => true
  | .notificationWait => true
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
  | .untypedResetDispatch => true
  | .cspaceDeleteDispatch => true
  | .cspaceRevokeDispatch => true
  | .declassifyDispatch => true
  | .declassifySignalDispatch => true
  | .auditReadDispatch => true
  | .auditDrainDispatch => true
  | .lifecycleRetypeDispatch => true

theorem crossCoreTransitionIsLiveArm_count :
    (CrossCoreTransition.all.filter crossCoreTransitionIsLiveArm).length = 25 := by decide

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
  | .notificationSignalBound => some .notificationSignal
  | .notificationWait => some .notificationWait
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
  | .untypedResetDispatch => some .untypedReset
  | .cspaceDeleteDispatch => some .cspaceDelete
  | .cspaceRevokeDispatch => some .cspaceRevoke
  | .declassifyDispatch => some .declassify
  | .declassifySignalDispatch => some .declassifySignal
  | .auditReadDispatch => some .auditRead
  | .auditDrainDispatch => some .auditDrain
  | .lifecycleRetypeDispatch => some .lifecycleRetype

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
  | .notificationSignal => .readOffTheArm "below-API transition; live arm is .notificationSignalBound"
  | .notificationSignalBound =>
      .readOffTheArm "checked `.signal` arm; wrapper definitionally the OnCore call; delegation theorem pending"
  | .notificationWait =>
      .readOffTheArm "checked `.wait` arm; wrapper definitionally the OnCore call; delegation theorem pending"
  | .endpointReply => .readOffTheArm "below-API transition; live arm is .endpointReplyDispatch"
  | .endpointReplyDispatch =>
      .readOffTheArm "checked `.reply` arm calls endpointReplyCrossCoreDispatch; delegation theorem pending"
  | .endpointReceiveDual =>
      .readOffTheArm "below-API transition; live arm is .endpointReceiveDualWithCaps"
  | .endpointReceiveDualWithCaps => .delegationProof .receive syscallDelegates_receive
  | .endpointReplyRecvDispatch =>
      .readOffTheArm "checked `.replyRecv` arm calls endpointReplyRecvOnCore; delegation theorem pending"
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
  | .untypedResetDispatch => .delegationProof .untypedReset syscallDelegates_untypedReset
  | .cspaceDeleteDispatch => .delegationProof .cspaceDelete syscallDelegates_cspaceDelete
  | .cspaceRevokeDispatch => .delegationProof .cspaceRevoke syscallDelegates_cspaceRevoke
  | .declassifyDispatch => .delegationProof .declassify syscallDelegates_declassify
  | .declassifySignalDispatch =>
      .delegationProof .declassifySignal syscallDelegates_declassifySignal
  | .auditReadDispatch => .delegationProof .auditRead syscallDelegates_auditRead
  | .auditDrainDispatch => .delegationProof .auditDrain syscallDelegates_auditDrain
  | .lifecycleRetypeDispatch =>
      .delegationProof .lifecycleRetype syscallDelegates_lifecycleRetype

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
    crossCoreLiveArmDelegationBacked.length = 17 := by decide

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
  | .notificationWait => false
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
  -- WS-BP BP7.1 (slice 3): and the reset, for the unmap's own reason
  | .untypedResetDispatch => false
  -- WS-BP BP7.1 (`v0.36.7`): and the two finalising destroyers, for the same
  -- reason — their teardown is the unmap's own transition
  | .cspaceDeleteDispatch => false
  | .cspaceRevokeDispatch => false
  | .lifecycleRetypeDispatch => true
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

theorem crossCoreTransitionWritesRemote_count :
    (CrossCoreTransition.all.filter crossCoreTransitionWritesRemote).length = 23 := by decide

end SeLe4n.Kernel
