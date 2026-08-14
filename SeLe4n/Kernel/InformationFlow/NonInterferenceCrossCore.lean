/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under the GNU General Public License v3.0 or later.

WS-SM SM8.B — per-core non-interference at the *genuinely* cross-core
transitions.

`NonInterferencePerCore` proves `crossCoreNonInterference` and lifts the
thirty-five single-core operations, every one of which is confined to the boot
core.  That leaves the theorem's interesting direction — a transition running on
core `c'` observed from a different core `c` — without an instantiation at a
transition that actually writes a remote core.  This module supplies them.
-/

import SeLe4n.Kernel.InformationFlow.NonInterferencePerCore
-- WS-SM SM8.B (review round 14): the SM5.I raw-insert home-core atoms
-- (`determineTargetCore_insert_tcb`, `getTcb?_insert_schedContext_eq`) the
-- SchedContext confinement proofs compose.  Cycle-free: this module's closure
-- contains neither NonInterferencePerCore nor this file.
import SeLe4n.Kernel.Scheduler.Operations.PerCoreTickCbsAffinity
import SeLe4n.Kernel.IPC.CrossCore.EndpointReply
import SeLe4n.Kernel.IPC.CrossCore.Cancellation
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallDispatch
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyDispatch
import SeLe4n.Kernel.API
import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCore

/-!
# WS-SM SM8.B — non-interference at the cross-core transitions

Plan `docs/planning/SMP_INFORMATION_FLOW_PLAN.md` §3.3, sub-tasks SM8.B.2 /
SM8.B.3.

## What this module adds that SM6 does not

The SM6 phases already prove per-core non-interference for their own cross-core
transitions — `endpointCallOnCore_call_path_NI_smp`,
`notificationSignalOnCore_NI_smp`, `endpointReplyOnCore_NI_smp` and siblings.
Every one of those is **label-conditional on the per-core half**: they route
through `wakeThread_preserves_projectionOnCore`, whose `hHighThread` hypothesis
says the woken thread is *not observable*.  Under that hypothesis the run-queue
insert is invisible because the filter drops it, on the woken thread's own core
as much as anywhere else.

`crossCoreNonInterference` says something different and strictly stronger for a
*remote* observer: waking a **fully visible** thread on core `c'` is invisible on
core `c ≠ c'`, because core `c`'s six observable slots did not move.  No label
hypothesis is needed for the per-core half at all — only for the shared half,
which is what the object writes touch.

That is the practical SMP guarantee: a core learns nothing from scheduling
activity on another core, whatever the clearances of the threads involved.

## The write-set discipline

A cross-core transition does not run "on a core" in the single-core sense.
`endpointCallOnCore` wakes the receiver on the receiver's home core **and**
deschedules the caller on the caller's own core: two per-core write targets,
in the interesting case two different ones.  So the premise
`crossCoreNonInterference_ofCores` takes is confinement to a *list* of cores
(`observableSlotsConfinedToCores`, `NonInterferencePerCore` §1b), and each
transition here ships an explicit write set **computed from the pre-state**, so
a caller can decide membership rather than being handed an existential.

Each write set is proved sound in the only direction that matters for security:
every core outside it is untouched.  It is deliberately not proved *tight* — a
transition confined to fewer cores than declared is safe, and the wake paths do
collapse to the empty set on the fail-closed arms.

## Sections

* §1 — the per-core scheduler primitives (`enqueueRunnableOnCore`,
  `removeRunnableOnCore`, `wakeThread`, `descheduleThread`) and the
  scheduler-silent object-store steps, which are confined to `[]`.
* §1a — the home-core frame layer: why a write set may name
  `determineTargetCore` at the *pre-state* even though the wake it describes
  happens several object stores later.
* §2 — the SM6.B notification signal and wait.
* §3 — the SM6.A endpoint call (the two-core case).
* §4 — the SM6.C reply.
* §5 — the SM6.E cancellation: the `descheduleThread` primitive and the
  composed `cancelIpcBlockingOnCore` (teardown + home-core removal).
* §5a — the SM5.F priority-inheritance chain walk, and the union that bounds
  the **live** `.call` arm.  The below-API write sets do not bound it on their
  own: `endpointCallCrossCoreDispatch` also runs the donation and the chain
  walk, and the walk re-buckets on each boosted server's *home* core.
* §6 — the non-interference instantiations.
* §7 — coverage, as checkable data.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)
open SeLe4n.Kernel.Lifecycle.Suspend
open SeLe4n.Kernel.PriorityInheritance

-- ============================================================================
-- §1  The per-core scheduler primitives
-- ============================================================================

/-- SM8.B.2: a bare run-queue write is confined to the core it names.

The structural helper the SchedContext proofs compose, rather than re-deriving
the six-field obligation inline each time — which is where a `simp_all` hid the
mid-state home-core problem in the first attempt. -/
theorem setRunQueueOnCore_confinedToCores (st : SystemState) (cc : CoreId)
    (q : SeLe4n.Kernel.RunQueue) :
    observableSlotsConfinedToCores st
      { st with scheduler := st.scheduler.setRunQueueOnCore cc q } [cc] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c hc <;>
    simp only [List.mem_singleton] at hc
  · exact SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ cc c q (fun h => hc h.symm)
  · exact SchedulerState.setRunQueueOnCore_currentOnCore _ cc c q
  · exact SchedulerState.setRunQueueOnCore_activeDomainOnCore _ cc c q
  · exact SchedulerState.setRunQueueOnCore_domainTimeRemainingOnCore _ cc c q
  · exact SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore _ cc c q
  · rfl

/-- SM8.B.2: a **replenish**-queue write is confined to no core at all — the
replenish queue is outside the six observable slots, so it is per-core silent
even on the core it names. -/
theorem setReplenishQueueOnCore_confinedToCores (st : SystemState) (cc : CoreId)
    (q : SeLe4n.Kernel.ReplenishQueue) :
    observableSlotsConfinedToCores st
      { st with scheduler := st.scheduler.setReplenishQueueOnCore cc q } [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c _
  · exact SchedulerState.setReplenishQueueOnCore_runQueueOnCore _ cc c q
  · exact SchedulerState.setReplenishQueueOnCore_currentOnCore _ cc c q
  · exact SchedulerState.setReplenishQueueOnCore_activeDomainOnCore _ cc c q
  · exact SchedulerState.setReplenishQueueOnCore_domainTimeRemainingOnCore _ cc c q
  · exact SchedulerState.setReplenishQueueOnCore_domainScheduleIndexOnCore _ cc c q
  · rfl

/-- SM8.B.2 (PR #861 review round 17): a replenish-queue **purge** writes no
confined slot, at any core.

The named form of the lemma above, for the SchedContext operations' per-core
purges.  The replenish queue is not one of the six confined slots, so the
purge's *target core* does not enter the write set — which is what lets the
round-17 fix reroute all three purge sites without widening any bound. -/
theorem purgeReplenishmentOnCore_confinedToCores (st : SystemState) (cc : CoreId)
    (scId : SeLe4n.SchedContextId) :
    observableSlotsConfinedToCores st
      (SchedContextOps.purgeReplenishmentOnCore st cc scId) [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c _ <;> simp

/-- SM8.B.2: and so does the all-cores sweep — every fold step is the above. -/
theorem purgeReplenishmentFromAllCores_confinedToCores (st : SystemState)
    (scId : SeLe4n.SchedContextId) :
    observableSlotsConfinedToCores st
      (SchedContextOps.purgeReplenishmentFromAllCores st scId) [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c _ <;> simp

/-- SM8.B.2: `enqueueRunnableOnCore` writes core `cc`'s run-queue slot and the
enqueued TCB, and nothing else per-core. -/
theorem enqueueRunnableOnCore_confinedToCores (st : SystemState) (cc : CoreId)
    (tid : SeLe4n.ThreadId) :
    observableSlotsConfinedToCores st (enqueueRunnableOnCore st cc tid) [cc] :=
  ⟨fun c hc => enqueueRunnableOnCore_runQueueOnCore_ne st cc c tid
      (fun h => hc (by simp [h])),
   fun c _ => enqueueRunnableOnCore_currentOnCore st cc tid c,
   fun c _ => enqueueRunnableOnCore_activeDomainOnCore st cc tid c,
   fun c _ => enqueueRunnableOnCore_domainTimeRemainingOnCore st cc tid c,
   fun c _ => enqueueRunnableOnCore_domainScheduleIndexOnCore st cc tid c,
   fun _ _ => by rw [enqueueRunnableOnCore_machineEq]⟩

/-- SM8.B.2: `removeRunnableOnCore` writes core `cc`'s run-queue and current
slots, and nothing else per-core. -/
theorem removeRunnableOnCore_confinedToCores (st : SystemState)
    (tid : SeLe4n.ThreadId) (cc : CoreId) :
    observableSlotsConfinedToCores st (removeRunnableOnCore st tid cc) [cc] :=
  ⟨fun c hc => removeRunnableOnCore_runQueueOnCore_ne st tid cc c (fun h => hc (by simp [h])),
   fun c hc => removeRunnableOnCore_currentOnCore_ne st tid cc c (fun h => hc (by simp [h])),
   fun c _ => removeRunnableOnCore_activeDomainOnCore st tid cc c,
   fun c _ => removeRunnableOnCore_domainTimeRemainingOnCore st tid cc c,
   fun c _ => removeRunnableOnCore_domainScheduleIndexOnCore st tid cc c,
   fun _ _ => by rw [removeRunnableOnCore_machine_eq]⟩

/-- SM8.B.2: **the cross-core wake writes exactly the woken thread's home
core.**  The write set is `[determineTargetCore st tid]` — read off the
pre-state, and *not* the executing core, which is the whole point of SM5.C: a
wake routes to the target's home core, so a signaller on core 0 waking a thread
homed on core 2 writes core 2's run queue and nothing of core 0's or core 1's. -/
theorem wakeThread_confinedToCores (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) :
    observableSlotsConfinedToCores st (wakeThread st tid executingCore).1
      [determineTargetCore st tid] := by
  rw [wakeThread_state_eq_enqueue]
  exact enqueueRunnableOnCore_confinedToCores st (determineTargetCore st tid) tid

/-- SM8.B.2: the wake's dual — `descheduleThread` writes exactly the victim's
home core. -/
theorem descheduleThread_confinedToCores (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) :
    observableSlotsConfinedToCores st (descheduleThread st tid executingCore).1
      [determineTargetCore st tid] := by
  rw [descheduleThread_state_eq]
  exact removeRunnableOnCore_confinedToCores st tid (determineTargetCore st tid)

/-- SM8.B.2: a successful `storeObject` is per-core silent — it writes the
object store and neither the scheduler nor any register bank, so it is confined
to the **empty** core set.  Every cross-core IPC pipeline below is a chain of
these plus one or two scheduler primitives. -/
theorem storeObject_confinedToCores (st st' : SystemState) (oid : SeLe4n.ObjId)
    (obj : KernelObject) (hStep : storeObject oid obj st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (storeObject_scheduler_eq st st' oid obj hStep)
    (storeObject_machine_eq st st' oid obj hStep)

theorem storeTcbIpcStateAndMessage_confinedToCores (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (storeTcbIpcStateAndMessage_scheduler_eq st st' tid ipc msg hStep)
    (storeTcbIpcStateAndMessage_machine_eq st st' tid ipc msg hStep)

theorem storeTcbIpcState_confinedToCores (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (storeTcbIpcState_scheduler_eq st st' tid ipc hStep)
    (storeTcbIpcState_machine_eq st st' tid ipc hStep)

theorem storeTcbIpcState_fromTcb_confinedToCores (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (ipc : ThreadIpcState)
    (hStep : storeTcbIpcState_fromTcb st tid tcb ipc = .ok st') :
    observableSlotsConfinedToCores st st' [] := by
  unfold storeTcbIpcState_fromTcb at hStep
  cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
  | error e => simp [hStore] at hStep
  | ok pair =>
    simp only [hStore] at hStep
    have hEq := Except.ok.inj hStep; subst hEq
    exact storeObject_confinedToCores st pair.2 _ _ hStore

theorem endpointQueuePopHead_confinedToCores (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) {headTcb : TCB}
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, headTcb, st')) :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (endpointQueuePopHead_scheduler_eq endpointId isReceiveQ st st' tid hStep)
    (endpointQueuePopHead_machine_eq endpointId isReceiveQ st st' tid hStep)

theorem endpointQueueEnqueue_confinedToCores (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (st st' : SystemState)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (endpointQueueEnqueue_scheduler_eq endpointId isReceiveQ tid st st' hStep)
    (endpointQueueEnqueue_machine_eq endpointId isReceiveQ tid st st' hStep)

theorem linkServerStashedReply_confinedToCores (caller server : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hStep : SystemState.linkServerStashedReply caller server st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (linkServerStashedReply_scheduler_eq st st' caller server hStep)
    (linkServerStashedReply_machine_eq st st' caller server hStep)

theorem consumeCallerReply_confinedToCores (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hStep : SystemState.consumeCallerReply caller rid st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (SystemState.consumeCallerReply_scheduler_eq st st' caller rid hStep)
    (SystemState.consumeCallerReply_machine_eq st st' caller rid hStep)

theorem linkCallerReply_confinedToCores (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (st st' : SystemState)
    (hStep : SystemState.linkCallerReply caller rid st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (linkCallerReply_scheduler_eq st st' caller rid hStep)
    (linkCallerReply_machine_eq st st' caller rid hStep)

theorem endpointQueueRemoveDual_confinedToCores (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId) (st st' : SystemState)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (endpointQueueRemoveDual_scheduler_eq st st' endpointId isReceiveQ tid hStep)
    (endpointQueueRemoveDual_machine_eq st st' endpointId isReceiveQ tid hStep)

theorem storeTcbReceiveComplete_confinedToCores (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (hStep : storeTcbReceiveComplete st tid msg = .ok st') :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (storeTcbReceiveComplete_scheduler_eq st st' tid msg hStep)
    (storeTcbReceiveComplete_machine_eq st st' tid msg hStep)

theorem cleanupPreReceiveDonationChecked_confinedToCores (st st' : SystemState)
    (receiver : SeLe4n.ThreadId)
    (hStep : cleanupPreReceiveDonationChecked st receiver = .ok st') :
    observableSlotsConfinedToCores st st' [] := by
  have hEq : cleanupPreReceiveDonation st receiver = st' :=
    cleanupPreReceiveDonationChecked_ok_eq_cleanup st st' receiver hStep
  exact observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (hEq ▸ cleanupPreReceiveDonation_scheduler_eq st receiver)
    (hEq ▸ cleanupPreReceiveDonation_machine_eq st receiver)

theorem storeTcbIpcStateAndMessage_fromTcb_confinedToCores (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hStep : storeTcbIpcStateAndMessage_fromTcb st tid tcb ipc msg = .ok st') :
    observableSlotsConfinedToCores st st' [] := by
  unfold storeTcbIpcStateAndMessage_fromTcb at hStep
  split at hStep
  · exact absurd hStep (by simp)
  · next st1 hStore =>
    simp only [Except.ok.injEq] at hStep
    subst hStep
    exact storeObject_confinedToCores st st1 _ _ hStore

-- ============================================================================
-- §1a  The home-core frame layer
-- ============================================================================
--
-- Every write set below names `determineTargetCore st _` at the **pre-state**,
-- but the wake it describes happens several object stores later.  Pushing the
-- target back across those stores is the affinity-stability argument SM6.B makes
-- for one pipeline (`notificationSignalOnCore_remote_wake_preState`); the
-- cross-core IPC transitions need it for four more, so it is factored here into
-- a reusable layer rather than repeated.
--
-- The general fact: a home core is `getTcb?` composed with `cpuAffinity`, so a
-- store preserves it whenever the store preserves that composite — which every
-- IPC-pipeline store does, since none of them is a *migration*.

/-- SM8.B.2: storing a TCB that agrees with the current one on `cpuAffinity`
preserves **every** thread's home core.  The generic form behind the
IPC-pipeline frames: an IPC store rewrites `ipcState`, `pendingMessage` or the
queue links, never the affinity, so it is never a migration. -/
theorem storeObject_tcb_determineTargetCore_eq (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb newTcb : TCB) (x : SeLe4n.ThreadId)
    (hOld : st.getTcb? tid = some tcb)
    (hAff : newTcb.cpuAffinity = tcb.cpuAffinity)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject tid.toObjId (.tcb newTcb) st = .ok ((), st')) :
    determineTargetCore st' x = determineTargetCore st x := by
  -- Stated over the typed accessor (AK7 cascade discipline): the raw store form
  -- is recovered inside the proof, so no caller has to name it.
  have hRaw := (SystemState.getTcb?_eq_some_iff st tid tcb).mp hOld
  refine determineTargetCore_congr st st' x ?_
  by_cases hEq : x.toObjId = tid.toObjId
  · simp [SystemState.getTcb?, hEq, hRaw,
      storeObject_objects_eq st st' tid.toObjId (.tcb newTcb) hObjInv hStore, hAff]
  · simp only [SystemState.getTcb?,
      storeObject_objects_ne st st' tid.toObjId x.toObjId (.tcb newTcb) hEq hObjInv hStore]

/-- SM8.B.2: storing an **endpoint** over an object that is already an endpoint
preserves every thread's home core.  Note there is no disjointness hypothesis
and none is needed: at a *different* id the TCB lookup is framed, and at the
*same* id the lookup fails both before and after (an endpoint is not a TCB), so
both sides read the unbound default. -/
theorem storeObject_endpoint_determineTargetCore_eq (st st' : SystemState)
    (endpointId : SeLe4n.ObjId) (ep ep' : Endpoint) (x : SeLe4n.ThreadId)
    (hPre : st.objects[endpointId]? = some (.endpoint ep))
    (hObjInv : st.objects.invExt)
    (hStore : storeObject endpointId (.endpoint ep') st = .ok ((), st')) :
    determineTargetCore st' x = determineTargetCore st x := by
  refine determineTargetCore_congr st st' x ?_
  by_cases hEq : x.toObjId = endpointId
  · simp only [SystemState.getTcb?, hEq, hPre,
      storeObject_objects_eq st st' endpointId (.endpoint ep') hObjInv hStore]
  · simp only [SystemState.getTcb?,
      storeObject_objects_ne st st' endpointId x.toObjId (.endpoint ep') hEq hObjInv hStore]

/-- SM8.B.2: storing a **SchedContext** preserves every thread's home core.

The `storeObject_endpoint_determineTargetCore_eq` argument verbatim, and for the
same reason it needs no disjointness hypothesis: at a different id the TCB
lookup is framed, and at the *same* id `getTcb?` fails both before and after
(`SystemState.getTcb?` matches only `some (.tcb _)`, and a SchedContext is not a
TCB), so both sides read the unbound default.

Added in PR #861 review round 14 for the SchedContext arms: the reroute through
`determineTargetCore` made them remote writers, and their write sets name the
home core at the *pre*-state while the transitions compute it after this
store. -/
theorem storeObject_schedContext_determineTargetCore_eq (st st' : SystemState)
    (scObjId : SeLe4n.ObjId) (sc sc' : SchedContext) (x : SeLe4n.ThreadId)
    (hPre : st.objects[scObjId]? = some (.schedContext sc))
    (hObjInv : st.objects.invExt)
    (hStore : storeObject scObjId (.schedContext sc') st = .ok ((), st')) :
    determineTargetCore st' x = determineTargetCore st x := by
  refine determineTargetCore_congr st st' x ?_
  by_cases hEq : x.toObjId = scObjId
  · simp only [SystemState.getTcb?, hEq, hPre,
      storeObject_objects_eq st st' scObjId (.schedContext sc') hObjInv hStore]
  · simp only [SystemState.getTcb?,
      storeObject_objects_ne st st' scObjId x.toObjId (.schedContext sc') hEq hObjInv hStore]

-- The raw-`objects.insert` frames these operations need already exist as SM5.I
-- atoms in `Scheduler/Operations/PerCoreTickCbsAffinity.lean`, imported above:
-- `determineTargetCore_insert_tcb` (a TCB insert with unchanged `cpuAffinity`) and
-- `getTcb?_insert_schedContext_eq` (a SchedContext insert leaves every TCB lookup
-- alone).  They are used rather than re-proved here.

/-- SM8.B.2: the `_fromTcb` IPC store is not a migration either. -/
theorem storeTcbIpcStateAndMessage_fromTcb_determineTargetCore_eq (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (x : SeLe4n.ThreadId)
    (hOld : st.getTcb? tid = some tcb)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage_fromTcb st tid tcb ipc msg = .ok st') :
    determineTargetCore st' x = determineTargetCore st x := by
  unfold storeTcbIpcStateAndMessage_fromTcb at hStep
  split at hStep
  · exact absurd hStep (by simp)
  · next st1 hStore =>
    simp only [Except.ok.injEq] at hStep
    subst hStep
    exact storeObject_tcb_determineTargetCore_eq st st1 tid tcb
      { tcb with ipcState := ipc, pendingMessage := msg } x hOld rfl hObjInv hStore

/-- SM8.B.2: a queue-link store is not a migration. -/
theorem storeTcbQueueLinks_determineTargetCore_eq (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId) (x : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    determineTargetCore st' x = determineTargetCore st x := by
  unfold storeTcbQueueLinks at hStep
  split at hStep
  · exact absurd hStep (by simp)
  · next tcb hLk =>
    split at hStep
    · exact absurd hStep (by simp)
    · next st1 hStore =>
      simp only [Except.ok.injEq] at hStep
      subst hStep
      exact storeObject_tcb_determineTargetCore_eq st st1 tid tcb
        (tcbWithQueueLinks tcb prev pprev next) x
        ((SystemState.getTcb?_eq_some_iff st tid tcb).mpr
          (lookupTcb_some_objects st tid tcb hLk)) rfl hObjInv hStore

/-- SM8.B.2: `endpointQueueRemoveDual` is not a migration — the mid-queue splice
rewrites the endpoint, the removed thread's links and its neighbours', never an
affinity.  Composed from the two directions of the transition's own TCB
transport: backward gives affinity agreement where the post-state has a TCB,
forward rules out a TCB appearing or vanishing. -/
theorem endpointQueueRemoveDual_determineTargetCore_eq (st st' : SystemState)
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid x : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    determineTargetCore st' x = determineTargetCore st x := by
  refine determineTargetCore_congr st st' x ?_
  cases hPost : st'.getTcb? x with
  | none =>
    cases hPre : st.getTcb? x with
    | none => simp
    | some tcb =>
      -- A TCB cannot vanish: the forward transport produces one at the same key.
      obtain ⟨tcb', hTcb'⟩ := endpointQueueRemoveDual_tcb_forward st st' endpointId
        isReceiveQ tid x.toObjId tcb hObjInv hStep
        ((SystemState.getTcb?_eq_some_iff st x tcb).mp hPre)
      rw [(SystemState.getTcb?_eq_some_iff st' x tcb').mpr hTcb'] at hPost
      exact absurd hPost (by simp)
  | some tcb' =>
    obtain ⟨tcb, hPreRaw, hAff⟩ := endpointQueueRemoveDual_tcb_cpuAffinity_backward st st'
      endpointId isReceiveQ tid x tcb' hObjInv hStep
      ((SystemState.getTcb?_eq_some_iff st' x tcb').mp hPost)
    rw [(SystemState.getTcb?_eq_some_iff st x tcb).mpr hPreRaw]
    simp [hAff]

/-- SM8.B.2: `storeTcbReceiveComplete` is not a migration — it rewrites the
receiver's `ipcState`, `pendingMessage` and reply stash, never its affinity. -/
theorem storeTcbReceiveComplete_determineTargetCore_eq (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (msg : Option IpcMessage) (x : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbReceiveComplete st tid msg = .ok st') :
    determineTargetCore st' x = determineTargetCore st x := by
  unfold storeTcbReceiveComplete at hStep
  cases hTcb : lookupTcb st tid with
  | none => simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := .ready, pendingMessage := msg, pendingReceiveReply := none }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep; subst hEq
      exact storeObject_tcb_determineTargetCore_eq st pair.2 tid tcb
        { tcb with ipcState := .ready, pendingMessage := msg, pendingReceiveReply := none } x
        ((SystemState.getTcb?_eq_some_iff st tid tcb).mpr
          (lookupTcb_some_objects st tid tcb hTcb)) rfl hObjInv hStore

/-- SM8.B.2: `endpointQueuePopHead` is not a migration either — it rewrites the
endpoint's queue and two threads' link fields, and nothing's affinity. -/
theorem endpointQueuePopHead_determineTargetCore_eq (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (st st' : SystemState) (rTid : SeLe4n.ThreadId) (rTcb : TCB)
    (x : SeLe4n.ThreadId) (hObjInv : st.objects.invExt)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (rTid, rTcb, st')) :
    determineTargetCore st' x = determineTargetCore st x := by
  unfold endpointQueuePopHead at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _
    | reply _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep; revert hStep
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp
      | some headTid =>
        simp only []
        cases hLookup : lookupTcb st headTid with
        | none => simp
        | some headTcb =>
          simp only []
          cases hStore : storeObject endpointId
              (.endpoint (if isReceiveQ
                then { ep with receiveQ := _ } else { ep with sendQ := _ })) st with
          | error e => simp
          | ok pair =>
            have hInv1 : pair.2.objects.invExt :=
              storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
            have hT1 : determineTargetCore pair.2 x = determineTargetCore st x :=
              storeObject_endpoint_determineTargetCore_eq st pair.2 endpointId ep _ x hObj
                hObjInv (by rw [hStore])
            simp only []
            cases hNext : headTcb.queueNext with
            | none =>
              simp only []
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, _, hEq⟩; subst hEq
                rw [storeTcbQueueLinks_determineTargetCore_eq pair.2 st3 headTid none none none
                      x hInv1 hFinal, hT1]
            | some nextTid =>
              simp only []
              cases hLookupNext : lookupTcb pair.2 nextTid with
              | none => simp
              | some nextTcb =>
                simp only []
                cases hLink : storeTcbQueueLinks pair.2 nextTid none
                    (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp
                | ok st2 =>
                  have hInv2 : st2.objects.invExt :=
                    storeTcbQueueLinks_preserves_objects_invExt pair.2 st2 nextTid none
                      (some QueuePPrev.endpointHead) nextTcb.queueNext hInv1 hLink
                  have hT2 : determineTargetCore st2 x = determineTargetCore st x := by
                    rw [storeTcbQueueLinks_determineTargetCore_eq pair.2 st2 nextTid none
                          (some QueuePPrev.endpointHead) nextTcb.queueNext x hInv1 hLink, hT1]
                  simp only []
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, _, hEq⟩; subst hEq
                    rw [storeTcbQueueLinks_determineTargetCore_eq st2 st3 headTid none none
                          none x hInv2 hFinal, hT2]

-- ============================================================================
-- §2  SM6.B — the notification transitions
-- ============================================================================

/-- SM8.B.2: **the cores a cross-core notification signal may write.**
Read off the pre-state: the head waiter's home core if the notification has a
waiter, nothing otherwise (the badge-accumulation path and every fail-closed arm
touch no scheduler slot at all).

`notificationSignalWriteSet_eq_lockSet_waiter` ties this to the *same*
pre-resolution the SM6.B lock set uses, so the declared information-flow write
set and the declared 2PL footprint cannot name different threads. -/
def notificationSignalWriteSet (st : SystemState) (notificationId : SeLe4n.ObjId) :
    List CoreId :=
  match st.getNotification? notificationId with
  | some ntfn =>
      match ntfn.waitingThreads.tail? with
      | some (waiter, _) => [determineTargetCore st waiter]
      | none => []
  | none => []

/-- SM8.B.2 (coherence with the SM6.B lock set): the write set names the home
core of exactly the thread `notificationSignalWaiter?` pre-resolves — the thread
whose TCB write lock the runtime takes. -/
theorem notificationSignalWriteSet_eq_lockSet_waiter (st : SystemState)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (hWaiter : notificationSignalWaiter? st notificationId = some waiter) :
    notificationSignalWriteSet st notificationId = [determineTargetCore st waiter] := by
  unfold notificationSignalWriteSet
  split
  · next ntfn hN =>
    split
    · next headWaiter rest hT =>
      have hResolve : notificationSignalWaiter? st notificationId = some headWaiter := by
        simp only [notificationSignalWaiter?, hN]
        exact SeLe4n.NoDupList.head?_eq_of_tail? hT
      rw [hResolve] at hWaiter
      simp only [Option.some.injEq] at hWaiter
      subst hWaiter
      rfl
    · next hT =>
      have hResolve : notificationSignalWaiter? st notificationId = none := by
        simp only [notificationSignalWaiter?, hN,
          SeLe4n.NoDupList.head?_eq_none_of_tail?_eq_none hT]
      rw [hResolve] at hWaiter; exact absurd hWaiter (by simp)
  · next hN =>
    have hResolve : notificationSignalWaiter? st notificationId = none := by
      simp only [notificationSignalWaiter?, hN]
    rw [hResolve] at hWaiter; exact absurd hWaiter (by simp)

/-- SM8.B.2 (**SM6.B, cross-core**): a notification signal's per-core writes stay
on the head waiter's home core.

The three-step pipeline — store the notification, store the waiter's IPC state,
wake the waiter — contributes `[] ++ [] ++ [home]`: the two object stores are
scheduler-silent and the wake writes exactly `determineTargetCore`.  Pushing the
wake target back through the two stores is the same affinity-stability argument
SM6.B's `notificationSignalOnCore_remote_wake_preState` makes: neither store
touches `cpuAffinity`, and the notification id and the waiter's TCB are distinct
objects (recovered from the store's success, `notification_ne_waiter_of_store`). -/
theorem notificationSignalOnCore_confinedToCores (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) :
    observableSlotsConfinedToCores st
      (notificationSignalOnCore notificationId badge executingCore st).1
      (notificationSignalWriteSet st notificationId) := by
  unfold notificationSignalOnCore notificationSignalWriteSet
  cases hN : st.getNotification? notificationId with
  | none =>
    simp only []
    split <;> exact observableSlotsConfinedToCores_of_eq _ rfl
  | some ntfn =>
    simp only []
    cases hT : ntfn.waitingThreads.tail? with
    | none =>
      simp only []
      split
      · exact observableSlotsConfinedToCores_of_eq _ rfl
      · next st1 hStore => exact storeObject_confinedToCores st st1 _ _ hStore
    | some pair =>
      simp only []
      split
      · exact observableSlotsConfinedToCores_of_eq _ rfl
      · next st1 hStore =>
        split
        · exact observableSlotsConfinedToCores_of_eq _ rfl
        · next st2 hMsg =>
          have hInv' : st1.objects.invExt :=
            storeObject_preserves_objects_invExt st st1 notificationId _ hObjInv hStore
          have hNtfn' := storeObject_objects_eq st st1 notificationId _ hObjInv hStore
          have hNe : notificationId ≠ pair.1.toObjId :=
            notification_ne_waiter_of_store st1 st2 notificationId pair.1 _ .ready _
              hNtfn' hMsg
          have hTarget : determineTargetCore st2 pair.1 = determineTargetCore st pair.1 := by
            rw [storeTcbIpcStateAndMessage_determineTargetCore_eq st1 st2 pair.1 .ready _
                  pair.1 hInv' hMsg,
                storeObject_determineTargetCore_eq st st1 notificationId _ pair.1 hNe
                  hObjInv hStore]
          have hChain := observableSlotsConfinedToCores_trans
            (observableSlotsConfinedToCores_trans
              (storeObject_confinedToCores st st1 _ _ hStore)
              (storeTcbIpcStateAndMessage_confinedToCores st1 st2 pair.1 .ready _ hMsg))
            (wakeThread_confinedToCores st2 pair.1 executingCore)
          rw [hTarget] at hChain
          exact hChain

/-- SM8.B.2 (**SM6.B, cross-core**): a notification *wait* never writes another
core.  The block path removes the caller from its own core's run queue; the
badge-consume path keeps it runnable and writes no scheduler slot at all.  So a
waiter on core 0 is invisible to every observer on cores 1..n outright — there
is no "unless the shared half moved" caveat to discharge on the per-core side. -/
theorem notificationWaitOnCore_confinedToCores (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) (executingCore : CoreId) (st : SystemState) :
    observableSlotsConfinedToCores st
      (notificationWaitOnCore notificationId waiter executingCore st).1 [executingCore] := by
  unfold notificationWaitOnCore
  cases hN : st.getNotification? notificationId with
  | none =>
    simp only []
    split <;> exact observableSlotsConfinedToCores_of_eq _ rfl
  | some ntfn =>
    simp only []
    cases hB : ntfn.pendingBadge with
    | some badge =>
      simp only []
      split
      · exact observableSlotsConfinedToCores_of_eq _ rfl
      · next st1 hStore =>
        split
        · exact observableSlotsConfinedToCores_of_eq _ rfl
        · next st2 hIpc =>
          exact observableSlotsConfinedToCores_widen
            (observableSlotsConfinedToCores_trans
              (storeObject_confinedToCores st st1 _ _ hStore)
              (storeTcbIpcState_confinedToCores st1 st2 waiter .ready hIpc))
    | none =>
      simp only []
      split
      · exact observableSlotsConfinedToCores_of_eq _ rfl
      · next tcb hLk =>
        split
        · exact observableSlotsConfinedToCores_of_eq _ rfl
        · split
          · exact observableSlotsConfinedToCores_of_eq _ rfl
          · next wt' hGuard =>
            split
            · exact observableSlotsConfinedToCores_of_eq _ rfl
            · next st1 hStore =>
              split
              · exact observableSlotsConfinedToCores_of_eq _ rfl
              · next st2 hIpc =>
                exact observableSlotsConfinedToCores_trans
                  (observableSlotsConfinedToCores_trans
                    (storeObject_confinedToCores st st1 _ _ hStore)
                    (storeTcbIpcState_fromTcb_confinedToCores st1 st2 waiter tcb _ hIpc))
                  (removeRunnableOnCore_confinedToCores st2 waiter executingCore)

/-- SM8.B.2: **the cores a bound-aware cross-core signal may write** — the bound
TCB's home core when the badge is delivered directly, otherwise the plain
signal's set.

`boundDeliveryTarget?` is the transition's own pre-state resolution, so the
declared set and the transition name the same TCB. -/
def notificationSignalBoundWriteSet (st : SystemState) (notificationId : SeLe4n.ObjId) :
    List CoreId :=
  match boundDeliveryTarget? st notificationId with
  | some (t, _) => [determineTargetCore st t]
  | none => notificationSignalWriteSet st notificationId

/-- SM8.B.2 (**SM6.B, cross-core** — the *bound* signal, the live `.signal` arm):
a bound-aware signal's per-core writes stay inside
`notificationSignalBoundWriteSet`.

Two shapes:

* **Bound delivery** — dequeue the bound TCB from the endpoint it is blocked on,
  store the badge, **wake it on its home core**: `[] ++ [] ++ [boundHome]`.
  Naming `boundHome` at the pre-state needs the dequeue and the badge store to
  be non-migrations, which is what the two §1a frames added for this path say.
* **Fall-through** — no bound-delivery target, so the transition *is*
  `notificationSignalOnCore` and its own confinement applies verbatim. -/
theorem notificationSignalBoundOnCore_confinedToCores (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) :
    observableSlotsConfinedToCores st
      (notificationSignalBoundOnCore notificationId badge executingCore st).1
      (notificationSignalBoundWriteSet st notificationId) := by
  unfold notificationSignalBoundOnCore notificationSignalBoundWriteSet
  cases hTarget : boundDeliveryTarget? st notificationId with
  | none =>
    simp only []
    exact notificationSignalOnCore_confinedToCores notificationId badge executingCore st hObjInv
  | some pair =>
    obtain ⟨t, epId⟩ := pair
    simp only []
    cases hRemove : endpointQueueRemoveDual epId true t st with
    | error e => exact observableSlotsConfinedToCores_of_eq _ rfl
    | ok u =>
      obtain ⟨_, st1⟩ := u
      simp only []
      have hInv1 : st1.objects.invExt :=
        endpointQueueRemoveDual_preserves_objects_invExt st st1 epId true t hObjInv hRemove
      have hT1 : determineTargetCore st1 t = determineTargetCore st t :=
        endpointQueueRemoveDual_determineTargetCore_eq st st1 epId true t t hObjInv hRemove
      cases hStore : storeTcbReceiveComplete st1 t
          (some { IpcMessage.empty with badge := some badge }) with
      | error e => exact observableSlotsConfinedToCores_of_eq _ rfl
      | ok st2 =>
        have hT2 : determineTargetCore st2 t = determineTargetCore st1 t :=
          storeTcbReceiveComplete_determineTargetCore_eq st1 st2 t _ t hInv1 hStore
        have hChain := observableSlotsConfinedToCores_widen_cons
          (observableSlotsConfinedToCores_trans
            (endpointQueueRemoveDual_confinedToCores epId true t st st1 hRemove)
            (storeTcbReceiveComplete_confinedToCores st1 st2 t _ hStore))
          (wakeThread_confinedToCores st2 t executingCore)
        rw [hT2, hT1] at hChain
        exact hChain

-- ============================================================================
-- §3  SM6.A — the endpoint call
-- ============================================================================

/-- SM8.B.2: **the cores a cross-core endpoint call may write** — the receiver's
home core (when a receiver is waiting, so the call rendezvouses and wakes it)
together with the caller's own core (where the caller blocks).

This is the two-element write set that motivates `observableSlotsConfinedToCores`:
in the interesting case the two are different cores, and no single-core
confinement statement covers the transition.  Both are read from the pre-state,
via SM6.A's own `endpointCallReceiver?` — the same pre-resolution
`lockSet_endpointCall` uses to decide whether the receiver-TCB write lock is in
the footprint, so the declared information-flow write set and the declared 2PL
footprint agree on which receiver is meant. -/
def endpointCallWriteSet (st : SystemState) (endpointId : SeLe4n.ObjId)
    (executingCore : CoreId) : List CoreId :=
  match endpointCallReceiver? st endpointId with
  | some receiver => [determineTargetCore st receiver, executingCore]
  | none => [executingCore]

/-- SM8.B.2 (**the flagship two-core instantiation**): a cross-core endpoint
call's per-core writes stay inside `endpointCallWriteSet`.

The rendezvous path is a six-step pipeline — pop the receive queue, store the
receiver's message, **wake the receiver on its home core**, store the caller's
blocked state, link the stashed reply, **deschedule the caller on its own core**
— contributing `[] ++ [] ++ [receiverHome] ++ [] ++ [] ++ [executingCore]`.  The
`§1a` frame layer is what lets `receiverHome` be named at the *pre-state*: the
pop and the two stores rewrite queue links, an endpoint and IPC fields, never a
`cpuAffinity`, so none of them is a migration.

The blocking path enqueues the caller and deschedules it, writing only
`executingCore`; every fail-closed arm writes nothing. -/
theorem endpointCallOnCore_confinedToCores (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    observableSlotsConfinedToCores st
      (endpointCallOnCore endpointId caller msg executingCore st).1
      (endpointCallWriteSet st endpointId executingCore) := by
  unfold endpointCallOnCore endpointCallWriteSet endpointCallReceiver?
  split
  · exact observableSlotsConfinedToCores_of_eq _ rfl
  · split
    · exact observableSlotsConfinedToCores_of_eq _ rfl
    · cases hEp : st.getEndpoint? endpointId with
      | none =>
        simp only []
        split <;> exact observableSlotsConfinedToCores_of_eq _ rfl
      | some ep =>
        simp only []
        cases hHead : ep.receiveQ.head with
        | none =>
          -- Blocking path: enqueue the caller, store its blocked state,
          -- deschedule it on its own core.
          simp only []
          split
          · exact observableSlotsConfinedToCores_of_eq _ rfl
          · next st1 hEnq =>
            split
            · exact observableSlotsConfinedToCores_of_eq _ rfl
            · next st2 hMsg =>
              exact observableSlotsConfinedToCores_trans
                (observableSlotsConfinedToCores_trans
                  (endpointQueueEnqueue_confinedToCores endpointId false caller st st1 hEnq)
                  (storeTcbIpcStateAndMessage_confinedToCores st1 st2 caller _ _ hMsg))
                (removeRunnableOnCore_confinedToCores st2 caller executingCore)
        | some headRecv =>
          -- Rendezvous path: wake the receiver on its home core, block the caller.
          simp only []
          split
          · exact observableSlotsConfinedToCores_of_eq _ rfl
          · next recvTid recvTcb st1 hPop =>
            split
            · exact observableSlotsConfinedToCores_of_eq _ rfl
            · next st2 hMsgR =>
              split
              · exact observableSlotsConfinedToCores_of_eq _ rfl
              · next st4 hMsgC =>
                split
                · exact observableSlotsConfinedToCores_of_eq _ rfl
                · next st5 hLink =>
                  have hEpObj : st.objects[endpointId]? = some (.endpoint ep) :=
                    (SystemState.getEndpoint?_eq_some_iff st endpointId ep).mp hEp
                  have hPopHead : ep.receiveQ.head = some recvTid := by
                    have h := endpointQueuePopHead_returns_head endpointId true st ep recvTid
                      st1 hEpObj hPop
                    simpa using h
                  have hRecv : recvTid = headRecv := by
                    rw [hHead] at hPopHead; simpa using hPopHead.symm
                  have hInv1 : st1.objects.invExt :=
                    endpointQueuePopHead_preserves_objects_invExt endpointId true st st1
                      recvTid recvTcb hObjInv hPop
                  have hT1 : determineTargetCore st1 recvTid = determineTargetCore st recvTid :=
                    endpointQueuePopHead_determineTargetCore_eq endpointId true st st1
                      recvTid recvTcb recvTid hObjInv hPop
                  have hT2 : determineTargetCore st2 recvTid = determineTargetCore st1 recvTid :=
                    storeTcbIpcStateAndMessage_determineTargetCore_eq st1 st2 recvTid
                      .ready (some msg) recvTid hInv1 hMsgR
                  have hChain := observableSlotsConfinedToCores_trans
                    (observableSlotsConfinedToCores_trans
                      (observableSlotsConfinedToCores_trans
                        (endpointQueuePopHead_confinedToCores endpointId true st st1
                          recvTid hPop)
                        (storeTcbIpcStateAndMessage_confinedToCores st1 st2 recvTid
                          .ready (some msg) hMsgR))
                      (wakeThread_confinedToCores st2 recvTid executingCore))
                    (observableSlotsConfinedToCores_trans
                      (observableSlotsConfinedToCores_trans
                        (storeTcbIpcStateAndMessage_confinedToCores
                          (wakeThread st2 recvTid executingCore).1 st4 caller _ _ hMsgC)
                        (linkServerStashedReply_confinedToCores caller recvTid st4 st5 hLink))
                      (removeRunnableOnCore_confinedToCores st5 caller executingCore))
                  rw [hT2, hT1, hRecv] at hChain
                  exact observableSlotsConfinedToCores_mono (by intro c hc; simpa using hc) hChain

-- ============================================================================
-- §4  SM6.C — the reply transition
-- ============================================================================

/-- SM8.B.2 (**SM6.C, cross-core**): a cross-core reply's per-core writes stay on
the **unblocked caller's** home core.  The replier does not block — it keeps
running on its own core — so unlike the call this is a one-element write set,
and it is a *remote* one whenever the answered caller is homed elsewhere.

The target is a parameter rather than a pre-resolution, so no lock-set coherence
lemma is needed here: the transition and the write set name the same thread by
construction. -/
theorem endpointReplyOnCore_confinedToCores (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) :
    observableSlotsConfinedToCores st
      (endpointReplyOnCore replier target msg executingCore st).1
      [determineTargetCore st target] := by
  unfold endpointReplyOnCore
  split
  · exact observableSlotsConfinedToCores_of_eq _ rfl
  · split
    · exact observableSlotsConfinedToCores_of_eq _ rfl
    · cases hLk : lookupTcb st target with
      | none => simp only []; exact observableSlotsConfinedToCores_of_eq _ rfl
      | some tcb =>
        simp only []
        split
        · next epId replyTarget hIpc =>
          split
          · exact observableSlotsConfinedToCores_of_eq _ rfl
          · next expected hSome =>
            split
            · exact observableSlotsConfinedToCores_of_eq _ rfl
            · next st1 hStore =>
              have hOld : st.getTcb? target = some tcb :=
                (SystemState.getTcb?_eq_some_iff st target tcb).mpr
                  (lookupTcb_some_objects st target tcb hLk)
              have hT1 : determineTargetCore st1 target = determineTargetCore st target :=
                storeTcbIpcStateAndMessage_fromTcb_determineTargetCore_eq st st1 target tcb
                  .ready (some msg) target hOld hObjInv hStore
              have hPre := observableSlotsConfinedToCores_trans
                (storeTcbIpcStateAndMessage_fromTcb_confinedToCores st st1 target tcb
                  .ready (some msg) hStore)
                (wakeThread_confinedToCores st1 target executingCore)
              rw [hT1] at hPre
              split
              · exact hPre
              · next rid hReply =>
                split
                · next unit st2 hConsume =>
                  exact observableSlotsConfinedToCores_trans hPre
                    (consumeCallerReply_confinedToCores _ st2 target rid hConsume)
                · exact observableSlotsConfinedToCores_of_eq _ rfl
        · exact observableSlotsConfinedToCores_of_eq _ rfl

-- ============================================================================
-- §4a  SM6.C — the receive leg, and the composed `replyRecv`
-- ============================================================================

/-- SM8.B.2: **the cores a cross-core endpoint receive may write** — the woken
sender's home core on a rendezvous, the receiver's own core when it blocks.

Read from the pre-state through the same `sendQ.head` the transition resolves,
so the declared set and the transition name the same sender.  The two arms are
genuinely exclusive: a receive that rendezvouses does not block, and a receive
that blocks wakes nobody. -/
def endpointReceiveDualWriteSet (st : SystemState) (endpointId : SeLe4n.ObjId)
    (executingCore : CoreId) : List CoreId :=
  match st.getEndpoint? endpointId with
  | some ep =>
      match ep.sendQ.head with
      | some sender => [determineTargetCore st sender]
      | none => [executingCore]
  | none => []

/-- SM8.B.2 (**SM6.C, cross-core** — the `replyRecv` receive leg): a cross-core
endpoint receive's per-core writes stay inside `endpointReceiveDualWriteSet`.

Three shapes, all covered:

* **`blockedOnSend` rendezvous** — pop the send queue, mark the sender `.ready`,
  **wake it on its home core**, store the receiver's message:
  `[] ++ [] ++ [senderHome] ++ []`.  The §1a frame layer is what lets
  `senderHome` be named at the pre-state.
* **`blockedOnCall` rendezvous** — the caller becomes `.blockedOnReply` and is
  deliberately *not* woken (the Call contract), so this path writes no core at
  all and is covered by the declared set through the append.
* **Block path** — return any donated SchedContext, enqueue on the receive
  queue, stash the server's reply object, then deschedule the receiver on **its
  own** core: `[executingCore]`.

Every fail-closed arm returns the pre-state. -/
theorem endpointReceiveDualOnCore_confinedToCores (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (executingCore : CoreId) (st : SystemState) (hObjInv : st.objects.invExt) :
    observableSlotsConfinedToCores st
      (endpointReceiveDualOnCore endpointId receiver replyId executingCore st).1
      (endpointReceiveDualWriteSet st endpointId executingCore) := by
  unfold endpointReceiveDualOnCore endpointReceiveDualWriteSet
  cases hEp : st.getEndpoint? endpointId with
  | none =>
    simp only []
    split <;> exact observableSlotsConfinedToCores_of_eq _ rfl
  | some ep =>
    simp only []
    cases hHead : ep.sendQ.head with
    | none =>
      -- Block path: every step is scheduler-silent until the receiver is
      -- descheduled on its own core.
      simp only []
      split
      · exact observableSlotsConfinedToCores_of_eq _ rfl
      · next stClean hClean =>
        split
        · exact observableSlotsConfinedToCores_of_eq _ rfl
        · next st1 hEnq =>
          have hPre := observableSlotsConfinedToCores_trans
            (cleanupPreReceiveDonationChecked_confinedToCores st stClean receiver hClean)
            (endpointQueueEnqueue_confinedToCores endpointId true receiver stClean st1 hEnq)
          split
          · exact observableSlotsConfinedToCores_of_eq _ rfl
          · next st2 hIpc =>
            have hPre2 := observableSlotsConfinedToCores_trans hPre
              (storeTcbIpcState_confinedToCores st1 st2 receiver _ hIpc)
            split
            · exact observableSlotsConfinedToCores_widen_cons hPre2
                (removeRunnableOnCore_confinedToCores st2 receiver executingCore)
            · next rTcb hTcb =>
              split
              · split
                · exact observableSlotsConfinedToCores_of_eq _ rfl
                · next _ st3 hStash =>
                  exact observableSlotsConfinedToCores_widen_cons
                    (observableSlotsConfinedToCores_trans hPre2
                      (storeObject_confinedToCores st2 st3 _ _ hStash))
                    (removeRunnableOnCore_confinedToCores st3 receiver executingCore)
              · exact observableSlotsConfinedToCores_of_eq _ rfl
    | some senderHead =>
      simp only []
      split
      · exact observableSlotsConfinedToCores_of_eq _ rfl
      · next sender senderTcb st1 hPop =>
        have hEpObj : st.objects[endpointId]? = some (.endpoint ep) :=
          (SystemState.getEndpoint?_eq_some_iff st endpointId ep).mp hEp
        have hPopHead : ep.sendQ.head = some sender := by
          have h := endpointQueuePopHead_returns_head endpointId false st ep sender st1
            hEpObj hPop
          simpa using h
        have hSender : sender = senderHead := by
          rw [hHead] at hPopHead; simpa using hPopHead.symm
        have hInv1 : st1.objects.invExt :=
          endpointQueuePopHead_preserves_objects_invExt endpointId false st st1
            sender senderTcb hObjInv hPop
        have hT1 : determineTargetCore st1 sender = determineTargetCore st sender :=
          endpointQueuePopHead_determineTargetCore_eq endpointId false st st1
            sender senderTcb sender hObjInv hPop
        have hPopConf := endpointQueuePopHead_confinedToCores endpointId false st st1
          sender hPop
        split
        · -- `blockedOnCall` sender: recorded as `.blockedOnReply`, never woken.
          rw [if_pos rfl]
          split
          · exact observableSlotsConfinedToCores_of_eq _ rfl
          · next st2 hIpc =>
            split
            · exact observableSlotsConfinedToCores_of_eq _ rfl
            · next rid =>
              split
              · exact observableSlotsConfinedToCores_of_eq _ rfl
              · next st3 hLink =>
                split
                · next st4 hMsg =>
                  exact observableSlotsConfinedToCores_widen_any
                    (observableSlotsConfinedToCores_trans
                      (observableSlotsConfinedToCores_trans hPopConf
                        (storeTcbIpcStateAndMessage_confinedToCores st1 st2 sender _ _ hIpc))
                      (observableSlotsConfinedToCores_trans
                        (linkCallerReply_confinedToCores sender rid st2 st3 hLink)
                        (storeTcbIpcStateAndMessage_confinedToCores st3 st4 receiver _ _ hMsg)))
                · exact observableSlotsConfinedToCores_of_eq _ rfl
        · -- `blockedOnSend` sender: woken on its own home core.
          rw [if_neg (by simp)]
          split
          · exact observableSlotsConfinedToCores_of_eq _ rfl
          · next st2 hReady =>
            have hT2 : determineTargetCore st2 sender = determineTargetCore st1 sender :=
              storeTcbIpcStateAndMessage_determineTargetCore_eq st1 st2 sender
                .ready none sender hInv1 hReady
            split
            · next st3 hMsg =>
              have hChain := observableSlotsConfinedToCores_trans
                (observableSlotsConfinedToCores_trans hPopConf
                  (storeTcbIpcStateAndMessage_confinedToCores st1 st2 sender .ready none hReady))
                (observableSlotsConfinedToCores_trans
                  (wakeThread_confinedToCores st2 sender executingCore)
                  (storeTcbIpcStateAndMessage_confinedToCores
                    (wakeThread st2 sender executingCore).1 st3 receiver _ _ hMsg))
              rw [hT2, hT1, hSender] at hChain
              exact observableSlotsConfinedToCores_mono (by intro c hc; simpa using hc) hChain
            · exact observableSlotsConfinedToCores_of_eq _ rfl

/-- SM8.B.2: **the cores a cross-core `replyRecv` may write** — the answered
caller's home core from the reply leg, plus whatever the receive leg writes at
the state the reply leg leaves behind.

Like `endpointCallDispatchChainWriteSet` this mirrors the transition's own
control flow rather than guessing: the receive leg runs at `st1`, the reply's
post-state, so its write set is read there.  Reading it at `st` would be wrong
for the same reason the call's chain leg cannot be read at `st` — the reply
unblocks a thread, which can change which sender heads the send queue. -/
def endpointReplyRecvWriteSet (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState) : List CoreId :=
  determineTargetCore st replyTarget ::
    (match endpointReplyOnCore receiver replyTarget msg executingCore st with
     | (st1, .ok _) => endpointReceiveDualWriteSet st1 endpointId executingCore
     | (_, .error _) => [])

/-- SM8.B.2 (**SM6.C, cross-core** — the composed `replyRecv`): both legs
together stay inside `endpointReplyRecvWriteSet`.

`endpointReplyRecvOnCore` is all-or-nothing: a failed leg returns the pre-state,
so only the both-succeed path writes anything, and there it is exactly the reply
leg's target home core followed by the receive leg's set at the intermediate
state.  The receive leg's `objects.invExt` premise is discharged from the reply
leg's own preservation theorem rather than assumed. -/
theorem endpointReplyRecvOnCore_confinedToCores (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (replyId : Option SeLe4n.ReplyId) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) :
    observableSlotsConfinedToCores st
      (endpointReplyRecvOnCore endpointId receiver replyTarget msg replyId executingCore st).1
      (endpointReplyRecvWriteSet endpointId receiver replyTarget msg executingCore st) := by
  unfold endpointReplyRecvOnCore endpointReplyRecvWriteSet
  have hReply := endpointReplyOnCore_confinedToCores receiver replyTarget msg executingCore st
    hObjInv
  have hInv1 : (endpointReplyOnCore receiver replyTarget msg executingCore st).1.objects.invExt :=
    endpointReplyOnCore_preserves_objects_invExt receiver replyTarget msg executingCore st hObjInv
  cases hRep : endpointReplyOnCore receiver replyTarget msg executingCore st with
  | mk st1 res =>
    rw [hRep] at hReply hInv1
    cases res with
    | error e => simp only []; exact observableSlotsConfinedToCores_of_eq _ rfl
    | ok replySgi =>
      simp only []
      have hRecv := endpointReceiveDualOnCore_confinedToCores endpointId receiver replyId
        executingCore st1 hInv1
      cases hRcv : endpointReceiveDualOnCore endpointId receiver replyId executingCore st1 with
      | mk st2 res2 =>
        rw [hRcv] at hRecv
        cases res2 with
        | error e => simp only []; exact observableSlotsConfinedToCores_of_eq _ rfl
        | ok pair =>
          rcases pair with ⟨_, recvSgi⟩
          simp only []
          have h := observableSlotsConfinedToCores_trans hReply hRecv
          simpa using h

-- ============================================================================
-- §5  SM6.E — the cancellation transition
-- ============================================================================

/-- SM8.B.2 (**SM6.E, cross-core**): the cancellation mechanism is
`descheduleThread`, whose confinement §1 proves — it writes only the victim's
**home** core, not the core running the cancellation.  This restates that at the
SM6.E name so the coverage list below reads off one theorem per sub-phase: a
`tcbSuspend` issued on core 0 against a victim homed on core 2 is invisible to
observers on cores 1 and 3 outright. -/
theorem cancellationCrossCore_confinedToCores (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) :
    observableSlotsConfinedToCores st (descheduleThread st tid executingCore).1
      [determineTargetCore st tid] :=
  descheduleThread_confinedToCores st tid executingCore

/-- SM8.B.2: the SM6.E object-level teardown is per-core **silent** — it rewrites
the victim's IPC fields, the endpoint/notification queues it sat in, and its
reply link, and touches neither the scheduler nor any register bank.

The `machine` half is `cancelIpcBlocking_machine_eq`, added beside the
long-standing `cancelIpcBlocking_scheduler_eq` for this consumer: per-core
confinement reads the register banks as well as the scheduler slots, so a
scheduler frame alone never bounded the teardown's observable writes. -/
theorem cancelIpcBlocking_confinedToCores (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) :
    observableSlotsConfinedToCores st (cancelIpcBlocking st tid tcb) [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (cancelIpcBlocking_scheduler_eq st tid tcb) (cancelIpcBlocking_machine_eq st tid tcb)

/-- SM8.B.2 (**SM6.E, the composed cancellation**): `cancelIpcBlockingOnCore`
writes only the victim's **home** core — not the core running the cancellation,
and not any core the victim's endpoint or notification neighbours are homed on.

`[] ++ [home]`: the teardown contributes nothing per-core, the home-core removal
contributes one core.  Unlike the wake pipelines this needs no pushback through
the §1a frame layer, because `cancelIpcBlockingOnCore` reads its home core from
the pre-state itself. -/
theorem cancelIpcBlockingOnCore_confinedToCores (victim : SeLe4n.ThreadId) (tcb : TCB)
    (executingCore : CoreId) (st : SystemState) :
    observableSlotsConfinedToCores st
      (cancelIpcBlockingOnCore victim tcb executingCore st).1
      [determineTargetCore st victim] :=
  observableSlotsConfinedToCores_trans
    (cancelIpcBlocking_confinedToCores st victim tcb)
    (removeRunnableOnCore_confinedToCores (cancelIpcBlocking st victim tcb) victim
      (determineTargetCore st victim))

-- ============================================================================
-- §5a  SM5.F — the priority-inheritance chain walk
-- ============================================================================
--
-- The below-API transitions above are *not* the whole live picture.  The live
-- `.call` arm is `endpointCallCrossCoreDispatch`, which runs the transition and
-- then `applyCallDonation` + `propagatePipChainCrossCore`; the chain walk
-- re-buckets each boosted server's run queue **on that server's home core**, so
-- it can write cores the endpoint call's own write set does not name.
--
-- Leaving that out would make any claim about the live dispatch's write set
-- false, so the chain walk gets a write set of its own, by the same discipline:
-- computed from the pre-state, mirroring the transition's own recursion.

/-- SM8.B.2: a PIP re-bucketing writes core `c`'s run queue and the boosted
TCB, and nothing else per-core. -/
theorem updatePipBoostOnCore_confinedToCores (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) :
    observableSlotsConfinedToCores st (updatePipBoostOnCore st c tid) [c] := by
  refine ⟨fun c' hc => updatePipBoostOnCore_runQueueOnCore_ne st c c' tid
            (fun h => hc (by simp [h])),
          fun c' _ => updatePipBoostOnCore_currentOnCore st c c' tid, ?_, ?_, ?_, ?_⟩
  all_goals intro c' _
  all_goals simp only [updatePipBoostOnCore]
  all_goals repeat' split
  all_goals first
    | rfl
    | simp only [SchedulerState.setRunQueueOnCore_activeDomainOnCore,
        SchedulerState.setRunQueueOnCore_domainTimeRemainingOnCore,
        SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore]

/-- SM8.B.2: one chain step writes exactly the boosted thread's home core. -/
theorem pipBoostWithWake_confinedToCores (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) :
    observableSlotsConfinedToCores st (pipBoostWithWake st tid executingCore).1
      [determineTargetCore st tid] :=
  updatePipBoostOnCore_confinedToCores st (determineTargetCore st tid) tid

/-- SM8.B.2: **the cores a cross-core PIP chain walk may write** — the home core
of every member the walk reaches, computed from the pre-state by mirroring the
walk's own fuel recursion.  The state is threaded exactly as
`propagatePipChainCrossCore` threads it, so the two agree member for member. -/
def pipChainWriteSet (st : SystemState) (startTid : SeLe4n.ThreadId)
    (executingCore : CoreId) : Nat → List CoreId
  | 0 => []
  | fuel + 1 =>
      determineTargetCore st startTid ::
        (match blockingServer st startTid with
         | some nextServer =>
             pipChainWriteSet (pipBoostWithWake st startTid executingCore).1 nextServer
               executingCore fuel
         | none => [])

/-- SM8.B.2 (**SM5.F, cross-core**): the chain walk's per-core writes stay inside
`pipChainWriteSet`.  By induction on the fuel, composing one
`pipBoostWithWake_confinedToCores` per step. -/
theorem propagatePipChainCrossCore_confinedToCores (executingCore : CoreId) :
    ∀ (fuel : Nat) (st : SystemState) (startTid : SeLe4n.ThreadId),
      observableSlotsConfinedToCores st
        (propagatePipChainCrossCore st startTid executingCore fuel).1
        (pipChainWriteSet st startTid executingCore fuel)
  | 0, st, _ => observableSlotsConfinedToCores_of_eq _ rfl
  | fuel + 1, st, startTid => by
      rw [propagatePipChainCrossCore_step]
      simp only [pipChainWriteSet]
      cases hNext : blockingServer st startTid with
      | none =>
        exact pipBoostWithWake_confinedToCores st startTid executingCore
      | some nextServer =>
        exact observableSlotsConfinedToCores_trans
          (pipBoostWithWake_confinedToCores st startTid executingCore)
          (propagatePipChainCrossCore_confinedToCores executingCore fuel
            (pipBoostWithWake st startTid executingCore).1 nextServer)

/-- SM8.B.2: SchedContext donation is per-core silent — it rewrites bindings in
the object store and, at most, the replenishment queue, which SM8.A's
`onCore_perCore_independence` puts outside the observer's read set entirely. -/
theorem applyCallDonation_confinedToCores (st st' : SystemState)
    (callerVtid receiverVtid : SeLe4n.ValidThreadId)
    (hStep : applyCallDonation st callerVtid receiverVtid = .ok st') :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (applyCallDonation_scheduler_eq st callerVtid receiverVtid st' hStep)
    (applyCallDonation_machine_eq st callerVtid receiverVtid st' hStep)

/-- SM8.B.2: **the cores the live cross-core `.call` may write.**

`endpointCallCrossCoreDispatch` is not just `endpointCallOnCore`: it runs the
transition (in its WithCaps form), then `applyCallDonation`, then
`propagatePipChainCrossCore`.  The donation is per-core silent, but the chain
walk re-buckets each boosted server's run queue on that server's **home** core,
which the endpoint call's own write set does not name.  A claim about the live
dispatch has to be made against the union — anything narrower is false.

**The chain leg is not computable from the pre-state, and this signature says
so.**  The live walk is `propagatePipChainCrossCore st'' receiverTid`: it starts
at the *resolved receiver*, not the caller, and runs at the *post-donation*
state, not `st`.  Both matter — the call blocks the caller on reply and the
donation rewrites SchedContext bindings, so `blockingServer` at `st''` is
genuinely not `blockingServer` at `st`, and a pre-state walk from the caller
would name a different chain.  An earlier form of this definition did exactly
that and was wrong (PR #861 review).

So `chainState` and `chainStart` are explicit parameters rather than something
this definition pretends to recover: instantiate them at the post-donation state
and the receiver `endpointCallReceiver? st endpointId` resolves.  The
`pipChainWriteSet` leg is then sound by
`propagatePipChainCrossCore_confinedToCores` at that state. -/
def endpointCallLiveWriteSet (st : SystemState) (endpointId : SeLe4n.ObjId)
    (executingCore : CoreId) (chainState : SystemState)
    (chainStart : SeLe4n.ThreadId) : List CoreId :=
  endpointCallWriteSet st endpointId executingCore
    ++ pipChainWriteSet chainState chainStart executingCore
        chainState.objectIndex.length

/-- SM8.B.2: the live write set contains the below-API one, so a core outside it
is outside both.  The composition rule that makes the union the right premise. -/
theorem endpointCallWriteSet_subset_live (st : SystemState) (endpointId : SeLe4n.ObjId)
    (executingCore : CoreId) (chainState : SystemState) (chainStart : SeLe4n.ThreadId)
    (c : CoreId)
    (h : c ∉ endpointCallLiveWriteSet st endpointId executingCore chainState chainStart) :
    c ∉ endpointCallWriteSet st endpointId executingCore :=
  fun hm => h (List.mem_append.mpr (Or.inl hm))

theorem pipChainWriteSet_subset_live (st : SystemState) (endpointId : SeLe4n.ObjId)
    (executingCore : CoreId) (chainState : SystemState) (chainStart : SeLe4n.ThreadId)
    (c : CoreId)
    (h : c ∉ endpointCallLiveWriteSet st endpointId executingCore chainState chainStart) :
    c ∉ pipChainWriteSet chainState chainStart executingCore
          chainState.objectIndex.length :=
  fun hm => h (List.mem_append.mpr (Or.inr hm))

/-- SM8.B.2: **the composition rule for the live `.call` legs.**

Read the signature literally: `stTrans` and `stDon` are *arbitrary* states and
`hTrans` / `hDonation` are *hypotheses about them*.  This is a composition
lemma; on its own it establishes nothing about `endpointCallCrossCoreDispatch`.

It is no longer the end of the story.  §5b below discharges those premises from
an actual dispatch result — `endpointCallCrossCoreDispatch_confinedToCores`,
whose write set mirrors the dispatch's own control flow and instantiates this
rule at the resolved receiver and the post-donation state.  This theorem is what
that one composes with. -/
theorem endpointCallLive_confinedToCores (st stTrans stDon : SystemState)
    (endpointId : SeLe4n.ObjId) (executingCore : CoreId) (chainStart : SeLe4n.ThreadId)
    (hTrans : observableSlotsConfinedToCores st stTrans
      (endpointCallWriteSet st endpointId executingCore))
    (hDonation : observableSlotsConfinedToCores stTrans stDon []) :
    observableSlotsConfinedToCores st
      (propagatePipChainCrossCore stDon chainStart executingCore
        stDon.objectIndex.length).1
      (endpointCallLiveWriteSet st endpointId executingCore stDon chainStart) :=
  observableSlotsConfinedToCores_trans
    (observableSlotsConfinedToCores_mono
      (by intro c hc; simpa using hc)
      (observableSlotsConfinedToCores_trans hTrans hDonation))
    (propagatePipChainCrossCore_confinedToCores executingCore
      stDon.objectIndex.length stDon chainStart)

-- ============================================================================
-- §5b  The live `.call` arm itself
-- ============================================================================
--
-- §5a bounds the legs.  This section bounds `endpointCallCrossCoreDispatch` —
-- the function the live `.call` syscall arm actually calls — by reducing it to
-- its own intermediate states rather than taking them as parameters.

/-- SM8.B.2: IPC capability transfer is per-core silent.  It rewrites the
receiver's CNode and the CDT, never a run queue and never a register bank, so it
contributes nothing to the cross-core `.call`'s write set. -/
theorem ipcUnwrapCaps_confinedToCores (msg : IpcMessage)
    (senderRoot receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
             = .ok (summary, st')) :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (ipcUnwrapCaps_preserves_scheduler msg senderRoot receiverRoot slotBase grantRight
      st st' summary hStep)
    (ipcUnwrapCaps_preserves_machine msg senderRoot receiverRoot slotBase grantRight
      st st' summary hStep)

/-- SM8.B.2: the WithCaps call leaves the bare call's run queues in place — every
arm either *is* the bare call's post-state or is that state after an
`ipcUnwrapCaps`, which preserves the scheduler. -/
theorem endpointCallWithCapsOnCore_scheduler_eq (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage) (endpointRights : AccessRightSet)
    (callerCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) :
    (endpointCallWithCapsOnCore endpointId caller msg endpointRights callerCspaceRoot
        receiverSlotBase executingCore st).1.scheduler
      = (endpointCallOnCore endpointId caller msg executingCore st).1.scheduler := by
  unfold endpointCallWithCapsOnCore
  cases hCall : endpointCallOnCore endpointId caller msg executingCore st with
  | mk stCall res =>
    cases res with
    | error e => rfl
    | ok sgi =>
      simp only []
      repeat' split
      all_goals first
        | rfl
        | (rename_i h; exact ipcUnwrapCaps_preserves_scheduler _ _ _ _ _ _ _ _ h)

/-- SM8.B.2: and the register banks, by the same case analysis. -/
theorem endpointCallWithCapsOnCore_machine_eq (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage) (endpointRights : AccessRightSet)
    (callerCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) :
    (endpointCallWithCapsOnCore endpointId caller msg endpointRights callerCspaceRoot
        receiverSlotBase executingCore st).1.machine
      = (endpointCallOnCore endpointId caller msg executingCore st).1.machine := by
  unfold endpointCallWithCapsOnCore
  cases hCall : endpointCallOnCore endpointId caller msg executingCore st with
  | mk stCall res =>
    cases res with
    | error e => rfl
    | ok sgi =>
      simp only []
      repeat' split
      all_goals first
        | rfl
        | (rename_i h; exact ipcUnwrapCaps_preserves_machine _ _ _ _ _ _ _ _ h)

/-- SM8.B.2: the **WithCaps** cross-core call — the form the live dispatch calls
— is confined to the bare call's write set.  The extra leg is `ipcUnwrapCaps`,
which by the lemma above writes no core at all, so the two forms declare the
same per-core footprint.

Proved through the two frames rather than by re-walking the WithCaps branch
tree: confinement reads only `scheduler` and the register banks, and on both of
those the WithCaps post-state *is* the bare call's. -/
theorem endpointCallWithCapsOnCore_confinedToCores (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage) (endpointRights : AccessRightSet)
    (callerCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) (hObjInv : st.objects.invExt) :
    observableSlotsConfinedToCores st
      (endpointCallWithCapsOnCore endpointId caller msg endpointRights callerCspaceRoot
        receiverSlotBase executingCore st).1
      (endpointCallWriteSet st endpointId executingCore) := by
  have h := observableSlotsConfinedToCores_trans
    (endpointCallOnCore_confinedToCores endpointId caller msg executingCore st hObjInv)
    (observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
      (endpointCallWithCapsOnCore_scheduler_eq endpointId caller msg endpointRights
        callerCspaceRoot receiverSlotBase executingCore st)
      (endpointCallWithCapsOnCore_machine_eq endpointId caller msg endpointRights
        callerCspaceRoot receiverSlotBase executingCore st))
  simpa using h

/-- SM8.B.2: **the chain leg the live `.call` actually walks**, recovered from
the pre-state by mirroring `endpointCallCrossCoreDispatch`'s own control flow —
same receiver resolution, same WithCaps call, same `applyCallDonation` — so the
walk is keyed on the *resolved receiver* at the *post-donation* state, which is
where the dispatch keys it.  Every arm on which the dispatch does not walk a
chain returns `[]`. -/
def endpointCallDispatchChainWriteSet
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet) (callerCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId)
    (st : SystemState) : List CoreId :=
  let maybeReceiver := match st.getEndpoint? endpointId with
    | some ep => ep.receiveQ.head
    | none    => none
  match endpointCallWithCapsOnCore endpointId caller msg endpointRights callerCspaceRoot
      receiverSlotBase executingCore st with
  | (_, .error _) => []
  | (st', .ok _) =>
      match maybeReceiver with
      | some receiverTid =>
        match SeLe4n.ThreadId.toValid? caller, SeLe4n.ThreadId.toValid? receiverTid with
        | some callerV, some receiverV =>
          match applyCallDonation st' callerV receiverV with
          | .error _ => []
          | .ok st'' =>
              pipChainWriteSet st'' receiverTid executingCore st''.objectIndex.length
        | _, _ => []
      | none => []

/-- SM8.B.2: **the cores the live cross-core `.call` may write** — the endpoint
call's own two-core set, plus the chain the dispatch really walks.  A function of
the dispatch's own arguments, so it can be evaluated at a call site rather than
supplied by hand. -/
def endpointCallDispatchWriteSet
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet) (callerCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId)
    (st : SystemState) : List CoreId :=
  endpointCallWriteSet st endpointId executingCore
    ++ endpointCallDispatchChainWriteSet endpointId caller msg endpointRights
        callerCspaceRoot receiverSlotBase executingCore st

/-- SM8.B.2 (**the live `.call` bound**): `endpointCallCrossCoreDispatch` — the
function `API.dispatchWithCap`'s `.call` arm routes through — writes no core
outside `endpointCallDispatchWriteSet`.

This is the theorem the composition rule §5a was missing.  The proof splits on
exactly the scrutinees the dispatch splits on, so each branch's write set is the
one that branch's states justify: the fail-closed arms and the no-receiver arm
stop at the WithCaps post-state (`endpointCallWriteSet`), and the rendezvous arm
composes WithCaps, the per-core-silent donation and the chain walk at the
post-donation state — `endpointCallLive_confinedToCores` instantiated at the
receiver `ep.receiveQ.head` and the state `applyCallDonation` returns. -/
theorem endpointCallCrossCoreDispatch_confinedToCores (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage) (endpointRights : AccessRightSet)
    (callerCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) (hObjInv : st.objects.invExt) :
    observableSlotsConfinedToCores st
      (endpointCallCrossCoreDispatch endpointId caller msg endpointRights callerCspaceRoot
        receiverSlotBase executingCore st).1
      (endpointCallDispatchWriteSet endpointId caller msg endpointRights callerCspaceRoot
        receiverSlotBase executingCore st) := by
  have hCaps := endpointCallWithCapsOnCore_confinedToCores endpointId caller msg
    endpointRights callerCspaceRoot receiverSlotBase executingCore st hObjInv
  -- A core outside the union is outside the endpoint-call leg, which is what
  -- every arm short of the full rendezvous needs.
  have hWiden : ∀ (stPost : SystemState) (extra : List CoreId),
      observableSlotsConfinedToCores st stPost
        (endpointCallWriteSet st endpointId executingCore) →
      observableSlotsConfinedToCores st stPost
        (endpointCallWriteSet st endpointId executingCore ++ extra) :=
    fun _ _ h => observableSlotsConfinedToCores_mono
      (fun _ hc => List.mem_append.mpr (Or.inl hc)) h
  unfold endpointCallCrossCoreDispatch endpointCallDispatchWriteSet
    endpointCallDispatchChainWriteSet
  cases hWith : endpointCallWithCapsOnCore endpointId caller msg endpointRights
      callerCspaceRoot receiverSlotBase executingCore st with
  | mk stWith res =>
    rw [hWith] at hCaps
    cases res with
    | error e => simp only []; exact hWiden _ _ hCaps
    | ok pair =>
      rcases pair with ⟨summary, sgi⟩
      simp only []
      cases hEp : st.getEndpoint? endpointId with
      | none => simp only []; exact hWiden _ _ hCaps
      | some ep =>
        simp only []
        cases hHead : ep.receiveQ.head with
        | none => simp only []; exact hWiden _ _ hCaps
        | some receiverTid =>
          simp only []
          cases hCallerV : SeLe4n.ThreadId.toValid? caller with
          | none => simp only []; exact hWiden _ _ hCaps
          | some callerV =>
            cases hRecvV : SeLe4n.ThreadId.toValid? receiverTid with
            | none => simp only []; exact hWiden _ _ hCaps
            | some receiverV =>
              simp only []
              cases hDon : applyCallDonation stWith callerV receiverV with
              | error e => simp only []; exact hWiden _ _ hCaps
              | ok stDon =>
                simp only []
                exact endpointCallLive_confinedToCores st stWith stDon endpointId
                  executingCore receiverTid hCaps
                  (applyCallDonation_confinedToCores stWith stDon callerV receiverV hDon)

/-- SM8.B.2: on the rendezvous path the live write set **is** the §5a union,
instantiated at the states the dispatch really produces.  Stated separately so
the instantiation is visible rather than buried inside the proof above: the
chain start is the resolved receiver and the chain state is the post-donation
state, the two things the second review round said were being supplied by hand. -/
theorem endpointCallDispatchWriteSet_eq_live_of_rendezvous (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage) (endpointRights : AccessRightSet)
    (callerCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st stWith stDon : SystemState) (receiverTid : SeLe4n.ThreadId)
    (callerV receiverV : SeLe4n.ValidThreadId) (summary : CapTransferSummary)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (hRecv : (match st.getEndpoint? endpointId with
              | some ep => ep.receiveQ.head
              | none => none) = some receiverTid)
    (hWith : endpointCallWithCapsOnCore endpointId caller msg endpointRights callerCspaceRoot
      receiverSlotBase executingCore st = (stWith, .ok (summary, sgi)))
    (hCallerV : SeLe4n.ThreadId.toValid? caller = some callerV)
    (hRecvV : SeLe4n.ThreadId.toValid? receiverTid = some receiverV)
    (hDon : applyCallDonation stWith callerV receiverV = .ok stDon) :
    endpointCallDispatchWriteSet endpointId caller msg endpointRights callerCspaceRoot
        receiverSlotBase executingCore st
      = endpointCallLiveWriteSet st endpointId executingCore stDon receiverTid := by
  unfold endpointCallDispatchWriteSet endpointCallDispatchChainWriteSet endpointCallLiveWriteSet
  simp only [hWith, hRecv, hCallerV, hRecvV, hDon]

/-- SM8.B.2 (**the live `.call` non-interference**): the syscall arm the kernel
really runs on a cross-core `Call` is invisible to any core outside its write
set — receiver's home core, caller's own core, and the priority-inheritance
chain's home cores — with no hypothesis on the clearance of the caller, the
receiver, or any boosted server. -/
theorem endpointCallCrossCoreDispatch_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet) (callerCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hne : c ∉ endpointCallDispatchWriteSet endpointId caller msg endpointRights
      callerCspaceRoot receiverSlotBase executingCore st)
    (hShared : sharedViewUnchanged ctx observer st
      (endpointCallCrossCoreDispatch endpointId caller msg endpointRights callerCspaceRoot
        receiverSlotBase executingCore st).1) :
    projectStateOnCore ctx observer
        (endpointCallCrossCoreDispatch endpointId caller msg endpointRights callerCspaceRoot
          receiverSlotBase executingCore st).1 c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (endpointCallCrossCoreDispatch_confinedToCores endpointId caller msg endpointRights
      callerCspaceRoot receiverSlotBase executingCore st hObjInv)
    hShared

-- ============================================================================
-- §5c  The live `.reply` arm itself
-- ============================================================================
--
-- `API.dispatchWithCap`'s `.reply` arm does not call `endpointReplyOnCore`; it
-- calls `endpointReplyCrossCoreDispatch`, which runs the reply, then returns the
-- **recorded server's** donated SchedContext — descheduling that server on *its
-- own* core — then reverts the priority-inheritance chain from that server.
-- Legs two and three can each name a core the reply's own write set does not, so
-- §4's theorem never bounded the live arm (PR #861 review round 4).

/-- SM8.B.2: the cross-core donation **return** writes at most the core it is
handed.  Unlike the call-side `applyCallDonation` this is *not* per-core silent:
the now-passive server is descheduled on its own core, which is precisely why
`endpointReplyCrossCoreDispatch` resolves `determineExecutingCore st expected`
instead of reusing the (possibly delegated) replier's syscall core.

The SchedContext rebinding itself is silent — `returnDonatedSchedContext` moves
`boundThread` in the object store and leaves the scheduler and every register
bank alone — so the whole leg collapses to the one `removeRunnableOnCore`. -/
theorem applyReplyDonationOnCore_confinedToCores (st st' : SystemState)
    (replierVtid : SeLe4n.ValidThreadId) (serverCore : CoreId)
    (hStep : applyReplyDonationOnCore st replierVtid serverCore = .ok st') :
    observableSlotsConfinedToCores st st' [serverCore] := by
  have hOkInj : ∀ {a b : SystemState},
      (Except.ok a : Except KernelError SystemState) = .ok b → a = b := by
    intro a b h; injection h
  unfold applyReplyDonationOnCore at hStep
  simp only [] at hStep
  split at hStep
  · exact observableSlotsConfinedToCores_of_eq _ (hOkInj hStep).symm
  · split at hStep
    · split at hStep
      · split at hStep
        · exact absurd hStep (by simp)
        · next stRet hRet =>
          rw [← hOkInj hStep]
          exact observableSlotsConfinedToCores_widen_cons
            (observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
              (returnDonatedSchedContext_scheduler_eq st stRet _ _ _ hRet)
              (returnDonatedSchedContext_machine_eq st stRet _ _ _ hRet))
            (removeRunnableOnCore_confinedToCores stRet replierVtid.val serverCore)
      · exact absurd hStep (by simp)
    · exact observableSlotsConfinedToCores_of_eq _ (hOkInj hStep).symm

/-- SM8.B.2: **the cores the live cross-core `.reply` may write**, recovered from
the pre-state by mirroring `endpointReplyCrossCoreDispatch`'s own control flow —
same recorded-server resolution, same server-core resolution, same donation
return — so the walk is keyed where the dispatch keys it: on the *recorded
server* at the *post-donation* state.

Three legs on the success path: the answered caller's home core, the recorded
server's own core, and the reverted chain's home cores.  Every arm on which the
dispatch fails closed returns `[]`, which is exact — those arms return the
pre-state unchanged. -/
def endpointReplyDispatchWriteSet (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState) : List CoreId :=
  match endpointReplyOnCore replier target msg executingCore st with
  | (_, .error _) => []
  | (st1, .ok _) =>
      match recordedReplyServer? st target with
      | some expected =>
          match SeLe4n.ThreadId.toValid? expected with
          | some expectedV =>
              match applyReplyDonationOnCore st1 expectedV
                  (determineExecutingCore st expected) with
              | .error _ => []
              | .ok st2 =>
                  (determineTargetCore st target
                    :: determineExecutingCore st expected
                    :: pipChainWriteSet st2 expected executingCore st2.objectIndex.length)
          | none => []
      | none => []

/-- SM8.B.2 (**the live `.reply` bound**): `endpointReplyCrossCoreDispatch` — the
function `API.dispatchWithCap`'s `.reply` arm routes through — writes no core
outside `endpointReplyDispatchWriteSet`.

The proof splits on exactly the scrutinees the dispatch splits on, so each
branch's write set is the one that branch's states justify.  The fail-closed arms
return the pre-state itself, so they are confined to `[]` and widen into
anything; the success arm composes the reply, the donation return and the chain
walk at the states the dispatch really produces. -/
theorem endpointReplyCrossCoreDispatch_confinedToCores (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) :
    observableSlotsConfinedToCores st
      (endpointReplyCrossCoreDispatch replier target msg executingCore st).1
      (endpointReplyDispatchWriteSet replier target msg executingCore st) := by
  have hReply := endpointReplyOnCore_confinedToCores replier target msg executingCore st
    hObjInv
  unfold endpointReplyCrossCoreDispatch endpointReplyDispatchWriteSet
  cases hRep : endpointReplyOnCore replier target msg executingCore st with
  | mk st1 res =>
    rw [hRep] at hReply
    cases res with
    | error e => simp only []; exact observableSlotsConfinedToCores_of_eq _ rfl
    | ok replySgi? =>
      simp only []
      cases hSrv : recordedReplyServer? st target with
      | none => simp only []; exact observableSlotsConfinedToCores_of_eq _ rfl
      | some expected =>
        simp only []
        cases hEV : SeLe4n.ThreadId.toValid? expected with
        | none => simp only []; exact observableSlotsConfinedToCores_of_eq _ rfl
        | some expectedV =>
          simp only []
          cases hDon : applyReplyDonationOnCore st1 expectedV
              (determineExecutingCore st expected) with
          | error e => simp only []; exact observableSlotsConfinedToCores_of_eq _ rfl
          | ok st2 =>
            simp only []
            exact observableSlotsConfinedToCores_trans
              (observableSlotsConfinedToCores_trans hReply
                (applyReplyDonationOnCore_confinedToCores st1 st2 expectedV
                  (determineExecutingCore st expected) hDon))
              (propagatePipChainCrossCore_confinedToCores executingCore
                st2.objectIndex.length st2 expected)

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

-- ============================================================================
-- §5d  The live `.replyRecv` arm itself
-- ============================================================================
--
-- `API.dispatchWithCap`'s `.replyRecv` arm routes to `replyRecvBody`, which is
-- the reply leg, the receive leg **and** `replyRecvReturnDonation` — the last of
-- which returns the old client's SchedContext, may donate the new client's, may
-- deschedule the now-passive recorded server on its own core, and always reverts
-- the recorded server's priority-inheritance chain.  `endpointReplyRecvOnCore`
-- (§4a) is only the first two legs, so it never bounded the live arm.

/-- SM8.B.2: the tail both non-rendezvous arms of `replyRecvReturnDonation` take
— deschedule the now-passive recorded server on its own core, then revert its
chain from the post-deschedule state. -/
def replyRecvDescheduleAndWalkWriteSet (recordedServer : SeLe4n.ThreadId)
    (serverCore : CoreId) (st : SystemState) : List CoreId :=
  serverCore :: pipChainWriteSet (removeRunnableOnCore st recordedServer serverCore)
    recordedServer serverCore
    (removeRunnableOnCore st recordedServer serverCore).objectIndex.length

theorem replyRecvDescheduleAndWalk_confinedToCores (recordedServer : SeLe4n.ThreadId)
    (serverCore : CoreId) (st : SystemState) :
    observableSlotsConfinedToCores st
      (propagatePipChainCrossCore (removeRunnableOnCore st recordedServer serverCore)
        recordedServer serverCore
        (removeRunnableOnCore st recordedServer serverCore).objectIndex.length).1
      (replyRecvDescheduleAndWalkWriteSet recordedServer serverCore st) :=
  observableSlotsConfinedToCores_trans
    (removeRunnableOnCore_confinedToCores st recordedServer serverCore)
    (propagatePipChainCrossCore_confinedToCores serverCore
      (removeRunnableOnCore st recordedServer serverCore).objectIndex.length
      (removeRunnableOnCore st recordedServer serverCore) recordedServer)

/-- SM8.B.2: **the cores `replyRecvReturnDonation` may write**, mirroring its own
control flow.  Four shapes: the non-donating arm walks the chain from the
pre-state; the rendezvous arm donates (per-core silent) and walks from the
post-donation state; the two non-rendezvous arms deschedule the recorded server
on its own core first.  The fail-closed arms produce no post-state at all, so
their entry is `[]` and the confinement theorem's hypothesis rules them out. -/
def replyRecvReturnDonationWriteSet (tid recordedServer nextThread : SeLe4n.ThreadId)
    (serverCore : CoreId) (st : SystemState) : List CoreId :=
  match lookupTcb st recordedServer with
  | none => []
  | some srvTcb =>
    match srvTcb.schedContextBinding with
    | .donated oldScId owner =>
      match recordedServer.toValid?, owner.toValid? with
      | some srvV, some ownerV =>
        match returnDonatedSchedContextValid st srvV oldScId ownerV with
        | .error _ => []
        | .ok st1 =>
          match lookupTcb st1 nextThread with
          | some nextTcb =>
            match nextTcb.ipcState with
            | .blockedOnReply _ _ =>
              match nextThread.toValid?, tid.toValid? with
              | some nextV, some tidV =>
                match applyCallDonation st1 nextV tidV with
                | .error _ => []
                | .ok st2 =>
                    pipChainWriteSet st2 recordedServer serverCore st2.objectIndex.length
              | _, _ => []
            | _ => replyRecvDescheduleAndWalkWriteSet recordedServer serverCore st1
          | none => replyRecvDescheduleAndWalkWriteSet recordedServer serverCore st1
      | _, _ => []
    | _ => pipChainWriteSet st recordedServer serverCore st.objectIndex.length

/-- SM8.B.2: `replyRecvReturnDonation`'s per-core writes stay inside its write
set.  The SchedContext moves (`returnDonatedSchedContextValid`, `applyCallDonation`)
are per-core silent; what is not silent is the recorded server's deschedule and
the chain reversion, and both are named. -/
theorem replyRecvReturnDonation_confinedToCores (tid recordedServer nextThread : SeLe4n.ThreadId)
    (serverCore : CoreId) (st st' : SystemState) (u : Unit)
    (hStep : replyRecvReturnDonation tid recordedServer nextThread serverCore st = .ok (u, st')) :
    observableSlotsConfinedToCores st st'
      (replyRecvReturnDonationWriteSet tid recordedServer nextThread serverCore st) := by
  have hOkInj : ∀ {a b : SystemState},
      (Except.ok ((), a) : Except KernelError (Unit × SystemState)) = .ok (u, b) → a = b := by
    intro a b h; simpa using h
  -- Split the *goal*: its write set mirrors the transition's own match tree, so
  -- each branch's equations reduce `hStep` to that branch's composition.
  unfold replyRecvReturnDonation at hStep
  unfold replyRecvReturnDonationWriteSet
  split
  · next hLk => simp only [hLk] at hStep; exact absurd hStep (by simp)
  · next srvTcb hLk =>
    simp only [hLk] at hStep
    split
    · next oldScId owner hB =>
      simp only [hB] at hStep
      split
      · next srvV ownerV hSrvV hOwnerV =>
        simp only [hSrvV, hOwnerV] at hStep
        split
        · next e hRet => simp only [hRet] at hStep; exact absurd hStep (by simp)
        · next st1 hRet =>
          simp only [hRet] at hStep
          have hSilent : observableSlotsConfinedToCores st st1 [] :=
            observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
              (returnDonatedSchedContext_scheduler_eq st st1 _ _ _ hRet)
              (returnDonatedSchedContext_machine_eq st st1 _ _ _ hRet)
          split
          · next nextTcb hNext =>
            simp only [hNext] at hStep
            split
            · next ep rt hIpc =>
              simp only [hIpc] at hStep
              split
              · next nextV tidV hNextV hTidV =>
                simp only [hNextV, hTidV] at hStep
                split
                · next e hDon => simp only [hDon] at hStep; exact absurd hStep (by simp)
                · next st2 hDon =>
                  simp only [hDon] at hStep
                  rw [← hOkInj hStep]
                  exact observableSlotsConfinedToCores_trans
                    (observableSlotsConfinedToCores_trans hSilent
                      (applyCallDonation_confinedToCores st1 st2 _ _ hDon))
                    (propagatePipChainCrossCore_confinedToCores serverCore
                      st2.objectIndex.length st2 recordedServer)
              · next hNo =>
                exfalso
                revert hStep
                rcases hNV : nextThread.toValid? with _ | nextV <;>
                  rcases hTV : tid.toValid? with _ | tidV <;>
                  simp_all
            · next hIpc =>
              -- the catch-all arm: reduce `hStep` through the same scrutinee,
              -- the rendezvous sub-branch contradicting the split's own guard
              split at hStep
              · next ep' rt' hEq => exact absurd hEq (by simpa using hIpc ep' rt')
              · rw [← hOkInj hStep]
                exact observableSlotsConfinedToCores_trans hSilent
                  (replyRecvDescheduleAndWalk_confinedToCores recordedServer serverCore st1)
          · next hNext =>
            simp only [hNext] at hStep
            rw [← hOkInj hStep]
            exact observableSlotsConfinedToCores_trans hSilent
              (replyRecvDescheduleAndWalk_confinedToCores recordedServer serverCore st1)
      · next hNo =>
        exfalso
        revert hStep
        rcases hSV : recordedServer.toValid? with _ | srvV <;>
          rcases hOV : owner.toValid? with _ | ownerV <;>
          simp_all
    · next hB =>
      -- the non-donating arm: same shape, the `.donated` sub-branch contradicts
      split at hStep
      · next scId' owner' hEq => exact absurd hEq (by simpa using hB scId' owner')
      · rw [← hOkInj hStep]
        exact propagatePipChainCrossCore_confinedToCores serverCore st.objectIndex.length st
          recordedServer

/-- SM8.B.2: **the cores the live `.replyRecv` may write** — the answered
caller's home core, the receive leg's set at the reply's post-state, and the
donation leg's set at the receive's post-state.  Each leg is read at the state
that leg actually runs at, which is the discipline `endpointCallDispatchChainWriteSet`
established: reading a later leg at `st` would name a different chain. -/
def replyRecvBodyWriteSet (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState) : List CoreId :=
  determineTargetCore st prevCaller ::
    (match endpointReplyOnCore receiver prevCaller msg executingCore st with
     | (_, .error _) => []
     | (st1, .ok _) =>
        endpointReceiveDualWriteSet st1 endpointId executingCore ++
          (match endpointReceiveDualOnCore endpointId receiver (some replyId) executingCore st1 with
           | (_, .error _) => []
           | (st2, .ok (nextThread, _)) =>
              replyRecvReturnDonationWriteSet receiver
                ((recordedReplyServer? st prevCaller).getD receiver) nextThread
                (determineExecutingCore st ((recordedReplyServer? st prevCaller).getD receiver))
                st2))

/-- SM8.B.2 (**the live `.replyRecv` bound**): `replyRecvBody` — the function
`API.dispatchWithCap`'s `.replyRecv` arm routes through — writes no core outside
`replyRecvBodyWriteSet`.

All three legs, at the states they really run at.  The receive leg's
`objects.invExt` premise is discharged from the reply leg's own preservation
theorem rather than assumed, exactly as in §4a. -/
theorem replyRecvBody_confinedToCores (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId)
    (msg : IpcMessage) (executingCore : CoreId) (st st' : SystemState) (u : Unit)
    (hObjInv : st.objects.invExt)
    (hStep : replyRecvBody endpointId receiver replyId prevCaller msg executingCore st
      = .ok (u, st')) :
    observableSlotsConfinedToCores st st'
      (replyRecvBodyWriteSet endpointId receiver replyId prevCaller msg executingCore st) := by
  have hReply := endpointReplyOnCore_confinedToCores receiver prevCaller msg executingCore st
    hObjInv
  have hInv1 : (endpointReplyOnCore receiver prevCaller msg executingCore st).1.objects.invExt :=
    endpointReplyOnCore_preserves_objects_invExt receiver prevCaller msg executingCore st hObjInv
  unfold replyRecvBody replyRecvBodyWriteSet at *
  simp only [] at hStep
  cases hRep : endpointReplyOnCore receiver prevCaller msg executingCore st with
  | mk st1 res =>
    rw [hRep] at hReply hInv1 hStep
    cases res with
    | error e => simp only [] at hStep; exact absurd hStep (by simp)
    | ok replySgi =>
      simp only [] at hStep ⊢
      have hRecv := endpointReceiveDualOnCore_confinedToCores endpointId receiver
        (some replyId) executingCore st1 hInv1
      cases hRcv : endpointReceiveDualOnCore endpointId receiver (some replyId) executingCore st1
        with
      | mk st2 res2 =>
        rw [hRcv] at hRecv hStep
        cases res2 with
        | error e => simp only [] at hStep; exact absurd hStep (by simp)
        | ok pair =>
          rcases pair with ⟨nextThread, recvSgi⟩
          simp only [] at hStep ⊢
          exact observableSlotsConfinedToCores_trans hReply
            (observableSlotsConfinedToCores_trans hRecv
              (replyRecvReturnDonation_confinedToCores receiver _ nextThread _ st2 st' u hStep))

/-- SM8.B.2 (**the live `.replyRecv` non-interference**): the syscall arm the
kernel really runs on a cross-core `ReplyRecv` is invisible to any core outside
its write set, with no hypothesis on the clearance of the answered caller, the
rendezvousing sender, the recorded server or any chain member. -/
theorem replyRecvBody_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st st' : SystemState) (u : Unit) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hStep : replyRecvBody endpointId receiver replyId prevCaller msg executingCore st
      = .ok (u, st'))
    (hne : c ∉ replyRecvBodyWriteSet endpointId receiver replyId prevCaller msg executingCore st)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (replyRecvBody_confinedToCores endpointId receiver replyId prevCaller msg executingCore
      st st' u hObjInv hStep)
    hShared

-- ============================================================================
-- §5e  The live `.tcbSuspend` arm itself
-- ============================================================================
--
-- `API.dispatchCapabilityOnly`'s `.tcbSuspend` arm routes to `suspendThreadOnCore`,
-- which is `cancelIpcBlockingOnCore`'s teardown *plus* the priority-inheritance
-- chain reversion, the donation-cancellation arms, the home-core removal, the
-- running-core removal when the victim diverged from its home, and a scheduling
-- point on the executing core.  §5's `cancelIpcBlockingOnCore_confinedToCores`
-- covers the first two of those, so it never bounded the live arm (PR #861
-- review round 4).
--
-- The leaf frames below are new: per-core confinement reads the domain slots and
-- the register banks, and the context switch had frames for neither.

/-- SM8.B.2: a preemption leaves every core's domain slots alone. -/
theorem preemptCurrentOnCore_activeDomainOnCore (st : SystemState) (c c' : CoreId)
    (tid : SeLe4n.ThreadId) :
    (preemptCurrentOnCore st c tid).scheduler.activeDomainOnCore c'
      = st.scheduler.activeDomainOnCore c' := by
  simp only [preemptCurrentOnCore]; repeat' split
  all_goals first | rfl | simp only [SchedulerState.setCurrentOnCore_activeDomainOnCore,
      SchedulerState.setRunQueueOnCore_activeDomainOnCore]

theorem preemptCurrentOnCore_domainTimeRemainingOnCore (st : SystemState) (c c' : CoreId)
    (tid : SeLe4n.ThreadId) :
    (preemptCurrentOnCore st c tid).scheduler.domainTimeRemainingOnCore c'
      = st.scheduler.domainTimeRemainingOnCore c' := by
  simp only [preemptCurrentOnCore]; repeat' split
  all_goals first | rfl | simp only [SchedulerState.setCurrentOnCore_domainTimeRemainingOnCore,
      SchedulerState.setRunQueueOnCore_domainTimeRemainingOnCore]

theorem preemptCurrentOnCore_domainScheduleIndexOnCore (st : SystemState) (c c' : CoreId)
    (tid : SeLe4n.ThreadId) :
    (preemptCurrentOnCore st c tid).scheduler.domainScheduleIndexOnCore c'
      = st.scheduler.domainScheduleIndexOnCore c' := by
  simp only [preemptCurrentOnCore]; repeat' split
  all_goals first | rfl | simp only [SchedulerState.setCurrentOnCore_domainScheduleIndexOnCore,
      SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore]

/-- SM8.B.2: a context switch leaves every core's domain slots alone — it moves
the current thread and the run queue, never the domain schedule. -/
theorem switchToThreadOnCore_activeDomainOnCore (st st' : SystemState) (c c' : CoreId)
    (tid : SeLe4n.ThreadId) (h : switchToThreadOnCore st c tid = .ok st') :
    st'.scheduler.activeDomainOnCore c' = st.scheduler.activeDomainOnCore c' := by
  unfold switchToThreadOnCore at h
  repeat' split at h
  all_goals try simp only [] at h
  all_goals first
    | (rw [Except.ok.injEq] at h
       subst h
       simp only [restoreIncomingContextOnCoreUnlessCurrent_scheduler,
         SchedulerState.setCurrentOnCore_activeDomainOnCore,
         SchedulerState.setRunQueueOnCore_activeDomainOnCore,
         preemptCurrentOnCore_activeDomainOnCore])
    | exact absurd h (by simp)

theorem switchToThreadOnCore_domainTimeRemainingOnCore (st st' : SystemState) (c c' : CoreId)
    (tid : SeLe4n.ThreadId) (h : switchToThreadOnCore st c tid = .ok st') :
    st'.scheduler.domainTimeRemainingOnCore c' = st.scheduler.domainTimeRemainingOnCore c' := by
  unfold switchToThreadOnCore at h
  repeat' split at h
  all_goals try simp only [] at h
  all_goals first
    | (rw [Except.ok.injEq] at h
       subst h
       simp only [restoreIncomingContextOnCoreUnlessCurrent_scheduler,
         SchedulerState.setCurrentOnCore_domainTimeRemainingOnCore,
         SchedulerState.setRunQueueOnCore_domainTimeRemainingOnCore,
         preemptCurrentOnCore_domainTimeRemainingOnCore])
    | exact absurd h (by simp)

theorem switchToThreadOnCore_domainScheduleIndexOnCore (st st' : SystemState) (c c' : CoreId)
    (tid : SeLe4n.ThreadId) (h : switchToThreadOnCore st c tid = .ok st') :
    st'.scheduler.domainScheduleIndexOnCore c' = st.scheduler.domainScheduleIndexOnCore c' := by
  unfold switchToThreadOnCore at h
  repeat' split at h
  all_goals try simp only [] at h
  all_goals first
    | (rw [Except.ok.injEq] at h
       subst h
       simp only [restoreIncomingContextOnCoreUnlessCurrent_scheduler,
         SchedulerState.setCurrentOnCore_domainScheduleIndexOnCore,
         SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore,
         preemptCurrentOnCore_domainScheduleIndexOnCore])
    | exact absurd h (by simp)

/-- SM8.B.2: **a context switch on core `c` is confined to core `c`.**  The
register-bank clause is the one that needed a new frame: SM5.I banks every
core's `RegisterFile` inside one `MachineState`, so a switch does write
`machine`, and "writes `machine`" is not the same as "is visible on every
core". -/
theorem switchToThreadOnCore_confinedToCores (st st' : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (h : switchToThreadOnCore st c tid = .ok st') :
    observableSlotsConfinedToCores st st' [c] :=
  ⟨fun c' hc => (switchToThreadOnCore_independent_of_other_core st c c' tid st'
      (fun he => hc (by simp [he])) h).2,
   fun c' hc => (switchToThreadOnCore_independent_of_other_core st c c' tid st'
      (fun he => hc (by simp [he])) h).1,
   fun c' _ => switchToThreadOnCore_activeDomainOnCore st st' c c' tid h,
   fun c' _ => switchToThreadOnCore_domainTimeRemainingOnCore st st' c c' tid h,
   fun c' _ => switchToThreadOnCore_domainScheduleIndexOnCore st st' c c' tid h,
   fun c' hc => switchToThreadOnCore_machine_regsOnCore_ne st c c' tid st'
      (fun he => hc (by simp [he])) h⟩

/-- SM8.B.2: the per-core reschedule handler is confined to the core it runs
on — it either idles that core, keeps its current thread, or switches it. -/
theorem handleRescheduleSgiOnCore_confinedToCores (st st' : SystemState) (c : CoreId)
    (h : handleRescheduleSgiOnCore st c = .ok st') :
    observableSlotsConfinedToCores st st' [c] := by
  unfold handleRescheduleSgiOnCore at h
  split at h
  · exact absurd h (by simp)
  · rw [Except.ok.injEq] at h; subst h; exact observableSlotsConfinedToCores_refl _ _
  · split at h
    · exact switchToThreadOnCore_confinedToCores st st' c _ h
    · rw [Except.ok.injEq] at h; subst h; exact observableSlotsConfinedToCores_refl _ _

/-- SM8.B.2: the suspend pipeline's G7 scheduling point writes at most the
**executing** core.  Its remote leg is an SGI *return value*, not a state
change: the home core is poked, and pokes are not writes. -/
theorem suspendRescheduleOnCore_confinedToCores (st st' : SystemState)
    (home executingCore : CoreId) (wasCurrentHome localDeboosted : Bool)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (h : suspendRescheduleOnCore st home executingCore wasCurrentHome localDeboosted
      = .ok (st', sgi)) :
    observableSlotsConfinedToCores st st' [executingCore] := by
  unfold suspendRescheduleOnCore at h
  repeat' split at h
  all_goals first
    | (rw [Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨hs, -⟩ := h
       subst hs
       first
         | exact handleRescheduleSgiOnCore_confinedToCores st _ executingCore (by assumption)
         | exact observableSlotsConfinedToCores_refl _ _)
    | exact absurd h (by simp)

/-- SM8.B.2: the priority ops' preemption seam writes at most the **executing**
core.  Its remote leg is an SGI *return value*, not a state change: the running
core is poked, and pokes are not writes.  Shared with the per-core SchedContext
unbind, whose demotion needs the same scheduling point. -/
theorem priorityRescheduleOnCore_confinedToCores (st st' : SystemState)
    (running? : Option CoreId) (executingCore : CoreId) (shouldPreempt : Bool)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (h : SchedContext.PriorityManagement.priorityRescheduleOnCore st running?
      executingCore shouldPreempt = .ok (st', sgi)) :
    observableSlotsConfinedToCores st st' [executingCore] := by
  unfold SchedContext.PriorityManagement.priorityRescheduleOnCore at h
  repeat' split at h
  all_goals first
    | (rw [Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨hs, -⟩ := h
       subst hs
       first
         | exact handleRescheduleSgiOnCore_confinedToCores st _ executingCore (by assumption)
         | exact observableSlotsConfinedToCores_refl _ _)
    | exact absurd h (by simp)

/-- SM8.B.2 (PR #861 review round 34): the **wrapper** is confined to the
executing core, in *both* settings of the restore seam.

Proved by cases on the flag, so neither branch is dead: the live branch defers
to the base theorem above, and the gated branch changes no state at all. -/
theorem priorityRescheduleOnCoreLive_confinedToCores (st st' : SystemState)
    (running? : Option CoreId) (executingCore : CoreId) (shouldPreempt : Bool)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (h : SchedContext.PriorityManagement.priorityRescheduleOnCoreLive st running?
      executingCore shouldPreempt = .ok (st', sgi)) :
    observableSlotsConfinedToCores st st' [executingCore] := by
  unfold SchedContext.PriorityManagement.priorityRescheduleOnCoreLive at h
  split at h
  · exact priorityRescheduleOnCore_confinedToCores st st' running? executingCore
      shouldPreempt sgi h
  · rw [SchedContext.PriorityManagement.priorityRescheduleEnqueueOnly_state
      st st' running? executingCore shouldPreempt sgi h]
    exact observableSlotsConfinedToCores_refl _ _

/-- SM8.B.2 (PR #861 review round 35): **the cores a destroy sweep actually
touches** — those the thread occupies in the pre-state.

`removeRunnableFromAllCores` folds over *every* core, so the naive bound is
`allCores`, which is true and useless.  Round 17 rewrote the step to be
**guarded** by `threadOccupiesCore` precisely so a sharper bound would be
available: an unoccupied core is left literally untouched, not rewritten with
equal values.  This is that bound. -/
def threadOccupiedCores (st : SystemState) (tid : SeLe4n.ThreadId) : List CoreId :=
  Concurrency.allCores.filter (threadOccupiesCore st tid)

/-- SM8.B.2: a core outside the occupancy set does not hold the thread. -/
theorem not_threadOccupiesCore_of_not_mem (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : CoreId) (h : c ∉ threadOccupiedCores st tid) :
    threadOccupiesCore st tid c = false := by
  cases hOcc : threadOccupiesCore st tid c with
  | false => rfl
  | true =>
    exact absurd (List.mem_filter.mpr ⟨Concurrency.mem_allCores c, by simp [hOcc]⟩) h

/-- SM8.B.2 (**the destroy sweep's bound**): the sweep writes no core the thread
does not occupy.

All six observable slots: the two the guarded step writes come from the sweep's
closed forms (both keyed on the *pre-state* guard, which is what makes a
pre-state write set possible at all), the three domain slots from the round-35
fold frame, and the register banks because the sweep never touches `machine`. -/
theorem removeRunnableFromAllCores_confinedToCores (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    observableSlotsConfinedToCores st (removeRunnableFromAllCores st tid)
      (threadOccupiedCores st tid) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c hc
  · rw [removeRunnableFromAllCores_runQueueOnCore]
    simp [not_threadOccupiesCore_of_not_mem st tid c hc]
  · rw [removeRunnableFromAllCores_currentOnCore]
    have hOcc := not_threadOccupiesCore_of_not_mem st tid c hc
    unfold threadOccupiesCore at hOcc
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hOcc
    simp [hOcc.2]
  · exact removeRunnableFromAllCores_activeDomainOnCore st tid c
  · exact removeRunnableFromAllCores_domainTimeRemainingOnCore st tid c
  · exact removeRunnableFromAllCores_domainScheduleIndexOnCore st tid c
  · rw [removeRunnableFromAllCores_machine]

/-- SM8.B.2: occupancy is a scheduler read, so a scheduler-preserving prefix
does not move the write set.

Load-bearing for the retype: the sweep runs several steps into the cleanup
pipeline, but the write set is declared at the pipeline's **entry** state.  The
two are the same set precisely because everything in between frames the
scheduler. -/
theorem threadOccupiedCores_congr {st st' : SystemState} (tid : SeLe4n.ThreadId)
    (h : st'.scheduler = st.scheduler) :
    threadOccupiedCores st' tid = threadOccupiedCores st tid := by
  unfold threadOccupiedCores threadOccupiesCore
  rw [h]

/-- SM8.B.2: a scheduler- and machine-preserving prefix can be dropped from a
confinement statement.

The composition shape the retype pipeline needs everywhere: only one of its
steps writes a scheduler slot, and the several around it must be discharged
without inflating the declared set (which `observableSlotsConfinedToCores_trans`
alone would do, leaving `[] ++ cs`). -/
theorem observableSlotsConfinedToCores_of_framed_prefix {st stMid st' : SystemState}
    {cs : List CoreId}
    (hSched : stMid.scheduler = st.scheduler) (hMach : stMid.machine = st.machine)
    (h : observableSlotsConfinedToCores stMid st' cs) :
    observableSlotsConfinedToCores st st' cs :=
  ⟨fun c hc => (h.runQueue c hc).trans (by rw [hSched]),
   fun c hc => (h.current c hc).trans (by rw [hSched]),
   fun c hc => (h.activeDomain c hc).trans (by rw [hSched]),
   fun c hc => (h.domainTimeRemaining c hc).trans (by rw [hSched]),
   fun c hc => (h.domainScheduleIndex c hc).trans (by rw [hSched]),
   fun c hc => (h.regs c hc).trans (by rw [hMach])⟩

/-- SM8.B.2: and the mirror — a framed **suffix** does not move the set either,
where "framed" here reaches only as far as the observer does.

The register-bank form rather than the whole-machine one, because the retype's
memory scrub writes `machine.memory` and the whole-machine version would be
false of it. -/
theorem observableSlotsConfinedToCores_of_framed_suffix_regs {st stMid st' : SystemState}
    {cs : List CoreId}
    (hSched : st'.scheduler = stMid.scheduler)
    (hRegs : ∀ c, st'.machine.regsOnCore c = stMid.machine.regsOnCore c)
    (h : observableSlotsConfinedToCores st stMid cs) :
    observableSlotsConfinedToCores st st' cs :=
  ⟨fun c hc => (by rw [hSched] : st'.scheduler.runQueueOnCore c = _).trans (h.runQueue c hc),
   fun c hc => (by rw [hSched] : st'.scheduler.currentOnCore c = _).trans (h.current c hc),
   fun c hc => (by rw [hSched] : st'.scheduler.activeDomainOnCore c = _).trans
     (h.activeDomain c hc),
   fun c hc => (by rw [hSched] : st'.scheduler.domainTimeRemainingOnCore c = _).trans
     (h.domainTimeRemaining c hc),
   fun c hc => (by rw [hSched] : st'.scheduler.domainScheduleIndexOnCore c = _).trans
     (h.domainScheduleIndex c hc),
   fun c hc => (hRegs c).trans (h.regs c hc)⟩

/-- SM8.B.2: the whole-machine instance of the suffix rule, for the steps that
frame `machine` outright. -/
theorem observableSlotsConfinedToCores_of_framed_suffix {st stMid st' : SystemState}
    {cs : List CoreId}
    (hSched : st'.scheduler = stMid.scheduler) (hMach : st'.machine = stMid.machine)
    (h : observableSlotsConfinedToCores st stMid cs) :
    observableSlotsConfinedToCores st st' cs :=
  ⟨fun c hc => (by rw [hSched] : st'.scheduler.runQueueOnCore c = _).trans (h.runQueue c hc),
   fun c hc => (by rw [hSched] : st'.scheduler.currentOnCore c = _).trans (h.current c hc),
   fun c hc => (by rw [hSched] : st'.scheduler.activeDomainOnCore c = _).trans
     (h.activeDomain c hc),
   fun c hc => (by rw [hSched] : st'.scheduler.domainTimeRemainingOnCore c = _).trans
     (h.domainTimeRemaining c hc),
   fun c hc => (by rw [hSched] : st'.scheduler.domainScheduleIndexOnCore c = _).trans
     (h.domainScheduleIndex c hc),
   fun c hc => (by rw [hMach] : st'.machine.regsOnCore c = _).trans (h.regs c hc)⟩

/-- SM8.B.2: **the TCB reference scrub's bound** — the destroy sweep, plus two
object-store sweeps that write no scheduler slot at all. -/
theorem cleanupTcbReferences_confinedToCores (st : SystemState) (tid : SeLe4n.ThreadId) :
    observableSlotsConfinedToCores st (cleanupTcbReferences st tid)
      (threadOccupiedCores st tid) :=
  observableSlotsConfinedToCores_of_framed_suffix
    (cleanupTcbReferences_scheduler_eq_removeRunnableFromAllCores st tid)
    (by rw [cleanupTcbReferences_machine_eq, removeRunnableFromAllCores_machine])
    (removeRunnableFromAllCores_confinedToCores st tid)

/-- SM8.B.2: clearing a suspended thread's transient fields is per-core silent —
it rewrites one TCB and touches neither the scheduler nor a register bank. -/
theorem clearPendingState_confinedToCores (st : SystemState) (tid : SeLe4n.ThreadId) :
    observableSlotsConfinedToCores st (clearPendingState st tid) [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (by unfold clearPendingState; split <;> rfl)
    (by unfold clearPendingState; split <;> rfl)

/-- SM8.B.2: the bound-SchedContext cancellation arm is per-core silent.  It
unbinds the SC, purges the victim's replenishments from its home core's
**replenishment** queue and rewrites the TCB binding — and SM8.A's
`onCore_perCore_independence` puts the replenishment queue outside the
observer's read set entirely, so none of that is observable anywhere. -/
theorem cancelBoundDonationOnCore_confinedToCores (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (rqCore : CoreId)
    (h : cancelBoundDonationOnCore st tid tcb rqCore = .ok st') :
    observableSlotsConfinedToCores st st' [] := by
  refine ⟨fun c _ => (cancelBoundDonationOnCore_runQueue_current_eq st st' tid tcb rqCore c h).1,
          fun c _ => (cancelBoundDonationOnCore_runQueue_current_eq st st' tid tcb rqCore c h).2,
          ?_, ?_, ?_, ?_⟩
  all_goals intro c _
  all_goals (
    simp only [cancelBoundDonationOnCore] at h
    repeat' split at h
    all_goals first
      | (rw [Except.ok.injEq] at h; subst h; simp)
      | exact absurd h (by simp))

/-- SM8.B.2: a replenishment migration is per-core silent — it moves a
SchedContext's replenishments between two cores' **replenishment** queues, and
SM8.A's `onCore_perCore_independence` puts that queue outside the observer's
read set entirely. -/
theorem migrateSchedContextReplenishment_confinedToCores (st : SystemState)
    (scId : SeLe4n.SchedContextId) (fromCore toCore : CoreId) :
    observableSlotsConfinedToCores st
      (migrateSchedContextReplenishment st scId fromCore toCore) [] := by
  refine ⟨fun c _ => (migrateSchedContextReplenishment_runQueue_current_eq st scId fromCore
            toCore c).1,
          fun c _ => (migrateSchedContextReplenishment_runQueue_current_eq st scId fromCore
            toCore c).2, ?_, ?_, ?_, ?_⟩
  all_goals intro c _
  all_goals (unfold migrateSchedContextReplenishment; split <;> simp)

/-- SM8.B.2 (**the missing frame**): a run-queue migration writes the two cores
it names and nothing else.

`migrateRunQueueOnAffinityChange` had frames for `machine`, `objects`,
`getTcb`, `getSchedContext`, `replenishQueueOnCore` and `determineTargetCore`,
and a projection-preservation lemma — but nothing saying *which cores it leaves
alone*, which is exactly what confinement needs.  Its absence is why
`.tcbSetAffinity` sat in the routing allowlist instead of carrying a proof.

Every arm but one returns the pre-state outright; the migrating arm is two
`setRunQueueOnCore` writes at `fromCore` and `toCore`, so a core outside the
pair sees neither, and the five non-run-queue slots are untouched on every
arm. -/
theorem migrateRunQueueOnAffinityChange_confinedToCores (st : SystemState)
    (tid : SeLe4n.ThreadId) (fromCore toCore : CoreId) :
    observableSlotsConfinedToCores st
      (migrateRunQueueOnAffinityChange st tid fromCore toCore) [fromCore, toCore] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
    obtain ⟨hf, ht⟩ := hc
    unfold migrateRunQueueOnAffinityChange
    split
    · rfl
    · split
      · rfl
      · split
        · simp [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne, Ne.symm hf, Ne.symm ht]
        · rfl
  all_goals intro c _
  all_goals (unfold migrateRunQueueOnAffinityChange; repeat' split)
  all_goals simp

/-- SM8.B.2: the donated-SchedContext cancellation arm is per-core silent for
the same reason — the SC returns to its owner in the object store and its
replenishments migrate between two cores' replenishment queues, neither of
which the observer reads. -/
theorem cancelDonatedDonationOnCore_confinedToCores (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (h : cancelDonatedDonationOnCore st tid tcb = .ok st') :
    observableSlotsConfinedToCores st st' [] := by
  unfold cancelDonatedDonationOnCore at h
  split at h
  · split at h
    · exact absurd h (by simp)
    · next stCleanup hCleanup =>
      rw [Except.ok.injEq] at h
      subst h
      exact observableSlotsConfinedToCores_trans
        (observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
          (cleanupDonatedSchedContext_scheduler_eq st stCleanup tid hCleanup)
          (cleanupDonatedSchedContext_machine_eq st stCleanup tid hCleanup))
        (migrateSchedContextReplenishment_confinedToCores stCleanup _ _ _)
  · exact absurd h (by simp)

/-- SM8.B.2: **the cores the live `.tcbSuspend` may write**, mirroring
`suspendThreadOnCore`'s own control flow.  Four contributions, all read off the
**pre-state** exactly as the transition reads them:

* the reverted priority-inheritance chain's home cores, walked from the
  captured `blockingServer` at the post-teardown state;
* the victim's `home` (`determineTargetCore`), where it is dequeued;
* the core actually **running** the victim, when `runningCoreOf?` diverges from
  the home — the PR #831 review-4 case of an unbound victim current on a
  secondary core;
* the **executing** core, where G7 may run a local preemption point.

The teardown, both donation arms, `clearPendingState` and the `.Inactive` store
are per-core silent and contribute nothing. -/
def suspendThreadOnCoreWriteSet (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (executingCore : CoreId) : List CoreId :=
  match st.getTcb? vtid.val with
  | none => []
  | some tcb =>
    if tcb.threadState == .Inactive then []
    else
      -- One entry per pipeline step, in execution order; `[]` marks a step that
      -- writes no core at all, so this reads as the transition's own shape.
      (match PriorityInheritance.blockingServer st vtid.val with
       | some serverId =>
           pipChainWriteSet (cancelIpcBlockingValid st vtid tcb) serverId executingCore
             (cancelIpcBlockingValid st vtid tcb).objectIndex.length
       | none => [])                                  -- teardown, then chain reversion
      ++ []                                           -- donation cancellation
      ++ (determineTargetCore st vtid.val
          :: (match runningCoreOf? st vtid.val with
              | some c => [c]
              | none => []))                          -- home dequeue, running dequeue
      ++ []                                           -- clearPendingState
      ++ []                                           -- the `.Inactive` store
      ++ [executingCore]                              -- the G7 scheduling point

/-- SM8.B.2: the suspend pipeline's two dequeues — the victim leaves its
**home** core's queue always, and the core actually **running** it as well when
`runningCoreOf?` diverges from the home (the PR #831 review-4 case). -/
theorem suspendDequeues_confinedToCores (s : SystemState) (tid : SeLe4n.ThreadId)
    (home : CoreId) (rc : Option CoreId) :
    observableSlotsConfinedToCores s
      (match rc with
       | some c =>
         if (c == home) = true then removeRunnableOnCore s tid home
         else removeRunnableOnCore (removeRunnableOnCore s tid home) tid c
       | none => removeRunnableOnCore s tid home)
      (home :: (match rc with | some c => [c] | none => [])) := by
  cases rc with
  | none => exact removeRunnableOnCore_confinedToCores s tid home
  | some c =>
    simp only []
    split
    · exact observableSlotsConfinedToCores_mono
        (fun _ hm => by simp only [List.mem_singleton] at hm; simp [hm])
        (removeRunnableOnCore_confinedToCores s tid home)
    · exact observableSlotsConfinedToCores_trans
        (removeRunnableOnCore_confinedToCores s tid home)
        (removeRunnableOnCore_confinedToCores _ tid c)

/-- SM8.B.2: marking the victim `.Inactive` is per-core silent — one object
store write. -/
theorem suspendInactiveStore_confinedToCores (s : SystemState) (tid : SeLe4n.ThreadId) :
    observableSlotsConfinedToCores s
      (match s.getTcb? tid with
       | some t =>
         { s with objects := s.objects.insert tid.toObjId (.tcb { t with
             threadState := .Inactive }) }
       | none => s) [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (by split <;> rfl) (by split <;> rfl)

/-- SM8.B.2: whichever donation-cancellation arm the victim's binding selects,
the step is per-core silent. -/
theorem suspendDonationArms_confinedToCores (s sD : SystemState) (tid : SeLe4n.ThreadId)
    (tcb' : TCB) (home : CoreId)
    (h : (match tcb'.schedContextBinding with
          | .unbound => (Except.ok s : Except KernelError SystemState)
          | .bound _ => cancelBoundDonationOnCore s tid tcb' home
          | .donated _ _ => cancelDonatedDonationOnCore s tid tcb') = .ok sD) :
    observableSlotsConfinedToCores s sD [] := by
  split at h
  · rw [Except.ok.injEq] at h; subst h; exact observableSlotsConfinedToCores_refl _ _
  · exact cancelBoundDonationOnCore_confinedToCores s sD tid tcb' home h
  · exact cancelDonatedDonationOnCore_confinedToCores s sD tid tcb' h

/-- SM8.B.2 (**the live `.tcbSuspend` bound**): `suspendThreadOnCore` — the
function `API.dispatchCapabilityOnly`'s `.tcbSuspend` arm routes through —
writes no core outside `suspendThreadOnCoreWriteSet`.

Six of its steps are per-core silent (the IPC teardown, both donation arms,
`clearPendingState`, the `.Inactive` store); the three that are not are the
priority-inheritance reversion, the two dequeues and the G7 scheduling point,
and all three are named.  The closing `mono` is only re-ordering — the
composition produces the cores in execution order, the declared set lists them
in reading order. -/
theorem suspendThreadOnCore_confinedToCores (st st' : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (hStep : suspendThreadOnCore st vtid executingCore = .ok (st', sgi)) :
    observableSlotsConfinedToCores st st'
      (suspendThreadOnCoreWriteSet st vtid executingCore) := by
  unfold suspendThreadOnCore at hStep
  unfold suspendThreadOnCoreWriteSet
  simp only [] at hStep
  split
  · next hTcb => simp only [hTcb] at hStep; exact absurd hStep (by simp)
  · next tcb hTcb =>
    simp only [hTcb] at hStep
    split
    · next hInact => simp only [hInact] at hStep; exact absurd hStep (by simp)
    · next hInact =>
      rw [if_neg hInact] at hStep
      have hCancel : observableSlotsConfinedToCores st (cancelIpcBlockingValid st vtid tcb) [] :=
        cancelIpcBlocking_confinedToCores st vtid.val tcb
      -- The chain reversion, stated over the same `blockingServer` scrutinee the
      -- transition and the write set both read, so the two stay in step.
      have hPre : observableSlotsConfinedToCores st
          (match PriorityInheritance.blockingServer st vtid.val with
           | some serverId =>
             (PriorityInheritance.propagatePipChainCrossCore
               (cancelIpcBlockingValid st vtid tcb) serverId executingCore).1
           | none => cancelIpcBlockingValid st vtid tcb)
          (match PriorityInheritance.blockingServer st vtid.val with
           | some serverId =>
             pipChainWriteSet (cancelIpcBlockingValid st vtid tcb) serverId executingCore
               (cancelIpcBlockingValid st vtid tcb).objectIndex.length
           | none => []) := by
        cases hSrv : PriorityInheritance.blockingServer st vtid.val with
        | none => simp only []; exact hCancel
        | some serverId =>
          simp only []
          exact observableSlotsConfinedToCores_trans hCancel
            (propagatePipChainCrossCore_confinedToCores executingCore _ _ serverId)
      split at hStep
      · exact absurd hStep (by simp)
      · next stD hDonArm =>
        exact (observableSlotsConfinedToCores_trans
            (observableSlotsConfinedToCores_trans
              (observableSlotsConfinedToCores_trans
                (observableSlotsConfinedToCores_trans
                  (observableSlotsConfinedToCores_trans hPre
                    (suspendDonationArms_confinedToCores _ stD vtid.val _ _ hDonArm))
                  (suspendDequeues_confinedToCores stD vtid.val
                    (determineTargetCore st vtid.val) (runningCoreOf? st vtid.val)))
                (clearPendingState_confinedToCores _ vtid.val))
              (suspendInactiveStore_confinedToCores _ vtid.val))
            (suspendRescheduleOnCore_confinedToCores _ st' _ executingCore _ _ sgi hStep))

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

-- ============================================================================
-- §5f  The live `.tcbResume` arm
-- ============================================================================
--
-- PR #861 review round 10 found this arm calling the boot-pinned `resumeThread`
-- while `resumeThreadOnCore` sat unused: a thread homed on a secondary core was
-- resumed onto the **boot** run queue, where its own core would never dispatch
-- it.  The arm is rerouted; this section is the audit the inventory was missing.

/-- SM8.B.2: **the cores the live `.tcbResume` may write** — the resumed thread's
home core, where it re-enters the run queue, and the executing core, which runs
the reschedule inline when it *is* the home core.  A remote resume writes only
the home core and hands it an SGI, so the declared set over-approximates by one
core on that path; over-approximating is the safe direction. -/
def resumeThreadOnCoreWriteSet (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (executingCore : CoreId) : List CoreId :=
  [determineTargetCore st vtid.val, executingCore]

/-- SM8.B.2: the per-core resume's ready-restore leg is per-core silent — it
rewrites the victim's TCB (IPC fields, `threadState`, `pipBoost`) and touches
neither the scheduler nor any register bank. -/
theorem resumeReadyMidState_confinedToCores (st : SystemState) (tid : SeLe4n.ThreadId) :
    observableSlotsConfinedToCores st (resumeReadyMidState st tid) [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (resumeReadyMidState_scheduler_eq st tid)
    (resumeReadyMidState_machine_eq st tid)

/-- SM8.B.2 (**the live `.tcbResume` bound**): `resumeThreadOnCore` writes no
core outside `resumeThreadOnCoreWriteSet`.

Three legs: the silent ready-restore, the enqueue on the **home** core (read
from the pre-state, which is where the write set reads it), and — only when the
home core is the executing one — the inline reschedule.  The remote path
returns an SGI rather than applying it, so it writes nothing further. -/
theorem resumeThreadOnCore_confinedToCores (st st' : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (hStep : Lifecycle.Suspend.resumeThreadOnCore st vtid executingCore = .ok (st', sgi)) :
    observableSlotsConfinedToCores st st'
      (resumeThreadOnCoreWriteSet st vtid executingCore) := by
  unfold Lifecycle.Suspend.resumeThreadOnCore at hStep
  simp only [] at hStep
  split at hStep
  · next tcb hTcb =>
    split at hStep
    · exact absurd hStep (by simp)
    · next hInactive =>
      have hPre : observableSlotsConfinedToCores st
          (enqueueRunnableOnCore (resumeReadyMidState st vtid.val)
            (determineTargetCore st vtid.val) vtid.val)
          [determineTargetCore st vtid.val] :=
        observableSlotsConfinedToCores_widen_cons
          (resumeReadyMidState_confinedToCores st vtid.val)
          (enqueueRunnableOnCore_confinedToCores _ (determineTargetCore st vtid.val) vtid.val)
      split at hStep
      · -- LOCAL: the home core is the executing core, reschedule runs inline.
        -- `[target] ++ [executingCore]` *is* the declared set, definitionally.
        split at hStep
        · next st4 hResched =>
          rw [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨hs, -⟩ := hStep
          subst hs
          exact observableSlotsConfinedToCores_trans hPre
            (handleRescheduleSgiOnCore_confinedToCores _ st4 executingCore hResched)
        · exact absurd hStep (by simp)
      · -- REMOTE: the SGI is returned, not applied, so only the home core moves.
        rw [Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨hs, -⟩ := hStep
        subst hs
        refine observableSlotsConfinedToCores_mono ?_ hPre
        intro c hc
        simp only [List.mem_singleton] at hc
        simp [resumeThreadOnCoreWriteSet, hc]
  · exact absurd hStep (by simp)

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

/-- SM8.B.2: the enqueue-only sibling's bound, which is **sharper** than the
base transition's — it writes the home core and nothing else.

`resumeThreadOnCore`'s set is `[target, executingCore]` because its local arm
runs the reschedule inline.  The gated form stops after the enqueue, so the
executing core never moves; declaring the smaller set is what makes that
difference a checked fact rather than a comment. -/
theorem resumeThreadEnqueueOnly_confinedToCores (st st' : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (hStep : Lifecycle.Suspend.resumeThreadEnqueueOnly st vtid executingCore
      = .ok (st', sgi)) :
    observableSlotsConfinedToCores st st' [determineTargetCore st vtid.val] := by
  unfold Lifecycle.Suspend.resumeThreadEnqueueOnly at hStep
  simp only [] at hStep
  split at hStep
  · next tcb hTcb =>
    split at hStep
    · exact absurd hStep (by simp)
    · next hInactive =>
      have hPre : observableSlotsConfinedToCores st
          (enqueueRunnableOnCore (resumeReadyMidState st vtid.val)
            (determineTargetCore st vtid.val) vtid.val)
          [determineTargetCore st vtid.val] :=
        observableSlotsConfinedToCores_widen_cons
          (resumeReadyMidState_confinedToCores st vtid.val)
          (enqueueRunnableOnCore_confinedToCores _ (determineTargetCore st vtid.val) vtid.val)
      -- both arms commit the same state; they differ only in the returned SGI
      split at hStep <;>
        · rw [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨hs, -⟩ := hStep
          subst hs
          exact hPre
  · exact absurd hStep (by simp)

/-- SM8.B.2 (**the bound on the function the live `.tcbResume` arm calls**).

PR #861 review round 37: the arm delegates to `resumeThreadOnCoreLive`, and with
`contextRestoreSeamLive = false` that is *not* `resumeThreadOnCore` — the
wrapper only enqueues where the base transition may also switch `current` on the
executing core.  Citing the base transition's theorem for this arm broke the
inventory's own round-5 rule (a live entry must name the function the dispatch
calls), and the round-34 wrapper rework is what broke it.

Stated at the base transition's write set so one set covers both settings: the
gated branch writes a strict subset, which
`resumeThreadEnqueueOnly_confinedToCores` records separately. -/
theorem resumeThreadOnCoreLive_confinedToCores (st st' : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (hStep : Lifecycle.Suspend.resumeThreadOnCoreLive st vtid executingCore
      = .ok (st', sgi)) :
    observableSlotsConfinedToCores st st'
      (resumeThreadOnCoreWriteSet st vtid executingCore) := by
  unfold Lifecycle.Suspend.resumeThreadOnCoreLive at hStep
  split at hStep
  · exact resumeThreadOnCore_confinedToCores st st' vtid executingCore sgi hStep
  · refine observableSlotsConfinedToCores_mono ?_
      (resumeThreadEnqueueOnly_confinedToCores st st' vtid executingCore sgi hStep)
    intro c hc
    simp only [List.mem_singleton] at hc
    simp [resumeThreadOnCoreWriteSet, hc]

/-- SM8.B.3 (**the live `.tcbResume` non-interference, at the function the arm
calls**): resuming a thread onto its home core is invisible to any core outside
the write set, in **both** settings of the context-restore seam and with no
hypothesis on the resumed thread's clearance.

Holding in both settings is the point: it is what makes the SM9.E flip a
one-constant change that owes no new information-flow proof. -/
theorem resumeThreadOnCoreLive_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (st st' : SystemState) (vtid : SeLe4n.ValidThreadId)
    (executingCore : CoreId) (sgi : Option (CoreId × Concurrency.SgiKind)) (c : CoreId)
    (hStep : Lifecycle.Suspend.resumeThreadOnCoreLive st vtid executingCore
      = .ok (st', sgi))
    (hne : c ∉ resumeThreadOnCoreWriteSet st vtid executingCore)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (resumeThreadOnCoreLive_confinedToCores st st' vtid executingCore sgi hStep)
    hShared

-- ============================================================================
-- §5g  The live `.send` arm
-- ============================================================================
--
-- PR #861 review round 10 found this arm calling the boot-pinned
-- `endpointSendDualWithCaps`.  Both of its scheduling effects target the boot
-- core: a rendezvous receiver is woken with `ensureRunnable` (so a receiver
-- homed elsewhere lands on a run queue its own core never dispatches from) and
-- a sender with nobody waiting is descheduled with `removeRunnable` (so a
-- sender blocking on a secondary core stays current and runnable there).  The
-- arm is rerouted through `endpointSendDualWithCapsOnCore`; this section is the
-- per-core audit that reroute owes.

/-- SM8.B.2: **the cores a cross-core endpoint send may write.**

Sharper than its `.call` sibling, because a send has *one* scheduling effect
rather than two:

* **rendezvous** — the receive queue offers a partner, so the send wakes it on
  **its** home core and returns; the sender keeps running, so the executing core
  is untouched;
* **block** — nobody is waiting, so the sender is descheduled on the **executing**
  core and no other core moves.

The receiver is resolved from the pre-state through SM6.A's own
`endpointCallReceiver?` — the receive-queue head, which is the same rendezvous
partner a `.call` would take, so send and call name it once rather than twice. -/
def endpointSendWriteSet (st : SystemState) (endpointId : SeLe4n.ObjId)
    (executingCore : CoreId) : List CoreId :=
  match endpointCallReceiver? st endpointId with
  | some receiver => [determineTargetCore st receiver]
  | none => [executingCore]

/-- SM8.B.2 (**the bare cross-core send bound**): `endpointSendDualOnCore` writes
no core outside `endpointSendWriteSet`.

Rendezvous path: pop the receive queue, store the receiver's message, **wake it
on its home core** — `[] ++ [] ++ [receiverHome]`.  Naming `receiverHome` at the
*pre-state* is what the §1a frame layer buys: neither the pop nor the store is a
migration, so the affinity the wake reads is the affinity the write set read.
Block path: enqueue the sender, store its blocked state, **deschedule it on its
own core** — `[] ++ [] ++ [executingCore]`.  Every fail-closed arm returns the
pre-state and writes nothing. -/
theorem endpointSendDualOnCore_confinedToCores (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    observableSlotsConfinedToCores st
      (endpointSendDualOnCore endpointId sender msg executingCore st).1
      (endpointSendWriteSet st endpointId executingCore) := by
  unfold endpointSendDualOnCore endpointSendWriteSet endpointCallReceiver?
  split
  · exact observableSlotsConfinedToCores_of_eq _ rfl
  · split
    · exact observableSlotsConfinedToCores_of_eq _ rfl
    · cases hEp : st.getEndpoint? endpointId with
      | none =>
        simp only []
        split <;> exact observableSlotsConfinedToCores_of_eq _ rfl
      | some ep =>
        simp only []
        cases hHead : ep.receiveQ.head with
        | none =>
          -- Block path: the sender stops on the core it is running on.
          simp only []
          split
          · exact observableSlotsConfinedToCores_of_eq _ rfl
          · next st1 hEnq =>
            split
            · exact observableSlotsConfinedToCores_of_eq _ rfl
            · next st2 hMsg =>
              exact observableSlotsConfinedToCores_trans
                (observableSlotsConfinedToCores_trans
                  (endpointQueueEnqueue_confinedToCores endpointId false sender st st1 hEnq)
                  (storeTcbIpcStateAndMessage_confinedToCores st1 st2 sender _ _ hMsg))
                (removeRunnableOnCore_confinedToCores st2 sender executingCore)
        | some headRecv =>
          -- Rendezvous path: the receiver wakes on its own home core.
          simp only []
          split
          · exact observableSlotsConfinedToCores_of_eq _ rfl
          · next recvTid recvTcb st1 hPop =>
            split
            · exact observableSlotsConfinedToCores_of_eq _ rfl
            · next st2 hMsgR =>
              have hEpObj : st.objects[endpointId]? = some (.endpoint ep) :=
                (SystemState.getEndpoint?_eq_some_iff st endpointId ep).mp hEp
              have hPopHead : ep.receiveQ.head = some recvTid := by
                have h := endpointQueuePopHead_returns_head endpointId true st ep recvTid
                  st1 hEpObj hPop
                simpa using h
              have hRecv : recvTid = headRecv := by
                rw [hHead] at hPopHead; simpa using hPopHead.symm
              have hInv1 : st1.objects.invExt :=
                endpointQueuePopHead_preserves_objects_invExt endpointId true st st1
                  recvTid recvTcb hObjInv hPop
              have hT1 : determineTargetCore st1 recvTid = determineTargetCore st recvTid :=
                endpointQueuePopHead_determineTargetCore_eq endpointId true st st1
                  recvTid recvTcb recvTid hObjInv hPop
              have hT2 : determineTargetCore st2 recvTid = determineTargetCore st1 recvTid :=
                storeTcbReceiveComplete_determineTargetCore_eq st1 st2 recvTid
                  (some msg) recvTid hInv1 hMsgR
              have hChain := observableSlotsConfinedToCores_widen_cons
                (observableSlotsConfinedToCores_trans
                  (endpointQueuePopHead_confinedToCores endpointId true st st1 recvTid hPop)
                  (storeTcbReceiveComplete_confinedToCores st1 st2 recvTid (some msg) hMsgR))
                (wakeThread_confinedToCores st2 recvTid executingCore)
              rw [hT2, hT1] at hChain
              rw [← hRecv]
              exact hChain

/-- SM8.B.2: the WithCaps send leaves the bare send's run queues in place — every
arm either *is* the bare send's post-state or is that state after an
`ipcUnwrapCaps`, which preserves the scheduler. -/
theorem endpointSendDualWithCapsOnCore_scheduler_eq (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage) (endpointRights : AccessRightSet)
    (senderCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) :
    (endpointSendDualWithCapsOnCore endpointId sender msg endpointRights senderCspaceRoot
        receiverSlotBase executingCore st).1.scheduler
      = (endpointSendDualOnCore endpointId sender msg executingCore st).1.scheduler := by
  unfold endpointSendDualWithCapsOnCore
  cases hSend : endpointSendDualOnCore endpointId sender msg executingCore st with
  | mk stSend res =>
    cases res with
    | error e => rfl
    | ok sgi =>
      simp only []
      repeat' split
      all_goals first
        | rfl
        | (rename_i h; exact ipcUnwrapCaps_preserves_scheduler _ _ _ _ _ _ _ _ h)

/-- SM8.B.2: and the register banks, by the same case analysis. -/
theorem endpointSendDualWithCapsOnCore_machine_eq (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage) (endpointRights : AccessRightSet)
    (senderCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) :
    (endpointSendDualWithCapsOnCore endpointId sender msg endpointRights senderCspaceRoot
        receiverSlotBase executingCore st).1.machine
      = (endpointSendDualOnCore endpointId sender msg executingCore st).1.machine := by
  unfold endpointSendDualWithCapsOnCore
  cases hSend : endpointSendDualOnCore endpointId sender msg executingCore st with
  | mk stSend res =>
    cases res with
    | error e => rfl
    | ok sgi =>
      simp only []
      repeat' split
      all_goals first
        | rfl
        | (rename_i h; exact ipcUnwrapCaps_preserves_machine _ _ _ _ _ _ _ _ h)

/-- SM8.B.2 (**the live unchecked `.send` bound**): the WithCaps cross-core send —
the form `dispatchWithCap_send_delegates` says the live arm calls — is confined to
the bare send's write set.  The extra leg is `ipcUnwrapCaps`, which writes no core
at all, so the two forms declare the same per-core footprint. -/
theorem endpointSendDualWithCapsOnCore_confinedToCores (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage) (endpointRights : AccessRightSet)
    (senderCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) (hObjInv : st.objects.invExt) :
    observableSlotsConfinedToCores st
      (endpointSendDualWithCapsOnCore endpointId sender msg endpointRights senderCspaceRoot
        receiverSlotBase executingCore st).1
      (endpointSendWriteSet st endpointId executingCore) := by
  have h := observableSlotsConfinedToCores_trans
    (endpointSendDualOnCore_confinedToCores endpointId sender msg executingCore st hObjInv)
    (observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
      (endpointSendDualWithCapsOnCore_scheduler_eq endpointId sender msg endpointRights
        senderCspaceRoot receiverSlotBase executingCore st)
      (endpointSendDualWithCapsOnCore_machine_eq endpointId sender msg endpointRights
        senderCspaceRoot receiverSlotBase executingCore st))
  simpa using h

/-- SM8.B.2 (**the live checked `.send` bound**): the flow-checked cross-core send
is confined to the same set.  Its three gates — two bounds checks and the
`sender → endpoint` flow guard — each return the pre-state, which writes nothing;
past them it *is* the unchecked form. -/
theorem endpointSendCrossCoreDispatchChecked_confinedToCores (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet) (senderCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) :
    observableSlotsConfinedToCores st
      (endpointSendCrossCoreDispatchChecked ctx endpointId sender msg endpointRights
        senderCspaceRoot receiverSlotBase executingCore st).1
      (endpointSendWriteSet st endpointId executingCore) := by
  unfold endpointSendCrossCoreDispatchChecked
  split
  · exact observableSlotsConfinedToCores_of_eq _ rfl
  · split
    · exact observableSlotsConfinedToCores_of_eq _ rfl
    · split
      · exact endpointSendDualWithCapsOnCore_confinedToCores endpointId sender msg
          endpointRights senderCspaceRoot receiverSlotBase executingCore st hObjInv
      · exact observableSlotsConfinedToCores_of_eq _ rfl

/-- SM8.B.2 (**the live unchecked `.send` non-interference**): a cross-core send is
invisible on every core outside `endpointSendWriteSet`, with no hypothesis on the
clearance of the sender or of the woken receiver. -/
theorem endpointSendDualWithCapsOnCore_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet) (senderCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hne : c ∉ endpointSendWriteSet st endpointId executingCore)
    (hShared : sharedViewUnchanged ctx observer st
      (endpointSendDualWithCapsOnCore endpointId sender msg endpointRights senderCspaceRoot
        receiverSlotBase executingCore st).1) :
    projectStateOnCore ctx observer
        (endpointSendDualWithCapsOnCore endpointId sender msg endpointRights senderCspaceRoot
          receiverSlotBase executingCore st).1 c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (endpointSendDualWithCapsOnCore_confinedToCores endpointId sender msg endpointRights
      senderCspaceRoot receiverSlotBase executingCore st hObjInv)
    hShared

/-- SM8.B.2 (**the live checked `.send` non-interference**). -/
theorem endpointSendCrossCoreDispatchChecked_crossCoreNonInterference
    (ctx : LabelingContext) (observer : IfObserver) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage) (endpointRights : AccessRightSet)
    (senderCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hne : c ∉ endpointSendWriteSet st endpointId executingCore)
    (hShared : sharedViewUnchanged ctx observer st
      (endpointSendCrossCoreDispatchChecked ctx endpointId sender msg endpointRights
        senderCspaceRoot receiverSlotBase executingCore st).1) :
    projectStateOnCore ctx observer
        (endpointSendCrossCoreDispatchChecked ctx endpointId sender msg endpointRights
          senderCspaceRoot receiverSlotBase executingCore st).1 c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (endpointSendCrossCoreDispatchChecked_confinedToCores ctx endpointId sender msg
      endpointRights senderCspaceRoot receiverSlotBase executingCore st hObjInv)
    hShared

-- ============================================================================
-- §5h  The live SchedContext arms
-- ============================================================================
--
-- PR #861 review round 14, and a direct consequence of this cut's own change:
-- `schedContextBind` / `schedContextConfigure` / `schedContextUnbind` used to
-- re-bucket and preempt against `bootCoreId`, so they wrote no remote core and
-- had no business in this inventory.  Routing them through `determineTargetCore`
-- makes them genuine remote writers, and a remote writer without a write set is
-- exactly the gap this module exists to close.

/-- SM8.B.2: the thread a SchedContext operation's scheduler effects act on,
resolved from the pre-state — the SC's bound thread, if it has one. -/
def schedContextSubject? (st : SystemState) (scObjId : SeLe4n.ObjId) :
    Option SeLe4n.ThreadId :=
  match st.getSchedContext? (SeLe4n.SchedContextId.ofObjId scObjId) with
  | some sc => sc.boundThread
  | none    => none

/-- SM8.B.2: **the cores `.schedContextUnbind` and `.schedContextConfigure` may
write** — the bound thread's home core alone.

Both have a single scheduling effect (clear-and-requeue, or re-bucket) and after
this cut both land on `determineTargetCore` of the SC's bound thread.  An SC with
no bound thread has no scheduling effect at all, hence the empty set.

**Not `.schedContextBind`**, which resolves its thread from an *argument*:
binding rejects an SC that already has one (`sc.boundThread.isSome → .error
.illegalState`), so on every success path this set is empty while bind does write
a run queue.  `schedContextBindWriteSet` is its write set.  (The earlier wording
here claimed to cover "every one of these operations", which was false for bind
— PR #861 review round 14.) -/
def schedContextWriteSet (st : SystemState) (scObjId : SeLe4n.ObjId) : List CoreId :=
  match schedContextSubject? st scObjId with
  | some tid => [determineTargetCore st tid]
  | none     => []

/-- SM8.B.2: **the cores a `.schedContextUnbind` may write** — the subject's
home core *and* the core actually running it.

Deliberately **not** `schedContextWriteSet` (PR #861 review round 39/40).  The
two differ, and the difference is the defect this set exists to make visible:
the run-queue re-bucket lands on the subject's **home** core, while the
preemption guard clears `current` on the core actually **running** it.  Those
coincide whenever affinity is set — a thread is only dispatched on a core its
affinity admits — and diverge for an unbound-affinity thread running on a
secondary core, which is admitted (see `runningCoreOf?`).

Keeping `schedContextWriteSet` at the singleton keeps `.schedContextConfigure`'s
bound sharp: configure only re-buckets, so the running core is not in its
footprint and declaring it would weaken a statement for no reason. -/
def schedContextUnbindWriteSet (st : SystemState) (scObjId : SeLe4n.ObjId) :
    List CoreId :=
  match schedContextSubject? st scObjId with
  | some tid => determineTargetCore st tid :: (runningCoreOf? st tid).toList
  | none     => []

/-- SM8.B.2 (**the live `.schedContextUnbind` bound**): unbinding writes no core
outside `schedContextUnbindWriteSet`.

The transition's scheduler effects are a `setCurrentOnCore` at the subject's
**running** core and a `setRunQueueOnCore` at its **home** core, plus a
`setReplenishQueueOnCore` — which touches no confined slot, the replenish queue
being outside the six `observableSlotsConfinedToCores` fields.  Everything else
it does is object-store and index writes.

The two cores are named separately because they genuinely differ (PR #861
review rounds 40/42): for an affinity-free thread running on a secondary core
the home is the boot core while `runningCoreOf?` is the secondary one, and the
transition must clear the slot that actually holds the thread while re-queueing
it where the next selection looks.  That is why `schedContextUnbindWriteSet`
names both, and why it is a set of its own rather than `schedContextWriteSet` —
`.schedContextConfigure` only re-buckets, so declaring the running core there
would weaken its bound for nothing. -/
theorem schedContextUnbind_confinedToCores (vScId : SeLe4n.ValidObjId)
    (st st' : SystemState)
    (hStep : SchedContextOps.schedContextUnbind vScId st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' (schedContextUnbindWriteSet st vScId.val) := by
  unfold SchedContextOps.schedContextUnbind schedContextUnbindWriteSet
    schedContextSubject? at *
  split at hStep
  · next sc hSc =>
    simp only [hSc]
    split at hStep
    · exact absurd hStep (by simp)
    · next tid hBound =>
      simp only [hBound]
      split at hStep
      · next tcb hTcb =>
        rw [Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨-, hs⟩ := hStep
        subst hs
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c hc <;>
          -- Two cores now: the re-bucket's home core and the guard's running
          -- core.  `hc` rules out both; orient each disequality the way the
          -- `_ne` lemmas expect before simplifying.
          simp only [List.mem_cons, Option.mem_toList, not_or] at hc <;>
          (have hne : determineTargetCore st tid ≠ c := fun h => hc.1 h.symm) <;>
          (have hcRun : runningCoreOf? st tid ≠ some c := hc.2) <;>
          (repeat' split) <;>
          -- the replenish-queue setters are not in this transition's footprint;
          -- their five frames were carried here and never fired
          simp_all [SchedulerState.setCurrentOnCore_runQueueOnCore,
            SchedulerState.setRunQueueOnCore_runQueueOnCore_ne,
            SchedulerState.setCurrentOnCore_currentOnCore_ne,
            SchedulerState.setRunQueueOnCore_currentOnCore,
            SchedulerState.setCurrentOnCore_activeDomainOnCore,
            SchedulerState.setRunQueueOnCore_activeDomainOnCore,
            SchedulerState.setCurrentOnCore_domainTimeRemainingOnCore,
            SchedulerState.setRunQueueOnCore_domainTimeRemainingOnCore,
            SchedulerState.setCurrentOnCore_domainScheduleIndexOnCore,
            SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore]
      · next hNoTcb =>
        rw [Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨-, hs⟩ := hStep
        subst hs
        exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
               fun _ _ => rfl, fun _ _ => rfl⟩
  · exact absurd hStep (by simp)

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


/-- SM8.B.2: **the cores a `.schedContextBind` may write** — the bound thread's
home core.

Deliberately **not** `schedContextWriteSet`: bind rejects an SC that already has
a bound thread (`sc.boundThread.isSome → .error .illegalState`), so on every
success path `schedContextSubject?` is `none` and that set is empty — while bind
genuinely writes a run queue.  The thread is an argument here, so this reads it
directly. -/
def schedContextBindWriteSet (st : SystemState) (tid : SeLe4n.ThreadId) : List CoreId :=
  [determineTargetCore st tid]

/-- SM8.B.2 (**the live `.schedContextBind` bound**): binding writes no core
outside the bound thread's home core.

Bind has exactly one scheduling effect — the re-bucket this cut routed through
`determineTargetCore` — reached across two object writes, and the work is the
home-core bridge: the transition computes its target two inserts later than the
write set names it.  Neither insert is a migration.  The SchedContext insert
leaves every TCB lookup alone (`getTcb?_insert_schedContext_eq`); the TCB insert
rewrites `schedContextBinding` and `priority`, never `cpuAffinity`
(`determineTargetCore_insert_tcb`).

The bridge is **transported into the disequality** rather than rewritten into the
goal: the post-state is a structure literal far too large to restate, but
`hHome ▸ hne` gives the setter's own frame lemma exactly the hypothesis it
wants, and `exact` closes the rest up to definitional equality. -/
theorem schedContextBind_confinedToCores (vScId : SeLe4n.ValidObjId)
    (vThreadId : SeLe4n.ValidThreadId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : SchedContextOps.schedContextBind vScId vThreadId st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' (schedContextBindWriteSet st vThreadId.val) := by
  unfold SchedContextOps.schedContextBind at hStep
  split at hStep
  · next sc hSc =>
    split at hStep
    · exact absurd hStep (by simp)
    · split at hStep
      · next tcb hTcb =>
        split at hStep
        · exact absurd hStep (by simp)
        · split at hStep
          · next hUnbound =>
            rw [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨-, hs⟩ := hStep
            subst hs
            let sc1 : SchedContext := { sc with boundThread := some vThreadId.val }
            let scObj : KernelObject := .schedContext sc1
            let st1 : SystemState := { st with objects := st.objects.insert vScId.val scObj }
            let tcb1 : TCB :=
              { tcb with schedContextBinding := SchedContextBinding.bound ⟨vScId.val.toNat⟩,
                         priority := sc.priority }
            let tcbObj : KernelObject := .tcb tcb1
            let st2 : SystemState :=
              { st1 with objects := st1.objects.insert vThreadId.val.toObjId tcbObj }
            have hScRaw : st.objects.get? vScId.val = some (.schedContext sc) := by
              simpa using (SystemState.getSchedContext?_eq_some_iff st
                (SeLe4n.SchedContextId.ofObjId vScId.val) sc).mp hSc
            have hT1 : ∀ x : SeLe4n.ThreadId, st1.getTcb? x = st.getTcb? x := fun x =>
              getTcb?_insert_schedContext_eq st st1
                (SeLe4n.SchedContextId.ofObjId vScId.val) sc sc1 hObjInv
                (by simpa using hScRaw) rfl x
            have hInv1 : st1.objects.invExt :=
              SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt _ _ _ hObjInv
            have hTcb1 : st1.objects.get? vThreadId.val.toObjId = some (.tcb tcb) := by
              have h := hT1 vThreadId.val
              rw [hTcb] at h
              simpa using (SystemState.getTcb?_eq_some_iff st1 vThreadId.val tcb).mp h
            have hHome : determineTargetCore st2 vThreadId.val
                = determineTargetCore st vThreadId.val := by
              refine Eq.trans (determineTargetCore_insert_tcb st1 st2 vThreadId.val tcb tcb1
                hInv1 hTcb1 rfl rfl vThreadId.val) ?_
              exact determineTargetCore_congr st st1 vThreadId.val (by rw [hT1 vThreadId.val])
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c hc <;>
              simp only [schedContextBindWriteSet, List.mem_singleton] at hc
            · have hne : determineTargetCore st vThreadId.val ≠ c := fun h => hc h.symm
              split
              · exact SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ c _ (hHome ▸ hne)
              · rfl
            · split
              · exact SchedulerState.setRunQueueOnCore_currentOnCore _ _ c _
              · rfl
            · split
              · exact SchedulerState.setRunQueueOnCore_activeDomainOnCore _ _ c _
              · rfl
            · split
              · exact SchedulerState.setRunQueueOnCore_domainTimeRemainingOnCore _ _ c _
              · rfl
            · split
              · exact SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore _ _ c _
              · rfl
            · -- registers: untouched on both arms, but the projection only
              -- reduces once the run-queue `if` is resolved.
              split <;> rfl
          · exact absurd hStep (by simp)
      · exact absurd hStep (by simp)
  · exact absurd hStep (by simp)

/-- SM8.B.2: **where a `.tcbSetAffinity` writes.**

The old home core and the new one.  Unlike bind and configure, the second core
needs no state at all: `setThreadCpuAffinity` inserts the TCB with
`cpuAffinity := affinity` and `determineTargetCore` reads exactly that field, so
the post-migration home is a function of the *argument*.  That is what
`setThreadCpuAffinity_determineTargetCore_eq` says, and it is why this write set
avoids the mid-state bridge its two SchedContext siblings needed. -/
def setThreadCpuAffinityWriteSet (st : SystemState) (tid : SeLe4n.ThreadId)
    (affinity : Option CoreId) : List CoreId :=
  [determineTargetCore st tid, affinity.getD Concurrency.bootCoreId]

/-- SM8.B.2: the affinity write touches the object store only. -/
theorem setThreadCpuAffinity_scheduler_machine_eq (st stSet : SystemState)
    (tid : SeLe4n.ThreadId) (affinity : Option CoreId)
    (hSet : setThreadCpuAffinity st tid affinity = .ok stSet) :
    stSet.scheduler = st.scheduler ∧ stSet.machine = st.machine := by
  unfold setThreadCpuAffinity at hSet
  split at hSet
  · rw [Except.ok.injEq] at hSet; subst hSet; exact ⟨rfl, rfl⟩
  · exact absurd hSet (by simp)

/-- SM8.B.2: after the affinity write the thread's home core IS the requested
affinity (boot when unbound) — the bridge that lets the write set name the new
core without mentioning the mid-state. -/
theorem setThreadCpuAffinity_determineTargetCore_eq (st stSet : SystemState)
    (tid : SeLe4n.ThreadId) (affinity : Option CoreId) (hInv : st.objects.invExt)
    (hSet : setThreadCpuAffinity st tid affinity = .ok stSet) :
    determineTargetCore stSet tid = affinity.getD Concurrency.bootCoreId := by
  unfold setThreadCpuAffinity at hSet
  split at hSet
  · next tcb hTcb =>
    rw [Except.ok.injEq] at hSet
    subst hSet
    unfold determineTargetCore SystemState.getTcb?
    simp only [RHTable_getElem?_eq_get?]
    rw [RHTable_getElem?_insert st.objects tid.toObjId
      (.tcb { tcb with cpuAffinity := affinity }) hInv tid.toObjId]
    simp only [beq_self_eq_true, if_pos]
    cases affinity <;> rfl
  · exact absurd hSet (by simp)

/-- SM8.B.2 (**the live `.tcbSetAffinity` bound**): a migration writes no core
outside the pair it moves the thread between.

Three effects, one of them confined-relevant.  The `setThreadCpuAffinity` write
touches the object store only (`setThreadCpuAffinity_scheduler_machine_eq`); the
replenishment migration is per-core silent even on the cores it names
(`migrateSchedContextReplenishment_confinedToCores`, against the *empty* set,
because the replenish queue is outside the six observable slots); and the
run-queue migration is bounded by
`migrateRunQueueOnAffinityChange_confinedToCores`, new in this cut and the
reason `.tcbSetAffinity` could not carry a proof before it.

Read as a chain: `st` and the post-affinity state share every observable slot,
the replenishment stage preserves all of them, and the run-queue stage moves
only the two cores the write set names — the second of which is the *argument*,
via the bridge above. -/
theorem setThreadCpuAffinityWithMigration_confinedToCores
    (st st' : SystemState) (targetTid : SeLe4n.ThreadId)
    (affinity : Option CoreId) (executingCore : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind)) (hInv : st.objects.invExt)
    (hStep : setThreadCpuAffinityWithMigration st targetTid affinity executingCore
      = .ok (st', sgi)) :
    observableSlotsConfinedToCores st st'
      (setThreadCpuAffinityWriteSet st targetTid affinity) := by
  unfold setThreadCpuAffinityWithMigration at hStep
  split at hStep
  · next tcb hTcb =>
    split at hStep
    · exact absurd hStep (by simp)
    · split at hStep
      · next stSet hSet =>
        rw [Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨hs, -⟩ := hStep
        subst hs
        obtain ⟨hSched, hMach⟩ :=
          setThreadCpuAffinity_scheduler_machine_eq st stSet targetTid affinity hSet
        have hNew := setThreadCpuAffinity_determineTargetCore_eq st stSet targetTid affinity
          hInv hSet
        -- The mid-state after the (optional) replenishment migration.  Written
        -- out rather than named: `set` cannot bind a `match` body here.
        have hRepl : observableSlotsConfinedToCores stSet
            (match tcb.schedContextBinding.scId? with
              | some scId => migrateSchedContextReplenishment stSet scId
                  (determineTargetCore st targetTid) (determineTargetCore stSet targetTid)
              | none => stSet) [] := by
          cases tcb.schedContextBinding.scId? with
          | none => exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
                           fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
          | some scId => exact migrateSchedContextReplenishment_confinedToCores _ _ _ _
        have hRun := migrateRunQueueOnAffinityChange_confinedToCores
          (match tcb.schedContextBinding.scId? with
            | some scId => migrateSchedContextReplenishment stSet scId
                (determineTargetCore st targetTid) (determineTargetCore stSet targetTid)
            | none => stSet) targetTid
          (determineTargetCore st targetTid) (determineTargetCore stSet targetTid)
        have key : ∀ c, c ∉ setThreadCpuAffinityWriteSet st targetTid affinity →
            c ∉ [determineTargetCore st targetTid, determineTargetCore stSet targetTid] := by
          intro c hc
          simp only [setThreadCpuAffinityWriteSet, List.mem_cons, List.not_mem_nil,
            or_false, not_or] at hc ⊢
          rw [hNew]
          exact hc
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals intro c hc
        all_goals have hcPair := key c hc
        · exact ((hRun.runQueue c hcPair).trans (hRepl.runQueue c (by simp))).trans
            (by rw [hSched])
        · exact ((hRun.current c hcPair).trans (hRepl.current c (by simp))).trans
            (by rw [hSched])
        · exact ((hRun.activeDomain c hcPair).trans (hRepl.activeDomain c (by simp))).trans
            (by rw [hSched])
        · exact ((hRun.domainTimeRemaining c hcPair).trans
            (hRepl.domainTimeRemaining c (by simp))).trans (by rw [hSched])
        · exact ((hRun.domainScheduleIndex c hcPair).trans
            (hRepl.domainScheduleIndex c (by simp))).trans (by rw [hSched])
        · exact ((hRun.regs c hcPair).trans (hRepl.regs c (by simp))).trans (by rw [hMach])
      · exact absurd hStep (by simp)
  · exact absurd hStep (by simp)

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

/-- SM8.B.2 (**the live `.schedContextConfigure` bound**): a configure writes no
core outside its subject's home core.

Two scheduler writes, and only one of them is confined-relevant: the
replenish-queue purge is outside the six observable slots, so it is per-core
silent even on the core it names.  The run-queue re-bucket needs the same
home-core bridge as bind, one hop longer — the target is computed after the
replenish write (scheduler-only, objects untouched), the `storeObject` of the
reconfigured SchedContext (`storeObject_schedContext_determineTargetCore_eq`) and
the TCB **priority** insert, which is not a migration.

The `boundThread = none` and `getTcb? = none` arms perform no scheduling work at
all, and the trailing domain propagation is an object write. -/
theorem schedContextConfigure_confinedToCores (vScId : SeLe4n.ValidObjId)
    (budget period priority deadline domain : Nat) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : SchedContextOps.schedContextConfigure vScId budget period priority deadline domain st
      = .ok ((), st')) :
    observableSlotsConfinedToCores st st' (schedContextWriteSet st vScId.val) := by
  unfold SchedContextOps.schedContextConfigure schedContextWriteSet schedContextSubject? at *
  split at hStep
  · exact absurd hStep (by simp)
  · split at hStep
    · next sc hSc =>
      simp only [hSc]
      -- Zeta-reduce the `let updated := …` binder so the admission guard is a
      -- splittable `if` rather than a `have`-wrapped one.
      simp only [] at hStep
      split at hStep
      · -- admission granted
        split at hStep
        · exact absurd hStep (by simp)
        · next stStored hStore =>
          have hScRaw : st.objects.get? vScId.val = some (.schedContext sc) := by
            simpa using (SystemState.getSchedContext?_eq_some_iff st
              (SeLe4n.SchedContextId.ofObjId vScId.val) sc).mp hSc
          split at hStep
          · -- no bound thread: no scheduling effect at all
            next hNone =>
            simp only [hNone]
            rw [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨-, hs⟩ := hStep
            subst hs
            exact observableSlotsConfinedToCores_trans
              (purgeReplenishmentOnCore_confinedToCores st _ _)
              (observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
                (storeObject_scheduler_eq _ _ _ _ hStore)
                (storeObject_machine_eq _ _ _ _ hStore))
          · next boundTid hBound =>
            simp only [hBound]
            have hInvStored : stStored.objects.invExt :=
              -- Named again for the same reason: the store's pre-state is the
              -- post-replenish one, not `st`.
              -- `by exact` postpones these until `hStore` has fixed the
              -- pre-state; passed directly they pin it to `st` first.
              storeObject_preserves_objects_invExt (st' := stStored) (hStore := hStore)
                (hObjInv := by exact hObjInv)
            -- The SchedContext store is not a migration, and the replenish write
            -- leaves `objects` alone, so the home core is already the pre-state's.
            have hHomeStored : ∀ x : SeLe4n.ThreadId,
                determineTargetCore stStored x = determineTargetCore st x := fun x => by
              -- The lemma's own conclusion names the store's pre-state — the
              -- post-replenish one.  Ascribing the statement up front would pin
              -- that to `st` and the store hypothesis would stop matching, so it
              -- is elaborated unascribed and closed by defeq: the replenish
              -- write leaves `objects`, and `determineTargetCore` reads nothing
              -- else.
              have h := storeObject_schedContext_determineTargetCore_eq (x := x) (sc := sc)
                (hStore := hStore) (hPre := by exact hScRaw) (hObjInv := by exact hObjInv)
              exact h
            split at hStep
            · next boundTcb hTcbStored =>
              have hTcbStoredRaw :
                  stStored.objects.get? boundTid.toObjId = some (.tcb boundTcb) := by
                simpa using (SystemState.getTcb?_eq_some_iff stStored boundTid boundTcb).mp
                  hTcbStored
              let boundTcb2 : TCB := { boundTcb with priority := ⟨priority⟩ }
              let boundObj : KernelObject := .tcb boundTcb2
              let stWithTcb : SystemState :=
                { stStored with objects := stStored.objects.insert boundTid.toObjId boundObj }
              have hHomeWith : determineTargetCore stWithTcb boundTid
                  = determineTargetCore st boundTid :=
                Eq.trans
                  (determineTargetCore_insert_tcb stStored stWithTcb boundTid boundTcb boundTcb2
                    hInvStored hTcbStoredRaw rfl rfl boundTid)
                  (hHomeStored boundTid)
              rw [Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨-, hs⟩ := hStep
              subst hs
              -- The prefix common to every arm: replenish purge then the SC
              -- store, neither of which is confined-relevant.
              have hStoredConf : observableSlotsConfinedToCores st stStored [] :=
                observableSlotsConfinedToCores_trans
                  (purgeReplenishmentOnCore_confinedToCores st _ _)
                  (observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
                    (storeObject_scheduler_eq _ _ _ _ hStore)
                    (storeObject_machine_eq _ _ _ _ hStore))
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c hc <;>
                simp only [List.mem_singleton] at hc <;>
                (have hne : determineTargetCore stWithTcb boundTid ≠ c := by
                  rw [hHomeWith]; exact fun h => hc h.symm) <;>
                -- Hoisted: a nested `by simp` inside a `first` alternative throws
                -- rather than backtracking, so the alternatives below carry no
                -- tactic blocks of their own.
                (have hNil : c ∉ ([] : List CoreId) := by simp) <;>
                (repeat' split) <;>
                first
                  -- arms that stop at `stStored` / `stWithTcb` (object writes only)
                  | exact hStoredConf.runQueue c hNil
                  | exact hStoredConf.current c hNil
                  | exact hStoredConf.activeDomain c hNil
                  | exact hStoredConf.domainTimeRemaining c hNil
                  | exact hStoredConf.domainScheduleIndex c hNil
                  | exact hStoredConf.regs c hNil
                  -- arms that additionally take the run-queue re-bucket
                  | (rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ c _ hne]
                     exact hStoredConf.runQueue c hNil)
                  | (rw [SchedulerState.setRunQueueOnCore_currentOnCore]
                     exact hStoredConf.current c hNil)
                  | (rw [SchedulerState.setRunQueueOnCore_activeDomainOnCore]
                     exact hStoredConf.activeDomain c hNil)
                  | (rw [SchedulerState.setRunQueueOnCore_domainTimeRemainingOnCore]
                     exact hStoredConf.domainTimeRemaining c hNil)
                  | (rw [SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore]
                     exact hStoredConf.domainScheduleIndex c hNil)
                  | rfl
            · -- the bound TCB vanished behind the store: no scheduling effect
              next hNoTcb =>
              rw [Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨-, hs⟩ := hStep
              subst hs
              refine observableSlotsConfinedToCores_widen_any ?_
              exact observableSlotsConfinedToCores_trans
                (purgeReplenishmentOnCore_confinedToCores st _ _)
                (observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
                  (storeObject_scheduler_eq _ _ _ _ hStore)
                  (storeObject_machine_eq _ _ _ _ hStore))
      · exact absurd hStep (by simp)
    · exact absurd hStep (by simp)

/-- SM8.B.2 (**the live `.schedContextConfigure` non-interference**): a configure
is invisible on every core outside its subject's home core. -/
theorem schedContextConfigure_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (vScId : SeLe4n.ValidObjId)
    (budget period priority deadline domain : Nat) (st st' : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hStep : SchedContextOps.schedContextConfigure vScId budget period priority deadline domain st
      = .ok ((), st'))
    (hne : c ∉ schedContextWriteSet st vScId.val)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (schedContextConfigure_confinedToCores vScId budget period priority deadline domain
      st st' hObjInv hStep) hShared

/-- SM8.B.2: **the cores the live `.schedContextUnbind` may write** — the demoted
thread's home core, where the revocation re-buckets it, and the executing core,
which runs the demotion's scheduling point inline.

The scheduling point is what PR #861 review round 15 added: revoking a
SchedContext drops the bound thread to its legacy priority, and the single-core
transition cleared its `current` slot with nothing to follow.  When the running
core is remote the seam only *posts* its SGI, so the declared set
over-approximates by one core on that path — over-approximating is the safe
direction, and it is the shape `resumeThreadOnCoreWriteSet` already uses. -/
def schedContextUnbindOnCoreWriteSet (st : SystemState) (scObjId : SeLe4n.ObjId)
    (executingCore : CoreId) : List CoreId :=
  schedContextUnbindWriteSet st scObjId ++ [executingCore]

/-- SM8.B.2 (**the live `.schedContextUnbind` bound**): the per-core unbind
writes no core outside the demoted thread's home and the executing core.

Two legs, composed by `observableSlotsConfinedToCores_trans` — which is why the
write set is literally the concatenation the transition performs: the revocation
(bounded by `schedContextUnbind_confinedToCores`) and the preemption seam
(bounded by `priorityRescheduleOnCore_confinedToCores`).  A rejected unbind never
reaches the seam. -/
theorem schedContextUnbindOnCore_confinedToCores (vScId : SeLe4n.ValidObjId)
    (executingCore : CoreId) (st st' : SystemState)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (hStep : SchedContextOps.schedContextUnbindOnCore vScId executingCore st
      = .ok (st', sgi)) :
    observableSlotsConfinedToCores st st'
      (schedContextUnbindOnCoreWriteSet st vScId.val executingCore) := by
  unfold SchedContextOps.schedContextUnbindOnCore schedContextUnbindOnCoreWriteSet at *
  simp only [] at hStep
  split at hStep
  · exact absurd hStep (by simp)
  · next stMid hUnbind =>
    exact observableSlotsConfinedToCores_trans
      (schedContextUnbind_confinedToCores vScId st stMid hUnbind)
      (priorityRescheduleOnCore_confinedToCores stMid st' _ executingCore true sgi hStep)

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

-- ============================================================================
-- §5i  The live priority-control arms
-- ============================================================================
--
-- PR #861 review round 12 rerouted `.tcbSetPriority` / `.tcbSetMCPriority` off
-- their doubly-boot-pinned operations, and round 15's inventory-completeness
-- check (`scripts/check_live_arm_per_core_routing.py`) observed that the reroute
-- was only half the obligation: a per-core operation can write a core it is not
-- executing on, and nothing here bounded what these two write.  `.tcbSetAffinity`
-- was never rerouted — it has been per-core since SM5.H.4 — and had the same
-- gap for the same reason.

/-- SM8.B.2: rewriting a thread's priority source is per-core silent — it stores
one TCB or one SchedContext and touches neither the scheduler nor a register
bank. -/
theorem updatePrioritySource_confinedToCores (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (newPriority : SeLe4n.Priority) :
    observableSlotsConfinedToCores st
      (SchedContext.PriorityManagement.updatePrioritySource st tid tcb newPriority) [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
    (by unfold SchedContext.PriorityManagement.updatePrioritySource
        repeat' split
        all_goals rfl)
    (by unfold SchedContext.PriorityManagement.updatePrioritySource
        repeat' split
        all_goals rfl)

/-- SM8.B.2: the run-queue bucket migration writes exactly the core it is given.

The generalisation of `migrateRunQueueBucket`, which was pinned to `bootCoreId`
in both its membership test and its write — so a target queued anywhere else got
a silent no-op while its priority field moved (PR #861 review rounds 10 and 12,
the defect this whole layer exists to keep from recurring). -/
theorem migrateRunQueueBucketOnCore_confinedToCores (st : SystemState)
    (tid : SeLe4n.ThreadId) (newPriority : SeLe4n.Priority) (homeCore : CoreId) :
    observableSlotsConfinedToCores st
      (SchedContext.PriorityManagement.migrateRunQueueBucketOnCore st tid newPriority homeCore)
      [homeCore] := by
  unfold SchedContext.PriorityManagement.migrateRunQueueBucketOnCore
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c hc <;>
    simp only [List.mem_singleton] at hc <;>
    (have hne : homeCore ≠ c := fun h => hc h.symm) <;>
    (repeat' split) <;>
    simp_all [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne,
      SchedulerState.setRunQueueOnCore_currentOnCore,
      SchedulerState.setRunQueueOnCore_activeDomainOnCore,
      SchedulerState.setRunQueueOnCore_domainTimeRemainingOnCore,
      SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore]

/-- SM8.B.2: the priority ops' shared state effect — store the new value, then
re-bucket on the given core — writes exactly that core.

Factored out because both ops perform it and because composing it in one step
keeps the intermediate terms small: chaining the two leaves inline forces
`isDefEq` over a fully-expanded mid-state and times out. -/
theorem priorityUpdateAndMigrate_confinedToCores (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (p : SeLe4n.Priority) (home : CoreId) :
    observableSlotsConfinedToCores st
      (SchedContext.PriorityManagement.migrateRunQueueBucketOnCore
        (SchedContext.PriorityManagement.updatePrioritySource st tid tcb p) tid p home)
      [home] :=
  observableSlotsConfinedToCores_widen_cons
    (updatePrioritySource_confinedToCores st tid tcb p)
    (migrateRunQueueBucketOnCore_confinedToCores _ tid p home)

/-- SM8.B.2: the priority ops' **whole** state effect writes the target's home
core and the executing core, and nothing else.

Stated against the named effect `applyPriorityChangeOnCore` rather than its
three composed steps, and over a base-state *variable*.  Both matter: written
out inline, the composition's metavariables (base state, TCB, home core) have to
be recovered by unifying a `migrateRunQueueBucketOnCore (updatePrioritySource …)
…` pattern against a fully-expanded mid-state, which does not terminate at any
heartbeat budget — raising it to a million changed nothing, the same
"term shape, not budget" lesson v0.32.151 recorded.  Named and generalised, the
caller instantiates it with one first-order match against its own `hStep`. -/
theorem applyPriorityChangeOnCore_confinedToCores (base st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (p : SeLe4n.Priority)
    (executingCore : CoreId) (shouldPreempt : Bool)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (hStep : SchedContext.PriorityManagement.applyPriorityChangeOnCore base tid tcb p
      executingCore shouldPreempt = .ok (st', sgi)) :
    observableSlotsConfinedToCores base st' [determineTargetCore base tid, executingCore] :=
  observableSlotsConfinedToCores_trans
    (priorityUpdateAndMigrate_confinedToCores base tid tcb p (determineTargetCore base tid))
    (priorityRescheduleOnCoreLive_confinedToCores _ st' _ executingCore shouldPreempt sgi hStep)

/-- SM8.B.2: **the cores the live `.tcbSetPriority` / `.tcbSetMCPriority` may
write** — the target's home core, where its run-queue bucket migrates, and the
executing core, which runs the demotion's preemption point inline.  A remote
preemption is posted as an SGI, so the set over-approximates by one core there. -/
def priorityControlWriteSet (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) : List CoreId :=
  [determineTargetCore st tid, executingCore]

/-- SM8.B.2 (**the live `.tcbSetPriority` bound**): setting a priority writes no
core outside the target's home and the executing core.

Three legs — the priority-source store (silent), the bucket migration (the home
core), the preemption seam (the executing core) — and the home core is resolved
at the **pre-state**, exactly where `setPriorityOnCore` resolves it, so no
home-core bridge is needed. -/
theorem setPriorityOnCore_confinedToCores (st st' : SystemState)
    (vCallerTid vTargetTid : SeLe4n.ValidThreadId) (newPriority : SeLe4n.Priority)
    (executingCore : CoreId) (sgi : Option (CoreId × Concurrency.SgiKind))
    (hStep : SchedContext.PriorityManagement.setPriorityOnCore st vCallerTid vTargetTid
      newPriority executingCore = .ok (st', sgi)) :
    observableSlotsConfinedToCores st st'
      (priorityControlWriteSet st vTargetTid.val executingCore) := by
  unfold SchedContext.PriorityManagement.setPriorityOnCore priorityControlWriteSet at *
  split at hStep
  · next callerTcb _ =>
    split at hStep
    · exact absurd hStep (by simp)
    · split at hStep
      · next targetTcb hTarget =>
        simp only [] at hStep
        exact applyPriorityChangeOnCore_confinedToCores st st' vTargetTid.val targetTcb
          newPriority executingCore _ sgi hStep
      · exact absurd hStep (by simp)
  · exact absurd hStep (by simp)

/-- SM8.B.3 (**the live `.tcbSetPriority` arm, cross-core**): a priority change is
invisible on every core outside the target's home and the executing core. -/
theorem setPriorityOnCore_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (st st' : SystemState)
    (vCallerTid vTargetTid : SeLe4n.ValidThreadId) (newPriority : SeLe4n.Priority)
    (executingCore c : CoreId) (sgi : Option (CoreId × Concurrency.SgiKind))
    (hStep : SchedContext.PriorityManagement.setPriorityOnCore st vCallerTid vTargetTid
      newPriority executingCore = .ok (st', sgi))
    (hne : c ∉ priorityControlWriteSet st vTargetTid.val executingCore)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (setPriorityOnCore_confinedToCores st st' vCallerTid vTargetTid newPriority
      executingCore sgi hStep) hShared

/-- SM8.B.2 (**the live `.tcbSetMCPriority` bound**): capping a thread's maximum
controlled priority writes no core outside the target's home and the executing
core, and the uncapped path writes no core at all.

One extra hop over `.tcbSetPriority`: the ceiling is stored *before* the home
core is resolved, so the transition reads `determineTargetCore` at a mid-state.
That store rewrites `maxControlledPriority`, never `cpuAffinity`, so it is not a
migration and the §1a bridge `determineTargetCore_insert_tcb` carries the
mid-state core back to the pre-state one the write set names. -/
theorem setMCPriorityOnCore_confinedToCores (st st' : SystemState)
    (vCallerTid vTargetTid : SeLe4n.ValidThreadId) (newMCP : SeLe4n.Priority)
    (executingCore : CoreId) (sgi : Option (CoreId × Concurrency.SgiKind))
    (hObjInv : st.objects.invExt)
    (hStep : SchedContext.PriorityManagement.setMCPriorityOnCore st vCallerTid vTargetTid
      newMCP executingCore = .ok (st', sgi)) :
    observableSlotsConfinedToCores st st'
      (priorityControlWriteSet st vTargetTid.val executingCore) := by
  unfold SchedContext.PriorityManagement.setMCPriorityOnCore priorityControlWriteSet at *
  split at hStep
  · next callerTcb _ =>
    split at hStep
    · exact absurd hStep (by simp)
    · split at hStep
      · next targetTcb hTarget =>
        simp only [] at hStep
        -- The ceiling store: an object write, so per-core silent, and not a
        -- migration — which is what lets the mid-state home core be the
        -- pre-state one.  Both facts are stated over a *generic* post-state
        -- constrained by its fields, so neither has to restate the nested
        -- record-update literal the transition builds.
        have hSilent : ∀ r : SystemState, r.scheduler = st.scheduler →
            r.machine = st.machine → observableSlotsConfinedToCores st r [] :=
          fun _ h1 h2 => observableSlotsConfinedToCores_nil_of_scheduler_machine_eq h1 h2
        have hHome : ∀ (o : KernelObject) (t' : TCB), o = .tcb t' →
            t'.cpuAffinity = targetTcb.cpuAffinity →
            determineTargetCore { st with objects := st.objects.insert vTargetTid.val.toObjId o }
              vTargetTid.val = determineTargetCore st vTargetTid.val := by
          rintro o t' rfl hAff
          exact determineTargetCore_insert_tcb st _ vTargetTid.val targetTcb t' hObjInv
            (by rw [← RHTable_getElem?_eq_get?]
                exact (SystemState.getTcb?_eq_some_iff st vTargetTid.val targetTcb).mp hTarget)
            hAff rfl _
        split at hStep
        · -- `hSilent`'s equations are left as goals rather than given as `rfl`
          -- here: supplied eagerly they would force Lean to solve
          -- `?r.scheduler =?= st.scheduler` for an unknown `?r`, and projecting a
          -- metavariable sends `whnf` into the fully-expanded 27-field mid-state
          -- record.  Deferred, `?r` is fixed first by the second leg and both
          -- close by `rfl`.
          refine observableSlotsConfinedToCores_mono ?_
            (observableSlotsConfinedToCores_trans (hSilent _ ?_ ?_)
              (applyPriorityChangeOnCore_confinedToCores _ st' vTargetTid.val _ newMCP
                executingCore true sgi hStep))
          · intro c hc
            simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
            rcases hc with hc | hc
            · exact Or.inl (hc ▸ hHome _ _ rfl rfl)
            · exact Or.inr hc
          · rfl
          · rfl
        · rw [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨hs, -⟩ := hStep
          subst hs
          exact observableSlotsConfinedToCores_widen_any (hSilent _ rfl rfl)
      · exact absurd hStep (by simp)
  · exact absurd hStep (by simp)

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

-- ============================================================================
-- §5j  The live memory-subsystem arms
-- ============================================================================
--
-- `.vspaceMap`, `.vspaceUnmap` and `.lifecycleRetype` route through per-core
-- wrappers (they take an `executingCore`), so round 15's inventory-completeness
-- check demands an entry for each.  Their entry is the **strongest** one this
-- module can carry: an *empty* write set.  Every field these wrappers touch
-- beyond the object store — `tlb`, `perCoreTlb`, `tlbShootdown`,
-- `perCoreICache`, `pendingIcacheMaintenance` — is proven outside the per-core
-- observer's read set by SM8.A (`onCore_perCore_independence` and its
-- corollaries), and none of them writes a scheduler slot or a register bank on
-- any core at all.
--
-- Stating that as a theorem rather than as an exception matters: an allowlist
-- entry is invisible to `crossCoreNiTheorem_count` and friends, so four live
-- arms would have been excluded from every coverage count in this file — the
-- same "reports coverage it does not have" failure that retired
-- `crossCoreRemoteWriterPendingAudit` earlier in this PR.

/-- SM8.B.2: caching a per-core TLB view writes no scheduler slot. -/
@[simp] theorem setTlbOnCore_scheduler (st : SystemState) (c : CoreId)
    (t : TlbState) :
    (Architecture.setTlbOnCore st c t).scheduler = st.scheduler := rfl

@[simp] theorem setTlbOnCore_machine (st : SystemState) (c : CoreId)
    (t : TlbState) :
    (Architecture.setTlbOnCore st c t).machine = st.machine := rfl

/-- SM8.B.2: the initiator's own TLB drain is likewise scheduler-silent. -/
@[simp] theorem drainInitiatorPerCoreView_scheduler (st : SystemState) (c : CoreId)
    (ops : List Architecture.TlbInvalidation) :
    (Architecture.drainInitiatorPerCoreView st c ops).scheduler = st.scheduler := rfl

@[simp] theorem drainInitiatorPerCoreView_machine (st : SystemState) (c : CoreId)
    (ops : List Architecture.TlbInvalidation) :
    (Architecture.drainInitiatorPerCoreView st c ops).machine = st.machine := rfl

/-- SM8.B.2: the whole memory-subsystem surface is scheduler- and
register-silent.  One lemma per layer, each `rfl` or a one-step composition, so
the wrappers below reduce to `storeObject`'s frames at the leaf.

`SchedulerMachineFramed` bundles the pair because every layer needs both and
carrying them separately doubles the chain. -/
abbrev SchedulerMachineFramed (st st' : SystemState) : Prop :=
  st'.scheduler = st.scheduler ∧ st'.machine = st.machine

theorem observableSlotsConfinedToCores_nil_of_framed {st st' : SystemState}
    (h : SchedulerMachineFramed st st') :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_machine_eq h.1 h.2

/-- SM8.B.2: unmapping a page is one `storeObject` of the rewritten root. -/
theorem vspaceUnmapPage_framed (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (st st' : SystemState)
    (h : Architecture.vspaceUnmapPage asid vaddr st = .ok ((), st')) :
    SchedulerMachineFramed st st' := by
  unfold Architecture.vspaceUnmapPage at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · exact ⟨storeObject_scheduler_eq _ _ _ _ h, storeObject_machine_eq _ _ _ _ h⟩

/-- SM8.B.2: the TLB flush the unmap appends writes only `tlb`. -/
theorem vspaceUnmapPageWithFlush_framed (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (st st' : SystemState)
    (h : Architecture.vspaceUnmapPageWithFlush asid vaddr st = .ok ((), st')) :
    SchedulerMachineFramed st st' := by
  unfold Architecture.vspaceUnmapPageWithFlush at h
  split at h
  · exact absurd h (by simp)
  · next stMid hMid =>
    rw [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hs⟩ := h
    subst hs
    exact vspaceUnmapPage_framed asid vaddr st stMid hMid

/-- SM8.B.2: posting a shootdown round writes only `tlbShootdown`. -/
theorem withShootdownRound_framed (executingCore : CoreId)
    (op : Architecture.TlbInvalidation) (st st' : SystemState)
    (h : Architecture.withShootdownRound executingCore op st = .ok ((), st')) :
    SchedulerMachineFramed st st' := by
  rw [Architecture.withShootdownRound_total, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, hs⟩ := h
  subst hs
  exact ⟨rfl, rfl⟩

/-- SM8.B.2: unmap-with-round — page table, TLB, then the posted round. -/
theorem vspaceUnmapPageWithShootdown_framed (executingCore : CoreId)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (st st' : SystemState)
    (h : Architecture.vspaceUnmapPageWithShootdown executingCore asid vaddr st
      = .ok ((), st')) :
    SchedulerMachineFramed st st' := by
  unfold Architecture.vspaceUnmapPageWithShootdown at h
  split at h
  · exact absurd h (by simp)
  · next stFlush hFlush =>
    obtain ⟨hs1, hm1⟩ := vspaceUnmapPageWithFlush_framed asid vaddr st stFlush hFlush
    obtain ⟨hs2, hm2⟩ := withShootdownRound_framed executingCore _ stFlush st' h
    exact ⟨by rw [hs2, hs1], by rw [hm2, hm1]⟩

/-- SM8.B.2: the initiator-atomic unmap — page table, TLB, round, initiator
view — writes no scheduler slot and no register bank. -/
theorem vspaceUnmapPageWithShootdownPerCore_framed (executingCore : CoreId)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (st st' : SystemState)
    (h : Architecture.vspaceUnmapPageWithShootdownPerCore executingCore asid vaddr st
      = .ok ((), st')) :
    SchedulerMachineFramed st st' := by
  unfold Architecture.vspaceUnmapPageWithShootdownPerCore at h
  split at h
  · exact absurd h (by simp)
  · next stRound hRound =>
    rw [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hs⟩ := h
    subst hs
    obtain ⟨hs1, hm1⟩ :=
      vspaceUnmapPageWithShootdown_framed executingCore asid vaddr st stRound hRound
    exact ⟨by rw [drainInitiatorPerCoreView_scheduler, hs1],
           by rw [drainInitiatorPerCoreView_machine, hm1]⟩

/-- SM8.B.2: caching a walked translation is `perCoreTlb`-only. -/
@[simp] theorem tlbFillOnCore_scheduler (st : SystemState) (c : CoreId)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) :
    (Architecture.tlbFillOnCore st c asid vaddr).scheduler = st.scheduler := by
  unfold Architecture.tlbFillOnCore
  split <;> rfl

@[simp] theorem tlbFillOnCore_machine (st : SystemState) (c : CoreId)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) :
    (Architecture.tlbFillOnCore st c asid vaddr).machine = st.machine := by
  unfold Architecture.tlbFillOnCore
  split <;> rfl

/-- SM8.B.2: mapping a page is one `storeObject` of the rewritten root. -/
theorem vspaceMapPage_framed (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions) (st st' : SystemState)
    (h : Architecture.vspaceMapPage asid vaddr paddr perms st = .ok ((), st')) :
    SchedulerMachineFramed st st' := by
  unfold Architecture.vspaceMapPage at h
  repeat' split at h
  all_goals first
    | exact absurd h (by simp)
    | exact ⟨storeObject_scheduler_eq _ _ _ _ h, storeObject_machine_eq _ _ _ _ h⟩

/-- SM8.B.2: the checked map wrapper adds only guards and a `tlb` write. -/
theorem vspaceMapPageCheckedWithFlushFromState_framed (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr) (perms : PagePermissions)
    (st st' : SystemState)
    (h : Architecture.vspaceMapPageCheckedWithFlushFromState asid vaddr paddr perms st
      = .ok ((), st')) :
    SchedulerMachineFramed st st' := by
  unfold Architecture.vspaceMapPageCheckedWithFlushFromState
    Architecture.vspaceMapPageWithFlush at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · next stMap hMap =>
          rw [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨-, hs⟩ := h
          subst hs
          exact vspaceMapPage_framed asid vaddr paddr perms st stMap hMap

/-- SM8.B.2: a *remap* posts a round; a fresh map does not.  Either way the
scheduler and the register banks frame. -/
theorem vspaceMapPageCheckedWithShootdownFromState_framed (executingCore : CoreId)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (perms : PagePermissions) (st st' : SystemState)
    (h : Architecture.vspaceMapPageCheckedWithShootdownFromState executingCore asid vaddr
      paddr perms st = .ok ((), st')) :
    SchedulerMachineFramed st st' := by
  unfold Architecture.vspaceMapPageCheckedWithShootdownFromState at h
  simp only [] at h
  split at h
  · exact absurd h (by simp)
  · next stFlush hFlush =>
    obtain ⟨hs1, hm1⟩ :=
      vspaceMapPageCheckedWithFlushFromState_framed asid vaddr paddr perms st stFlush hFlush
    split at h
    · obtain ⟨hs2, hm2⟩ := withShootdownRound_framed executingCore _ stFlush st' h
      exact ⟨by rw [hs2, hs1], by rw [hm2, hm1]⟩
    · rw [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, hs⟩ := h
      subst hs
      exact ⟨hs1, hm1⟩

/-- SM8.B.2 (**the live `.vspaceMap` bound**): the initiator-atomic map writes
**no core** — page tables, the scalar TLB, an optional remap round, the
initiator's drain and the fresh fill are all outside the observer's read set. -/
theorem vspaceMapPageCheckedWithShootdownFromStatePerCore_confinedToCores
    (executingCore : CoreId) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions) (st st' : SystemState)
    (hStep : Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore executingCore
      asid vaddr paddr perms st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' [] := by
  refine observableSlotsConfinedToCores_nil_of_framed ?_
  unfold Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore at hStep
  split at hStep
  · exact absurd hStep (by simp)
  · next stRound hRound =>
    rw [Except.ok.injEq, Prod.mk.injEq] at hStep
    obtain ⟨-, hs⟩ := hStep
    subst hs
    obtain ⟨hs1, hm1⟩ := vspaceMapPageCheckedWithShootdownFromState_framed executingCore
      asid vaddr paddr perms st stRound hRound
    exact ⟨by rw [tlbFillOnCore_scheduler, drainInitiatorPerCoreView_scheduler, hs1],
           by rw [tlbFillOnCore_machine, drainInitiatorPerCoreView_machine, hm1]⟩

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

/-- SM8.B.2: the I-cache broadcast seam writes only `perCoreICache` and the
maintenance ledger, so it frames whatever its wrapped transition frames. -/
theorem withIcacheBroadcast_framed
    (mkOp : SystemState → Option Architecture.ICacheInvalidation) (k : Kernel Unit)
    (st st' : SystemState)
    (hk : ∀ s s', k s = .ok ((), s') → SchedulerMachineFramed s s')
    (h : Architecture.withIcacheBroadcast mkOp k st = .ok ((), st')) :
    SchedulerMachineFramed st st' := by
  unfold Architecture.withIcacheBroadcast at h
  simp only [] at h
  split at h
  · exact absurd h (by simp)
  · next stK hK =>
    obtain ⟨hs, hm⟩ := hk st stK hK
    split at h
    · rw [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, he⟩ := h
      subst he
      exact ⟨hs, hm⟩
    · rw [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, he⟩ := h
      subst he
      exact ⟨hs, hm⟩

/-- SM8.B.2 (**the live `.vspaceUnmap` bound**): the unmap seam writes **no
core**.  Page tables, the scalar TLB, the shootdown round, the initiator's own
per-core view and the I-cache ledger — none of them is a scheduler slot or a
register bank, on any core. -/
theorem vspaceUnmapPageWithShootdownAndIcacheBroadcast_confinedToCores
    (executingCore : CoreId) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (st st' : SystemState)
    (hStep : Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast executingCore
      asid vaddr st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_framed
    (withIcacheBroadcast_framed _ _ st st'
      (fun _ _ hk => vspaceUnmapPageWithShootdownPerCore_framed executingCore asid vaddr _ _ hk)
      hStep)

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

-- ============================================================================
-- §5c  The live `.lifecycleRetype` arm — a sweep bounded by occupancy
-- ============================================================================
--
-- The third and last routing-allowlist exception, and the only one of the three
-- that genuinely writes scheduler state: destroying a TCB sweeps it out of
-- **every** core's run queue and current slot, because a destroy has no home
-- core to key on.
--
-- The naive bound is therefore `allCores`, which is true and says nothing.  The
-- honest one is the set of cores the destroyed thread actually occupied in the
-- pre-state, and it is available only because review round 17 rewrote the
-- sweep's step to be *guarded* by `threadOccupiesCore`: an unoccupied core is
-- left literally untouched rather than rewritten with equal values.
--
-- Everything else the retype pipeline does — the donation return, the
-- `scThreadIndex` removal, the two IPC-reference sweeps, the service-registration
-- cleanup, the CDT detach, the memory scrub, the object store, the ASID
-- shootdown rounds, the initiator's own TLB drain and the I-cache broadcast —
-- writes no scheduler slot and no register bank, and each of those is discharged
-- by a frame rather than by an argument.

/-- SM8.B.2: the I-cache broadcast seam preserves whatever confinement its
wrapped transition has.

The `withIcacheBroadcast_framed` sibling, keyed on the write set rather than on
whole-machine equality — the retype needs this one because its memory scrub
genuinely writes `machine`, so the `Framed` form is unavailable. -/
theorem withIcacheBroadcast_confinedToCores
    (mkOp : SystemState → Option Architecture.ICacheInvalidation) (k : Kernel Unit)
    (cs : List CoreId) (st st' : SystemState)
    (hk : ∀ s', k st = .ok ((), s') → observableSlotsConfinedToCores st s' cs)
    (h : Architecture.withIcacheBroadcast mkOp k st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' cs := by
  unfold Architecture.withIcacheBroadcast at h
  simp only [] at h
  split at h
  · exact absurd h (by simp)
  · next stK hK =>
    have hInner := hk stK hK
    split at h <;>
      · rw [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, he⟩ := h
        subst he
        exact observableSlotsConfinedToCores_of_framed_suffix (stMid := stK) rfl rfl hInner

/-- SM8.B.2: **where a `.lifecycleRetype` writes**, as a function of the object
being destroyed.

Only the TCB arm names any core, and it names the ones the doomed thread
occupies.  Every other kind of object — CNode, endpoint, notification, reply,
VSpace root, untyped, scheduling context — is scheduler-silent, so its write set
is empty. -/
def lifecycleRetypeWriteSetOf (st : SystemState) (currentObj : KernelObject) :
    List CoreId :=
  match currentObj with
  | .tcb tcb => threadOccupiedCores st tcb.tid
  | _ => []

/-- SM8.B.2: the same set, resolved from the target's id through the pre-state
store.  Retyping an absent object writes nothing (the pipeline errors out).

Read through the AN10-B accessor `getObject?` rather than the store directly:
this is a live-path definition, and the retype's own pipeline is the last place
this subsystem should be reintroducing raw matches. -/
def lifecycleRetypeWriteSet (st : SystemState) (target : SeLe4n.ObjId) : List CoreId :=
  match st.getObject? target with
  | some obj => lifecycleRetypeWriteSetOf st obj
  | none => []

/-- SM8.B.2: the TCB cleanup arm, with its scheduler- and machine-silent prefix
abstracted.

Stated separately because the arm runs at one of two mid-states (the
`scThreadIndex` removal fires only for a `.bound` binding) and the two differ in
nothing the observer reads. -/
private theorem tcbCleanupArm_confinedToCores (st stMid : SystemState)
    (tid : SeLe4n.ThreadId)
    (hSched : stMid.scheduler = st.scheduler) (hMach : stMid.machine = st.machine) :
    observableSlotsConfinedToCores st (cleanupTcbReferences stMid tid)
      (threadOccupiedCores st tid) := by
  refine observableSlotsConfinedToCores_of_framed_prefix hSched hMach ?_
  rw [← threadOccupiedCores_congr (st' := stMid) tid hSched]
  exact cleanupTcbReferences_confinedToCores stMid tid

/-- SM8.B.2 (**the cleanup pipeline's bound**): the pre-retype cleanup writes no
core outside the destroyed object's write set.

The case split is the definition's own: the TCB arm carries the sweep, the CNode
and endpoint arms are frames, and the remaining kinds return the state
unchanged.  The TCB arm's three prefix steps — the donated-SC return, the
`scThreadIndex` removal, and (on the error path) the reply-link rejection — are
all scheduler- and machine-preserving, which is also why the write set may be
read at the pipeline's entry state rather than at the sweep's. -/
theorem lifecyclePreRetypeCleanup_confinedToCores
    (st stClean : SystemState) (target : SeLe4n.ObjId) (currentObj newObj : KernelObject)
    (hOk : lifecyclePreRetypeCleanup st target currentObj newObj = .ok stClean) :
    observableSlotsConfinedToCores st stClean (lifecycleRetypeWriteSetOf st currentObj) := by
  cases currentObj with
  | tcb tcb =>
    simp only [lifecyclePreRetypeCleanup] at hOk
    -- Round 39: the running-target rejection is vacuous on the `.ok` path.
    rw [if_neg (by
      intro hRun
      rw [if_pos hRun] at hOk
      exact absurd hOk (by simp))] at hOk
    cases hDon : cleanupDonatedSchedContext st tcb.tid with
    | error e => rw [hDon] at hOk; contradiction
    | ok stDon =>
      rw [hDon] at hOk
      have hDonSched : stDon.scheduler = st.scheduler :=
        cleanupDonatedSchedContext_scheduler_eq st stDon tcb.tid hDon
      have hDonMach : stDon.machine = st.machine :=
        cleanupDonatedSchedContext_machine_eq st stDon tcb.tid hDon
      simp only [] at hOk
      have hRO : tcb.replyObject.isSome = false := by
        cases hr : tcb.replyObject.isSome with
        | false => rfl
        | true => rw [if_pos hr] at hOk; exact absurd hOk (by simp)
      rw [if_neg (by simp [hRO])] at hOk
      injection hOk with hOk; subst hOk
      simp only [lifecycleRetypeWriteSetOf]
      -- the `scThreadIndex` removal fires only for a `.bound` binding, and is
      -- scheduler- and machine-silent when it does
      cases tcb.schedContextBinding with
      | bound scId =>
        exact tcbCleanupArm_confinedToCores st
          { stDon with
            scThreadIndex := scThreadIndexRemove stDon.scThreadIndex scId tcb.tid }
          tcb.tid hDonSched hDonMach
      | unbound => exact tcbCleanupArm_confinedToCores st stDon tcb.tid hDonSched hDonMach
      | donated _ _ => exact tcbCleanupArm_confinedToCores st stDon tcb.tid hDonSched hDonMach
  | cnode cn =>
    simp only [lifecyclePreRetypeCleanup, lifecycleRetypeWriteSetOf] at hOk ⊢
    have hDetach : observableSlotsConfinedToCores st (detachCNodeSlots st target cn) [] :=
      observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
        (detachCNodeSlots_scheduler_eq st target cn)
        (detachCNodeSlots_machine_eq st target cn)
    cases newObj <;>
      (simp only [] at hOk
       injection hOk with hOk
       subst hOk
       first
         | exact observableSlotsConfinedToCores_refl _ _
         | exact hDetach)
  | endpoint _ =>
    simp only [lifecyclePreRetypeCleanup, lifecycleRetypeWriteSetOf] at hOk ⊢
    injection hOk with hOk; subst hOk
    exact observableSlotsConfinedToCores_nil_of_scheduler_machine_eq
      (cleanupEndpointServiceRegistrations_scheduler_eq st target)
      (cleanupEndpointServiceRegistrations_machine_eq st target)
  | reply _ =>
    simp only [lifecyclePreRetypeCleanup, lifecycleRetypeWriteSetOf] at hOk ⊢
    split at hOk
    · cases hOk
    · injection hOk with hOk; subst hOk; exact observableSlotsConfinedToCores_refl _ _
  | notification _ | vspaceRoot _ | untyped _ | schedContext _ =>
    simp only [lifecyclePreRetypeCleanup, lifecycleRetypeWriteSetOf] at hOk ⊢
    injection hOk with hOk; subst hOk; exact observableSlotsConfinedToCores_refl _ _

/-- SM8.B.2: the object-store replacement is scheduler- and machine-silent. -/
private theorem lifecycleRetypeDirect_framed
    (authCap : Capability) (target : SeLe4n.ObjId) (newObj : KernelObject)
    (st st' : SystemState)
    (h : lifecycleRetypeDirect authCap target newObj st = .ok ((), st')) :
    st'.scheduler = st.scheduler ∧ st'.machine = st.machine := by
  unfold lifecycleRetypeDirect at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · split at h
      · exact ⟨storeObject_scheduler_eq st st' target newObj h,
              storeObject_machine_eq st st' target newObj h⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- SM8.B.2: the base retype-with-cleanup writes no core outside the write set.

Three of its four steps are frames — the well-formedness reject, the memory
scrub (`machine.memory`, and `machine.regs` is a field beside it) and the object
store — so the whole transition's bound is the cleanup's. -/
theorem lifecycleRetypeDirectWithCleanup_confinedToCores
    (authCap : Capability) (target : SeLe4n.ObjId) (newObj : KernelObject)
    (st st' : SystemState)
    (h : lifecycleRetypeDirectWithCleanup authCap target newObj st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' (lifecycleRetypeWriteSet st target) := by
  unfold lifecycleRetypeDirectWithCleanup at h
  simp only [lifecycleRetypeWriteSet, SystemState.getObject?_eq_getElem]
  split at h
  · exact absurd h (by simp)
  · next =>
    split at h
    · -- absent target: the direct store errors or replaces, either way scheduler-silent
      next hNone =>
        rw [hNone]
        obtain ⟨hs, hm⟩ := lifecycleRetypeDirect_framed authCap target newObj st st' h
        exact observableSlotsConfinedToCores_nil_of_scheduler_machine_eq hs hm
    · next currentObj hSome =>
      rw [hSome]
      split at h
      · exact absurd h (by simp)
      · next stClean hClean =>
        have hCleanConf :=
          lifecyclePreRetypeCleanup_confinedToCores st stClean target currentObj newObj hClean
        obtain ⟨hs, hm⟩ := lifecycleRetypeDirect_framed authCap target newObj _ st' h
        -- the scrub writes `machine.memory`, so the suffix frame here is the
        -- register-bank one rather than whole-machine equality
        refine observableSlotsConfinedToCores_of_framed_suffix_regs
          (hs.trans (scrubObjectMemory_scheduler_eq stClean target currentObj.objectType))
          (fun c => by
            rw [hm, scrubObjectMemory_regsOnCore]) hCleanConf

/-- SM8.B.2: the initiator's own per-core TLB drain is scheduler- and
machine-silent, on both arms. -/
@[simp] theorem retypeInitiatorDrain_scheduler
    (executingCore : CoreId) (asids : List SeLe4n.ASID) (st : SystemState) :
    (retypeInitiatorDrain executingCore asids st).scheduler = st.scheduler := by
  unfold retypeInitiatorDrain
  cases asids <;> simp

@[simp] theorem retypeInitiatorDrain_machine
    (executingCore : CoreId) (asids : List SeLe4n.ASID) (st : SystemState) :
    (retypeInitiatorDrain executingCore asids st).machine = st.machine := by
  unfold retypeInitiatorDrain
  cases asids <;> simp

/-- SM8.B.2: adding the ASID shootdown rounds does not widen the write set —
TLB maintenance is not scheduling. -/
theorem lifecycleRetypeDirectWithCleanupShootdown_confinedToCores
    (executingCore : CoreId) (authCap : Capability) (target : SeLe4n.ObjId)
    (newObj : KernelObject) (st st' : SystemState)
    (h : lifecycleRetypeDirectWithCleanupShootdown executingCore authCap target newObj st
      = .ok ((), st')) :
    observableSlotsConfinedToCores st st' (lifecycleRetypeWriteSet st target) := by
  unfold lifecycleRetypeDirectWithCleanupShootdown at h
  cases hBase : lifecycleRetypeDirectWithCleanup authCap target newObj st with
  | error e => rw [hBase] at h; exact absurd h (by simp)
  | ok pair =>
    obtain ⟨u, stBase⟩ := pair
    cases u
    rw [hBase] at h
    simp only [] at h
    rw [retypeShootdownAsids_eq] at h
    rw [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, he⟩ := h
    subst he
    exact observableSlotsConfinedToCores_of_framed_suffix
      (retypeAsidRoundFold_scheduler _ _ _) (retypeAsidRoundFold_machine _ _ _)
      (lifecycleRetypeDirectWithCleanup_confinedToCores authCap target newObj st stBase hBase)

/-- SM8.B.2: nor does the initiator's own per-core view drain. -/
theorem lifecycleRetypeDirectWithCleanupShootdownPerCore_confinedToCores
    (executingCore : CoreId) (authCap : Capability) (target : SeLe4n.ObjId)
    (newObj : KernelObject) (st st' : SystemState)
    (h : lifecycleRetypeDirectWithCleanupShootdownPerCore executingCore authCap target
      newObj st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' (lifecycleRetypeWriteSet st target) := by
  unfold lifecycleRetypeDirectWithCleanupShootdownPerCore at h
  cases hRound : lifecycleRetypeDirectWithCleanupShootdown executingCore authCap target
      newObj st with
  | error e => rw [hRound] at h; exact absurd h (by simp)
  | ok pair =>
    obtain ⟨u, stRound⟩ := pair
    cases u
    rw [hRound] at h
    simp only [] at h
    rw [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, he⟩ := h
    subst he
    exact observableSlotsConfinedToCores_of_framed_suffix
      (retypeInitiatorDrain_scheduler _ _ _) (retypeInitiatorDrain_machine _ _ _)
      (lifecycleRetypeDirectWithCleanupShootdown_confinedToCores executingCore authCap target
        newObj st stRound hRound)

/-- SM8.B.2 (**the live `.lifecycleRetype` bound**): a retype writes no core the
destroyed object did not occupy.

The third routing-allowlist exception discharged, and the sharp statement rather
than the trivially-true `allCores` one: destroying a thread that no core held
(suspended, or queued nowhere) is invisible on **every** core, and destroying a
running one is visible only where it ran.  Retyping anything that is not a TCB
has an empty write set outright. -/
theorem lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_confinedToCores
    (executingCore : CoreId) (authCap : Capability) (target : SeLe4n.ObjId)
    (newObj : KernelObject) (st st' : SystemState)
    (h : lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache executingCore authCap
      target newObj st = .ok ((), st')) :
    observableSlotsConfinedToCores st st' (lifecycleRetypeWriteSet st target) :=
  withIcacheBroadcast_confinedToCores _ _ _ st st'
    (fun _ hk => lifecycleRetypeDirectWithCleanupShootdownPerCore_confinedToCores
      executingCore authCap target newObj st _ hk) h

/-- SM8.B.3 (**the live `.lifecycleRetype` arm, cross-core**): a retype is
invisible on every core the destroyed object did not occupy.

Read the hypotheses: `hne` is membership in a set computed from the **pre-state**
(it has to be — the destroyed thread is gone from the post-state), and `hShared`
is the object-level premise.  There is no hypothesis about the label of the
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

/-- SM8.B.2: destroying an object that is not a TCB writes **no** core.

The load-bearing sharpness check on the other side from
`removeRunnableFromAllCores_confinedToCores`: the write set is not merely
*smaller* than `allCores`, it is empty for six of the seven object kinds. -/
theorem lifecycleRetypeWriteSet_nil_of_not_tcb (st : SystemState) (target : SeLe4n.ObjId)
    (h : ∀ tcb : TCB, st.objects[target]? ≠ some (.tcb tcb)) :
    lifecycleRetypeWriteSet st target = [] := by
  unfold lifecycleRetypeWriteSet SystemState.getObject?
  cases hObj : st.objects[target]? with
  | none => rfl
  | some obj =>
    cases obj with
    | tcb tcb => exact absurd hObj (h tcb)
    | _ => rfl

-- ============================================================================
-- §6  The non-interference instantiations
-- ============================================================================
--
-- Each of these is `crossCoreNonInterference_ofCores` applied at a transition
-- that genuinely writes a remote core, so `c'` here is a real other core rather
-- than `bootCoreId`.  Read the hypotheses: `hne` is membership in a write set
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

/-- SM8.B.2 (SM6.C, **the composed live `.replyRecv`**): both legs together are
invisible to any core outside the union of the reply target's home core and the
receive leg's set at the intermediate state. -/
theorem endpointReplyRecvOnCore_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (endpointId : SeLe4n.ObjId) (receiver replyTarget : SeLe4n.ThreadId)
    (msg : IpcMessage) (replyId : Option SeLe4n.ReplyId) (executingCore : CoreId)
    (st : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hne : c ∉ endpointReplyRecvWriteSet endpointId receiver replyTarget msg executingCore st)
    (hShared : sharedViewUnchanged ctx observer st
      (endpointReplyRecvOnCore endpointId receiver replyTarget msg replyId executingCore st).1) :
    projectStateOnCore ctx observer
        (endpointReplyRecvOnCore endpointId receiver replyTarget msg replyId executingCore st).1 c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer hne
    (endpointReplyRecvOnCore_confinedToCores endpointId receiver replyTarget msg replyId
      executingCore st hObjInv)
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

/-- SM8.B.2 (SM6.E): a cross-core deschedule is invisible to any core that is not
the victim's home core. -/
theorem descheduleThread_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (tid : SeLe4n.ThreadId) (executingCore : CoreId)
    (st : SystemState) (c : CoreId)
    (hne : c ≠ determineTargetCore st tid)
    (hShared : sharedViewUnchanged ctx observer st (descheduleThread st tid executingCore).1) :
    projectStateOnCore ctx observer (descheduleThread st tid executingCore).1 c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer (by simpa using hne)
    (descheduleThread_confinedToCores st tid executingCore) hShared

/-- SM8.B.2 (SM6.E, composed): a cross-core IPC-blocking cancellation is
invisible to any core that is not the victim's home core. -/
theorem cancelIpcBlockingOnCore_crossCoreNonInterference (ctx : LabelingContext)
    (observer : IfObserver) (victim : SeLe4n.ThreadId) (tcb : TCB)
    (executingCore : CoreId) (st : SystemState) (c : CoreId)
    (hne : c ≠ determineTargetCore st victim)
    (hShared : sharedViewUnchanged ctx observer st
      (cancelIpcBlockingOnCore victim tcb executingCore st).1) :
    projectStateOnCore ctx observer
        (cancelIpcBlockingOnCore victim tcb executingCore st).1 c
      = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_ofCores ctx observer (by simpa using hne)
    (cancelIpcBlockingOnCore_confinedToCores victim tcb executingCore st) hShared

/-- SM8.B.2 (**the headline, and the thing SM6 cannot say**): waking a thread on
a remote core is invisible to a third core *whatever that thread's label*.

`wakeThread_preserves_projectionOnCore` (SM6.A) proves a wake invisible on
**every** core, but only under `hHighThread` — the woken thread must be outside
the observer's view, so the run-queue insert is dropped by the filter.  Here the
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
-- §7  Coverage
-- ============================================================================

/-- SM8.C.9 (**the live `.declassify` bound**): the declassification writes
**no core**.

Its entire state effect is one entry appended to
`SystemState.declassificationAuditLog` — not a scheduler slot, not a register
bank, not any per-core field.  The sharpest bound the inventory can express, and
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
        (ctx.threadDomainOf tid) (ctx.objectDomainOf targetId) targetId st st' hStep
      subst hSt'
      exact ⟨rfl, rfl⟩

/-- SM8.C.9 (**the live `.declassify` arm, cross-core**): a declassification is
invisible on every core.

The audit trail is deliberately outside `ObservableState`
(`declassificationAuditLog_write_preserves_projection`), so this is not merely
"writes no scheduler slot" — it is that the one field it does write is one no
observer reads.  See the field's docstring for why projecting it would open a
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

/-- SM8.B.2: the cross-core transitions this module instantiates
`crossCoreNonInterference` at, one per SM6 sub-phase that has one.

Recorded as data so the count is checkable and so a reader can see at a glance
what is *not* here.  The exhaustive-match tripwire lives on `KernelOperation`
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
  /-- SM6 — the **live** `.send` arm: the WithCaps cross-core send.  Added in
  PR #861 review round 10, which found the arm still routed to the boot-pinned
  `endpointSendDualWithCaps`. -/
  | endpointSendDispatch
  /-- SM8.B — the **live** `.schedContextUnbind` arm: clear-and-requeue on the
  bound thread's home core.  Added in PR #861 review round 14, after this cut's
  own home-core routing made it a remote writer. -/
  | schedContextUnbindDispatch
  /-- SM8.B — the **live** `.schedContextBind` arm: re-bucket on the bound
  thread's home core.  Its write set reads the thread from the *argument*, not
  from the SC — bind rejects an already-bound SC. -/
  | schedContextBindDispatch
  /-- SM8.B — the **live** `.tcbSetAffinity` arm: migrate a thread between two
  home cores.  The only entry whose write set names *two* remote cores, and the
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
  /-- SM6.C — the receive leg of `replyRecv`. -/
  | endpointReceiveDual
  /-- SM6.C — both `replyRecv` legs, below the donation. -/
  | endpointReplyRecv
  /-- SM6.C — the **live** `.replyRecv` arm: both legs *and* the donation. -/
  | replyRecvBodyDispatch
  /-- SM6.E — the deschedule primitive. -/
  | deschedule
  /-- SM6.E — the *composed* IPC-blocking cancellation (teardown + deschedule). -/
  | cancelIpcBlocking
  /-- SM6.E — the **live** `.tcbSuspend` arm: the whole suspend pipeline. -/
  | suspendThreadDispatch
  /-- SM5.F.6 — the **live** `.tcbResume` arm: ready-restore, home-core enqueue,
  and the reschedule.  Added in PR #861 review round 10, which found the arm
  still routed to the boot-pinned `resumeThread`. -/
  | resumeThreadDispatch
  | setPriorityDispatch
  | setMCPriorityDispatch
  /-- SM8.B — the **live** `.vspaceMap` arm.  The first of the three entries
  added in PR #861 review round 35 to empty the per-core routing allowlist: it
  takes an executing core, so the gate demands an entry, and its write set is
  **empty** — page tables, the scalar TLB, the shootdown round, the initiator's
  own per-core view and the I-cache ledger are none of them a scheduler slot or
  a register bank on any core.  Until this entry existed the inventory had no way
  to *say* "writes no core", which is the only reason the arm held a waiver. -/
  | vspaceMapDispatch
  /-- SM8.B — the **live** `.vspaceUnmap` arm.  Empty write set, same reasons. -/
  | vspaceUnmapDispatch
  /-- SM8.B — the **live** `.lifecycleRetype` arm, and the one of the final three
  that genuinely writes scheduler state: destroying a TCB sweeps it out of every
  core's run queue and current slot, because a destroy has no home core to key
  on.  Its write set is therefore the set of cores the destroyed thread
  *occupied* — sharp rather than the trivially-true `allCores`, and available
  only because review round 17 made the sweep's step guarded. -/
  | lifecycleRetypeDispatch
  /-- SM8.C.9 — the **live** `.declassify` arm.  Takes an executing core (to
  resolve the running subject whose domain the downgrade is attributed to) and
  writes **no** core: its whole state effect is one entry appended to the
  declassification audit trail, which is not a per-core field at all. -/
  | declassifyDispatch
  deriving DecidableEq, Repr

def CrossCoreTransition.all : List CrossCoreTransition :=
  [.wake, .endpointCall, .endpointCallDispatch, .endpointSendDispatch,
   .schedContextUnbindDispatch, .schedContextBindDispatch, .schedContextConfigureDispatch,
   .setThreadCpuAffinityDispatch,
   .notificationSignal, .notificationSignalBound,
   .notificationWait, .endpointReply, .endpointReplyDispatch, .endpointReceiveDual,
   .endpointReplyRecv, .replyRecvBodyDispatch, .deschedule, .cancelIpcBlocking,
   .suspendThreadDispatch, .resumeThreadDispatch,
   .setPriorityDispatch, .setMCPriorityDispatch,
   .vspaceMapDispatch, .vspaceUnmapDispatch, .lifecycleRetypeDispatch,
   .declassifyDispatch]

/-- SM8.B.2: **`all` really is all of them.**

Every count, the injectivity check and both evidence tallies quantify over this
hand-written list rather than over the type, so a constructor omitted from it
would leave a transition out of the audited surface with all of them still
green.  The match-based tables are exhaustive by construction; this list is not,
and needs its own theorem.

Caught by PR #861 review round 11 — the identical fix had just been applied to
`CovertChannelId.all` two files away, and the sibling was missed in the same
commit.  Enumerations that gates quantify over need this uniformly, not
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
  | .endpointReplyRecv => niName! endpointReplyRecvOnCore_crossCoreNonInterference
  | .replyRecvBodyDispatch => niName! replyRecvBody_crossCoreNonInterference
  | .deschedule => niName! descheduleThread_crossCoreNonInterference
  | .cancelIpcBlocking => niName! cancelIpcBlockingOnCore_crossCoreNonInterference
  | .suspendThreadDispatch => niName! suspendThreadOnCore_crossCoreNonInterference
  | .resumeThreadDispatch => niName! resumeThreadOnCoreLive_crossCoreNonInterference
  | .setPriorityDispatch => niName! setPriorityOnCore_crossCoreNonInterference
  | .setMCPriorityDispatch => niName! setMCPriorityOnCore_crossCoreNonInterference
  | .vspaceMapDispatch =>
      niName! vspaceMapPageCheckedWithShootdownFromStatePerCore_crossCoreNonInterference
  | .vspaceUnmapDispatch =>
      niName! vspaceUnmapPageWithShootdownAndIcacheBroadcast_crossCoreNonInterference
  | .lifecycleRetypeDispatch =>
      niName! lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_crossCoreNonInterference
  | .declassifyDispatch =>
      niName! declassifyObjectFromCore_crossCoreNonInterference

theorem crossCoreNiTheorem_count : CrossCoreTransition.all.length = 26 := by rfl

/-- SM8.B.2: **which entries are the arms the live syscall dispatch actually
reaches**, as opposed to the below-API transitions they are built from.

This distinction is the point of the three entries added in the fourth review
round: `.signal` on the bound-delivery path, `.receive` rendezvousing with a
blocked sender, and `.replyRecv` combining its legs are all live behaviour, and
an inventory that passed its count and injectivity checks without them was
reporting coverage it did not have.

**A live entry must name the function the dispatch calls, not one it is built
from** (PR #861 review round 5).  Three entries failed that test and now have
wrapper entries of their own: `.reply` routes to `endpointReplyCrossCoreDispatch`
(which adds the donation return and the PIP reversion), `.replyRecv` to
`replyRecvBody` (which adds `replyRecvReturnDonation`), and `.tcbSuspend` to
`suspendThreadOnCore` (which adds the chain reversion, the running-core dequeue
and a scheduling point).  Each does strictly more per-core writing than the
below-API transition it wraps, so the narrower theorem never bounded it.

Three entries are a different case and are *not* re-pointed, because their live
arm calls the `…OnCore` transition **directly**:
`notificationSignalBoundCrossCoreDispatch` and `notificationWaitCrossCoreDispatch`
are definitionally `…OnCore … (determineExecutingCore st …) st`, and
`API.dispatchWithCapChecked`'s `.receive` arm applies its `endpoint→receiver`
flow gate and then invokes `endpointReceiveDualOnCore` itself.  For those the
`…OnCore` theorem is a statement about the live arm already.

**Being a leg does not stop something being a live arm** (PR #861 review round
8).  `endpointReceiveDualOnCore` is the receive leg of `replyRecvBody` *and* the
function the live `.receive` syscall reaches; an earlier cut marked it `false` on
the strength of the first fact alone, which contradicted
`crossCoreEnforcementEntries` — that table has listed it among the live
cross-core operations since round 4 — and under-reported the live-arm count. -/
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
  | .endpointReceiveDual => true
  | .endpointReplyRecv => false
  | .replyRecvBodyDispatch => true
  | .deschedule => false
  | .cancelIpcBlocking => false
  | .suspendThreadDispatch => true
  | .resumeThreadDispatch => true
  | .setPriorityDispatch => true
  | .setMCPriorityDispatch => true
  | .vspaceMapDispatch => true
  | .vspaceUnmapDispatch => true
  | .declassifyDispatch => true
  | .lifecycleRetypeDispatch => true

theorem crossCoreTransitionIsLiveArm_count :
    (CrossCoreTransition.all.filter crossCoreTransitionIsLiveArm).length = 19 := by decide

-- The check is quadratic in the inventory and linear in each theorem name, and
-- round 35's three entries (one of them 76 characters) pushed it past the
-- default budget: 25 constructors is 600 disequalities to decide where 22 was
-- 463.  Raising the budget rather than weakening the check — the statement is
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
function is the arm the live dispatch reaches, wrongly.  Round 4 found three
arms missing; round 5 found `.reply` / `.replyRecv` / `.tcbSuspend` naming the
below-API transition instead of the wrapper that does strictly more; round 8
found `.receive` classified a leg when the checked arm calls it directly.

The root cause is visible in `API.lean`: eight dispatch arms carry a
`dispatchWithCap_…_delegates` theorem, and **none of those eight ever drifted**.
The tie is not documentation — it is a theorem saying `dispatch S = f …`, so a
wrong entry fails to compile.  The cross-core arms had no such theorem, and all
three drifts happened there.

**The first cut of this type recorded a theorem *name*, and round 11 correctly
rejected it**: `niName!` checks that a declaration by that name exists, not that
it proves anything about *this* transition, so `.receive` could have cited the
`tcbSuspend` theorem and counted as backed.  That was the same defect one level
up — a claim held by a string rather than by a type.

So the evidence now carries a **proof of `syscallDelegates sid`**, a proposition
computed from the syscall in `API.lean`.  `syscallDelegates .receive` and
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
  | .endpointReceiveDual => some .receive
  | .endpointReplyRecv => none
  | .replyRecvBodyDispatch => some .replyRecv
  | .deschedule => none
  | .cancelIpcBlocking => none
  | .suspendThreadDispatch => some .tcbSuspend
  | .resumeThreadDispatch => some .tcbResume
  | .setPriorityDispatch => some .tcbSetPriority
  | .setMCPriorityDispatch => some .tcbSetMCPriority
  | .vspaceMapDispatch => some .vspaceMap
  | .vspaceUnmapDispatch => some .vspaceUnmap
  | .declassifyDispatch => some .declassify
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
  | .endpointReceiveDual => .delegationProof .receive syscallDelegates_receive
  | .endpointReplyRecv => .readOffTheArm "both legs below the donation; live arm is .replyRecvBodyDispatch"
  | .replyRecvBodyDispatch =>
      .readOffTheArm "checked `.replyRecv` arm calls replyRecvBody; delegation theorem pending"
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
  | .declassifyDispatch => .delegationProof .declassify syscallDelegates_declassify
  | .lifecycleRetypeDispatch =>
      .delegationProof .lifecycleRetype syscallDelegates_lifecycleRetype

/-- SM8.B.2 (**the tie is checked, not assumed**): a delegation-backed entry
names the syscall its own transition belongs to.  Round 11's example — the
`.receive` entry citing the `tcbSuspend` theorem — is now excluded twice over:
by the indexed proposition, and by this. -/
theorem crossCoreLiveArmEvidence_syscall_matches (t : CrossCoreTransition) :
    (crossCoreLiveArmEvidence t).syscall?.isSome = true →
      (crossCoreLiveArmEvidence t).syscall? = crossCoreLiveArmSyscall t := by
  cases t <;> simp [crossCoreLiveArmEvidence, crossCoreLiveArmSyscall,
    LiveArmEvidence.syscall?]

/-- SM8.B.2: **how many live arms are mechanically tied to the dispatch.**

Ten of eighteen today — `crossCoreLiveArmDelegationBacked_count` and
`crossCoreTransitionIsLiveArm_count` immediately below are the two halves, so
the ratio is read off machine-checked facts rather than restated here.

The parenthetical this paragraph used to carry warned that "prose that repeats a
`decide` is prose that goes stale the next time the `decide` changes", and then
went stale: it said "seven of fourteen" while `crossCoreTransitionIsLiveArm_count`
already read 15, having moved when round 27 rerouted an arm.  Round 35's three
entries — `.vspaceMap`, `.vspaceUnmap` and `.lifecycleRetype`, the three that
emptied the per-core routing allowlist — moved both halves again, and all three
arrive delegation-backed, so the ratio improved rather than merely grew.  The
number above is therefore worth exactly what the two theorem names beside it are
worth; if it disagrees with them, believe them.

Stated so the gap is a tracked quantity closable only by adding delegation
theorems — not something a reader reconstructs by grepping. -/
def crossCoreLiveArmDelegationBacked : List CrossCoreTransition :=
  CrossCoreTransition.all.filter (fun t =>
    crossCoreTransitionIsLiveArm t && (crossCoreLiveArmEvidence t).isDelegationBacked)

theorem crossCoreLiveArmDelegationBacked_count :
    crossCoreLiveArmDelegationBacked.length = 11 := by decide

/-- SM8.B.2: and the residual — the live arms still resting on a human reading
of `API.lean`, which is the state every one of the three drifts occurred in. -/
theorem crossCoreLiveArm_readOffTheArm_count :
    (CrossCoreTransition.all.filter (fun t =>
      crossCoreTransitionIsLiveArm t
        && !(crossCoreLiveArmEvidence t).isDelegationBacked)).length = 8 := by decide

/-- SM8.B.2: **which transitions can write a core other than the executing
one.**  Named for remote *writes*, not for wakes: a reply, a deschedule and a
cancellation all name a remote core without waking anything, and the earlier
`…WakesRemote` spelling described the wrong semantics (PR #861 review).  A
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
  | .endpointReplyRecv => true
  | .replyRecvBodyDispatch => true
  | .deschedule => true
  | .cancelIpcBlocking => true
  | .suspendThreadDispatch => true
  | .resumeThreadDispatch => true
  | .setPriorityDispatch => true
  | .setMCPriorityDispatch => true
  -- the two VSpace arms take an executing core and write **no** core with it
  | .vspaceMapDispatch => false
  | .vspaceUnmapDispatch => false
  | .lifecycleRetypeDispatch => true
  -- SM8.C.9: and the declassification, for a different reason — the only field
  -- it writes is not per-core at all
  | .declassifyDispatch => false

theorem crossCoreTransitionWritesRemote_count :
    (CrossCoreTransition.all.filter crossCoreTransitionWritesRemote).length = 22 := by decide

end SeLe4n.Kernel
