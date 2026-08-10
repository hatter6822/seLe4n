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
import SeLe4n.Kernel.IPC.CrossCore.EndpointReply
import SeLe4n.Kernel.IPC.CrossCore.Cancellation

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
* §5 — the SM6.E cancellation *primitive*.  The composed
  `cancelIpcBlockingOnCore` is **not** covered; see the scope note there, which
  says why and what one lemma would close it.
* §6 — the non-interference instantiations.
* §7 — coverage, as checkable data.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)
open SeLe4n.Kernel.Lifecycle.Suspend

-- ============================================================================
-- §1  The per-core scheduler primitives
-- ============================================================================

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
-- §5  SM6.E — the cancellation transition
-- ============================================================================

/-- SM8.B.2 (**SM6.E, cross-core**): the cancellation mechanism is
`descheduleThread`, whose confinement §1 proves — it writes only the victim's
**home** core, not the core running the cancellation.  This restates that at the
SM6.E name so the coverage list below reads off one theorem per sub-phase: a
`tcbSuspend` issued on core 0 against a victim homed on core 2 is invisible to
observers on cores 1 and 3 outright.

**Scope note (honest, and deliberately not papered over).**  The *composed*
`cancelIpcBlockingOnCore` — the object-level teardown followed by this
deschedule — is **not** covered here.  The teardown is per-core silent in fact,
but the codebase carries only its `scheduler` frame
(`cancelIpcBlocking_scheduler_eq`); the matching machine/register frame does not
exist, and its components (`clearTcbIpcFields` is `private`, the queue sweeps are
folds) put deriving one outside this cut.  Registered as scoped follow-on work
in the plan rather than claimed: adding
`cancelIpcBlocking_machine_eq` beside the existing scheduler frame in
`Lifecycle/Suspend.lean` closes it in one lemma. -/
theorem cancellationCrossCore_confinedToCores (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) :
    observableSlotsConfinedToCores st (descheduleThread st tid executingCore).1
      [determineTargetCore st tid] :=
  descheduleThread_confinedToCores st tid executingCore

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

/-- SM8.B.2: the cross-core transitions this module instantiates
`crossCoreNonInterference` at, one per SM6 sub-phase that has one.

Recorded as data so the count is checkable and so a reader can see at a glance
what is *not* here.  The exhaustive-match tripwire lives on `KernelOperation`
(`NonInterferencePerCore` §5); this list is the cross-core companion, and its
entries name theorems in this file. -/
inductive CrossCoreTransition where
  /-- SM5.C — the wake primitive, target = the woken thread's home core. -/
  | wake
  /-- SM6.A — the endpoint call; the only **two-core** write set. -/
  | endpointCall
  /-- SM6.B — the notification signal. -/
  | notificationSignal
  /-- SM6.B — the notification wait. -/
  | notificationWait
  /-- SM6.C — the reply. -/
  | endpointReply
  /-- SM6.E — the deschedule primitive. -/
  | deschedule
  deriving DecidableEq, Repr

def CrossCoreTransition.all : List CrossCoreTransition :=
  [.wake, .endpointCall, .notificationSignal, .notificationWait, .endpointReply, .deschedule]

/-- SM8.B.2: the name of each covered transition's non-interference theorem,
compile-time-validated through `niName!` — a renamed or deleted theorem breaks
this table rather than leaving it naming something that no longer exists. -/
def crossCoreNiTheorem : CrossCoreTransition → String
  | .wake => niName! wakeThread_crossCoreNonInterference_of_visible_thread
  | .endpointCall => niName! endpointCallOnCore_crossCoreNonInterference
  | .notificationSignal => niName! notificationSignalOnCore_crossCoreNonInterference
  | .notificationWait => niName! notificationWaitOnCore_crossCoreNonInterference
  | .endpointReply => niName! endpointReplyOnCore_crossCoreNonInterference
  | .deschedule => niName! descheduleThread_crossCoreNonInterference

theorem crossCoreNiTheorem_count : CrossCoreTransition.all.length = 6 := by rfl

theorem crossCoreNiTheorem_injective :
    ∀ t₁ t₂ : CrossCoreTransition, crossCoreNiTheorem t₁ = crossCoreNiTheorem t₂ → t₁ = t₂ := by
  intro t₁ t₂ h
  cases t₁ <;> cases t₂ <;>
    first
      | rfl
      | (exact absurd h (by simp only [crossCoreNiTheorem]; decide))

/-- SM8.B.2: **exactly two** of the six write sets can name a core other than the
executing one — the wake-bearing transitions.  A reader checking "does this
module actually exercise the cross-core direction" can check this instead of
reading six proofs. -/
def crossCoreTransitionWakesRemote : CrossCoreTransition → Bool
  | .wake => true
  | .endpointCall => true
  | .notificationSignal => true
  | .notificationWait => false
  | .endpointReply => true
  | .deschedule => true

theorem crossCoreTransitionWakesRemote_count :
    (CrossCoreTransition.all.filter crossCoreTransitionWakesRemote).length = 5 := by decide

end SeLe4n.Kernel
