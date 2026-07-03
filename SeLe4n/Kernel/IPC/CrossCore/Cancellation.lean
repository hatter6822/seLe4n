-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.NotificationSignal
import SeLe4n.Kernel.Lifecycle.Invariant.SuspendPreservation

/-!
# WS-SM SM6.E — Cancellation across cores

This module is the SM6.E deliverable of the WS-SM Phase 6 cross-core IPC
workstream (plan `docs/planning/SMP_CROSS_CORE_IPC_PLAN.md` §3.1, §5).  It
lifts the two cancellation sub-operations of the suspend pipeline
(`Lifecycle.Suspend`) to *cross-core* transitions under the SM3.B per-object
lock-set discipline:

* **`descheduleThread`** — the SM5.C `wakeThread` dual: removes a thread from
  its *home* core's run queue / current slot (`determineTargetCore`, its
  `cpuAffinity`), surfacing a `.reschedule` SGI when the thread was *actively
  current on a remote core* — the poke that stops that core from continuing to
  execute a cancelled/suspended thread.  A merely-queued remote victim needs no
  poke (the dequeue suffices); a victim current on the *executing* core is
  rescheduled synchronously by the caller (the suspend pipeline's G7), so no
  self-SGI is surfaced — exactly mirroring `wakeThread`'s SGI discipline
  (including the ghost-guard: a `tid` that does not resolve to a TCB pokes
  nothing).
* **`cancelIpcBlockingOnCore`** — the cross-core cancellation composite
  (plan SM6.E.5): the single-core `cancelIpcBlocking` object-level teardown
  (endpoint/notification dequeue, reply-link consume, TCB IPC-field clear)
  followed by the home-core deschedule + remote poke.  This is the G2+G4+G7
  slice of `suspendThread` generalised across cores: on a single core G4's
  `removeRunnable` is bootCore-pinned and G7 reschedules locally; across cores
  the deschedule must target the victim's *home* core and an actively-running
  remote victim must be interrupted.  The home core and active status are
  **pre-resolved from the pre-state** (mirroring the SM3.B lock-set
  pre-resolution discipline); `cancelIpcBlocking_scheduler_eq` proves the
  object-level teardown never touches the scheduler, so the pre-state reads
  coincide with post-teardown reads (`cancelIpcBlockingOnCore_eq_descheduleThread`
  makes the coincidence explicit).
* **`cancelBoundDonationOnCore` / `cancelDonationOnCore`** — the per-core
  generalisation of the R5.A donation-cancellation arms (plan SM6.E.3): the
  bound-arm's replenish-queue purge is parametrised by the core whose queue
  holds the SchedContext's replenishments (SM5.H
  `replenishQueueAffinityConsistentOnCore`: the bound thread's home core)
  instead of the single-core form's hardcoded `bootCoreId`;
  `cancelBoundDonationOnCore … bootCoreId = cancelBoundDonation` definitionally
  (the SM5.A backward-compatibility bridge pattern).  The donated arm
  (`cancelDonatedDonation` → `returnDonatedSchedContext`) performs object
  writes only, so it is core-independent and shared as-is.

## Lock-set footprints (plan §3.1)

The cancellation rows of the plan's lock-set table:

* `lockSet_cancelIpcBlocking` — victim TCB (W); blocked-on endpoint (W) or
  notification (W), pre-resolved from the victim's `ipcState`; and (SM6.D
  reply-object fold) the consumed Reply object (W) when the victim is
  `.blockedOnReply` with a live `replyObject` link.
* `lockSet_cancelDonation` — donor (victim) TCB (W); bound/donated
  SchedContext (W); donated-arm original-owner TCB (W) (the plan row's
  "receiver TCB").

Both are member-by-member covered by the enclosing `lockSet_tcbSuspend`
footprint (the `lockSet_tcbSuspend_*_write_mem` family below) — the formal
content of "the cancellation sub-operations run inside the suspend syscall's
2PL bracket" (plan SM6.E.1/SM6.E.3).

**Footprint rationale for the store sweeps**: `cancelIpcBlocking`'s
endpoint/notification removal helpers (`removeFromAllEndpointQueues` /
`removeFromAllNotificationWaitLists`) defensively sweep every
endpoint/notification object, but under the IPC invariant bundle's queue
membership discipline (`ipcStateQueueMembershipConsistent`,
`notificationWaitListsConsistent`) a blocked victim is a member of exactly the
one queue named by its `ipcState`, so every other object's rewrite is an
identical-value Robin-Hood re-insert — lookup-invisible (the same
identical-value-re-insert argument as SM6.A's `EndpointCallInvariant` §5) —
and the *semantic* write footprint is the declared single endpoint /
notification write lock.  The intrusive-queue link patches
(`spliceOutMidQueueNode`) rewrite the victim's queue *neighbours*' link
fields; queue-link fields of queued TCBs are guarded by the queue-owning
endpoint's write lock (the established `endpointQueueRemoveDual` discipline,
cf. SM6.B's bound-delivery footprint), so they ride the declared endpoint
lock.  This is the same rationale under which the enclosing
`lockSet_tcbSuspend` footprint (SM3.B.3, audit-pass-3) already declared its
optional single-endpoint/notification locks for the same sweeps.

The runtime wiring — routing the live `.tcbSuspend` dispatch through
`cancelIpcBlockingOnCore` under a `withLockSet` bracket over the
state-resolved footprints, with the surfaced SGI fired after the state commit
(the SM6.A `syscallDispatchCrossCoreEntry` pattern) — is the phase's tracked
follow-on, exactly as SM6.A landed its theorems one cut before the live
dispatch flip.  This module proves the SM6.E theorems that wiring consumes.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency
open SeLe4n.Kernel.Lifecycle.Suspend

-- ============================================================================
-- §1  The per-core deschedule primitive — `descheduleThread` (wakeThread dual)
-- ============================================================================

/-- WS-SM SM6.E (plan §3.1): deschedule a thread from its home core, across
cores.

Determines `tid`'s home core (`determineTargetCore`, its `cpuAffinity`),
removes it from that core's run queue and current slot
(`removeRunnableOnCore`), and decides whether a cross-core `.reschedule` SGI
is required: only when `tid` was *actively current* on a home core that
differs from the `executingCore` must that core be poked to stop executing
it and re-run its scheduler.  A merely-queued victim needs no poke (the
dequeue suffices — the remote core simply never dispatches it again), and a
victim current on the executing core is handled synchronously by the caller
(no self-SGI), mirroring `wakeThread`'s SGI discipline.  The ghost-guard
(`getTcb? = none` ⇒ no SGI) keeps the poke consistent with the state effect,
exactly as SM5.C's wake guard does.

Pure function of `(st, tid, executingCore)`; deterministic; total. -/
def descheduleThread (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) : SystemState × Option (CoreId × SgiKind) :=
  let target := determineTargetCore st tid
  let st' := removeRunnableOnCore st tid target
  let sgi : Option (CoreId × SgiKind) :=
    match st.getTcb? tid with
    | none => none
    | some _ =>
        if st.scheduler.currentOnCore target = some tid ∧ target ≠ executingCore
        then some (target, SgiKind.reschedule)
        else none
  (st', sgi)

/-- WS-SM SM6.E: the post-state of `descheduleThread` is exactly the home-core
removal — the SGI decision never alters the state. -/
theorem descheduleThread_state_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) :
    (descheduleThread st tid executingCore).1
      = removeRunnableOnCore st tid (determineTargetCore st tid) := rfl

/-- WS-SM SM6.E: `descheduleThread` never touches `objects`. -/
theorem descheduleThread_objects_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) :
    (descheduleThread st tid executingCore).1.objects = st.objects := rfl

/-- WS-SM SM6.E: a victim **actively current on a remote home core** surfaces a
`.reschedule` SGI targeting that core — the poke that stops the remote core
from continuing to execute it. -/
theorem descheduleThread_emits_sgi_if_remote_current
    (st : SystemState) (tid : SeLe4n.ThreadId) (executingCore : CoreId)
    (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb)
    (hCur : st.scheduler.currentOnCore (determineTargetCore st tid) = some tid)
    (hRemote : determineTargetCore st tid ≠ executingCore) :
    (descheduleThread st tid executingCore).2
      = some (determineTargetCore st tid, SgiKind.reschedule) := by
  unfold descheduleThread
  simp only [hTcb]
  rw [if_pos ⟨hCur, hRemote⟩]

/-- WS-SM SM6.E: a victim whose home core **is** the executing core surfaces no
SGI — the caller reschedules synchronously. -/
theorem descheduleThread_no_sgi_if_local
    (st : SystemState) (tid : SeLe4n.ThreadId) (executingCore : CoreId)
    (hLocal : determineTargetCore st tid = executingCore) :
    (descheduleThread st tid executingCore).2 = none := by
  unfold descheduleThread
  cases hT : st.getTcb? tid with
  | none => rfl
  | some _ =>
      simp only []
      rw [if_neg (fun h => h.2 hLocal)]

/-- WS-SM SM6.E: a victim that is **not current** on its home core (merely
queued, or blocked and in no queue at all) surfaces no SGI — removing it from
the run queue suffices, no other core is executing it. -/
theorem descheduleThread_no_sgi_if_not_current
    (st : SystemState) (tid : SeLe4n.ThreadId) (executingCore : CoreId)
    (hNotCur : st.scheduler.currentOnCore (determineTargetCore st tid) ≠ some tid) :
    (descheduleThread st tid executingCore).2 = none := by
  unfold descheduleThread
  cases hT : st.getTcb? tid with
  | none => rfl
  | some _ =>
      simp only []
      rw [if_neg (fun h => hNotCur h.1)]

/-- WS-SM SM6.E (ghost-guard): a `tid` that does not resolve to a TCB pokes
nothing — the SGI stays consistent with the (no-op) state effect. -/
theorem descheduleThread_no_sgi_if_ghost
    (st : SystemState) (tid : SeLe4n.ThreadId) (executingCore : CoreId)
    (hGhost : st.getTcb? tid = none) :
    (descheduleThread st tid executingCore).2 = none := by
  unfold descheduleThread
  simp only [hGhost]

/-- WS-SM SM6.E: after `descheduleThread`, the thread is fully descheduled on
its home core — not in the run queue and not the current thread. -/
theorem descheduleThread_descheduled_on_home
    (st : SystemState) (tid : SeLe4n.ThreadId) (executingCore : CoreId) :
    tid ∉ (descheduleThread st tid executingCore).1.scheduler.runQueueOnCore
        (determineTargetCore st tid)
    ∧ (descheduleThread st tid executingCore).1.scheduler.currentOnCore
        (determineTargetCore st tid) ≠ some tid := by
  rw [descheduleThread_state_eq]
  exact ⟨removeRunnableOnCore_not_mem_self st tid (determineTargetCore st tid),
         removeRunnableOnCore_currentOnCore_ne_self st tid (determineTargetCore st tid)⟩

/-- WS-SM SM6.E: `descheduleThread` is confined to the home core — every other
core's run queue and current slot are exactly the pre-state's (the per-core
locality dual of `wakeThread_independent_of_other_core`). -/
theorem descheduleThread_independent_of_other_core
    (st : SystemState) (tid : SeLe4n.ThreadId) (executingCore : CoreId)
    (c' : CoreId) (hOther : determineTargetCore st tid ≠ c') :
    (descheduleThread st tid executingCore).1.scheduler.runQueueOnCore c'
        = st.scheduler.runQueueOnCore c'
    ∧ (descheduleThread st tid executingCore).1.scheduler.currentOnCore c'
        = st.scheduler.currentOnCore c' := by
  rw [descheduleThread_state_eq]
  exact ⟨removeRunnableOnCore_runQueueOnCore_ne st tid _ c' hOther,
         removeRunnableOnCore_currentOnCore_ne st tid _ c' hOther⟩

-- ============================================================================
-- §2  The cross-core cancellation transitions (plan SM6.E.1 / SM6.E.3 / SM6.E.5)
-- ============================================================================

/-- WS-SM SM6.E.5 (plan §3.1): IPC-blocking cancellation across cores.

The single-core `cancelIpcBlocking` object-level teardown (endpoint /
notification dequeue, reply-link consume, TCB IPC-field clear — the suspend
pipeline's G2) composed with the cross-core deschedule: the victim is removed
from its *home* core's run queue / current slot (the cross-core
generalisation of G4's bootCore-pinned `removeRunnable`), and a `.reschedule`
SGI is surfaced when the victim was actively current on a *remote* home core
(the cross-core generalisation of G7's local reschedule).

The home core and active status are pre-resolved from the **pre-state**,
mirroring the SM3.B lock-set pre-resolution discipline; this coincides with
post-teardown resolution because the teardown never touches the scheduler
(`cancelIpcBlocking_scheduler_eq`) nor any TCB's `cpuAffinity`
(`restoreToReady` / the sweeps rewrite only IPC and queue-link fields) — the
coincidence is explicit in `cancelIpcBlockingOnCore_eq_descheduleThread`.

Returns the post-state paired with the optional cross-core SGI to emit after
the state commit.  Total (the single-core teardown is pure), so a
`withLockSet` bracket always releases cleanly. -/
def cancelIpcBlockingOnCore (victim : SeLe4n.ThreadId) (tcb : TCB)
    (executingCore : CoreId) (st : SystemState) :
    SystemState × Option (CoreId × SgiKind) :=
  let home := determineTargetCore st victim
  let st' := removeRunnableOnCore (cancelIpcBlocking st victim tcb) victim home
  let sgi : Option (CoreId × SgiKind) :=
    match st.getTcb? victim with
    | none => none
    | some _ =>
        if st.scheduler.currentOnCore home = some victim ∧ home ≠ executingCore
        then some (home, SgiKind.reschedule)
        else none
  (st', sgi)

/-- WS-SM SM6.E.3 (plan §3.1): the R5.A in-place SchedContext unbind arm,
across cores.

Textual twin of `cancelBoundDonation` with the replenish-queue purge
parametrised by `rqCore` — the core whose replenish queue holds the
SchedContext's pending replenishments.  Under the SM5.H affinity invariant
(`replenishQueueAffinityConsistentOnCore`) that is the bound thread's *home*
core, which the dispatcher `cancelDonationOnCore` resolves via
`determineTargetCore`; the single-core form is exactly the `bootCoreId`
instance (`cancelBoundDonationOnCore_bootCoreId`). -/
def cancelBoundDonationOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (rqCore : CoreId) : Except KernelError SystemState :=
  match tcb.schedContextBinding with
  | .bound scId =>
    let st1 : SystemState := match st.getSchedContext? scId with
      | some sc =>
        let sc' := { sc with boundThread := none, isActive := false }
        { st with objects := st.objects.insert scId.toObjId (.schedContext sc') }
      | none => st
    let st2 := { st1 with scheduler := st1.scheduler.setReplenishQueueOnCore rqCore (ReplenishQueue.remove (st1.scheduler.replenishQueueOnCore rqCore) scId) }
    let st2 := { st2 with scThreadIndex :=
      (scThreadIndexRemove st2.scThreadIndex scId tid) }
    .ok (match st2.getTcb? tid with
    | some tcb' =>
      let tcb'' := { tcb' with schedContextBinding := .unbound }
      { st2 with objects := st2.objects.insert tid.toObjId (.tcb tcb'') }
    | none => st2)
  | _ => .error .illegalState

/-- WS-SM SM6.E.3: `cancelBoundDonationOnCore` at the boot core is exactly the
single-core `cancelBoundDonation` — the SM5.A backward-compatibility bridge. -/
@[simp] theorem cancelBoundDonationOnCore_bootCoreId (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) :
    cancelBoundDonationOnCore st tid tcb bootCoreId
      = cancelBoundDonation st tid tcb := rfl

/-- WS-SM SM6.E.3 (plan §3.1): donation cancellation across cores — the R5.A
dispatcher, per-core.

Dispatches on the victim's `schedContextBinding` exactly as the single-core
`cancelDonation`: `.unbound` is a no-op, `.bound` routes to the per-core
unbind arm (replenish-queue purge on the victim's *home* core,
`determineTargetCore`), `.donated` routes to `cancelDonatedDonation`
(object writes only — `returnDonatedSchedContext` is core-independent).

Returns the post-state paired with the `Except` outcome; on an error the
**pre-state** is returned so a `withLockSet` bracket still releases cleanly
(the SM6.A/B/C error convention).  No SGI is ever surfaced — donation
cancellation wakes no thread and never disturbs another core's current
slot (`cancelDonationOnCore_runQueue_current_eq`). -/
def cancelDonationOnCore (tid : SeLe4n.ThreadId) (tcb : TCB)
    (st : SystemState) : SystemState × Except KernelError Unit :=
  match tcb.schedContextBinding with
  | .unbound => (st, .ok ())
  | .bound _ =>
      match cancelBoundDonationOnCore st tid tcb (determineTargetCore st tid) with
      | .ok st' => (st', .ok ())
      | .error e => (st, .error e)
  | .donated _ _ =>
      match cancelDonatedDonation st tid tcb with
      | .ok st' => (st', .ok ())
      | .error e => (st, .error e)

-- ============================================================================
-- §3  Path/shape reduction lemmas
-- ============================================================================

/-- WS-SM SM6.E: the post-state of the cross-core cancellation is exactly the
single-core teardown followed by the home-core removal — the SGI decision
never alters the state. -/
theorem cancelIpcBlockingOnCore_state_eq (victim : SeLe4n.ThreadId) (tcb : TCB)
    (executingCore : CoreId) (st : SystemState) :
    (cancelIpcBlockingOnCore victim tcb executingCore st).1
      = removeRunnableOnCore (cancelIpcBlocking st victim tcb) victim
          (determineTargetCore st victim) := rfl

/-- WS-SM SM6.E: the cross-core cancellation's **object-level** effect is
exactly the single-core `cancelIpcBlocking`'s — the deschedule touches only
the scheduler. -/
theorem cancelIpcBlockingOnCore_objects_eq (victim : SeLe4n.ThreadId) (tcb : TCB)
    (executingCore : CoreId) (st : SystemState) :
    (cancelIpcBlockingOnCore victim tcb executingCore st).1.objects
      = (cancelIpcBlocking st victim tcb).objects := rfl

/-- WS-SM SM6.E (pre-state/post-state resolution coincidence): when the
teardown preserves the victim's home core and TCB-resolution status — which
it always does semantically (`cancelIpcBlocking` rewrites only IPC and
queue-link fields, never `cpuAffinity`, and never deletes the victim's TCB);
the two hypotheses make the frame explicit at the composition site — the
pre-resolved composite **is** the post-resolved primitive composition
`descheduleThread ∘ cancelIpcBlocking`. -/
theorem cancelIpcBlockingOnCore_eq_descheduleThread
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (st : SystemState)
    (hHome : determineTargetCore (cancelIpcBlocking st victim tcb) victim
       = determineTargetCore st victim)
    (hSome : ((cancelIpcBlocking st victim tcb).getTcb? victim).isSome
       = (st.getTcb? victim).isSome) :
    cancelIpcBlockingOnCore victim tcb executingCore st
      = descheduleThread (cancelIpcBlocking st victim tcb) victim executingCore := by
  unfold cancelIpcBlockingOnCore descheduleThread
  rw [hHome, cancelIpcBlocking_scheduler_eq]
  cases hPre : st.getTcb? victim with
  | none =>
      rw [hPre] at hSome
      cases hPost : (cancelIpcBlocking st victim tcb).getTcb? victim with
      | none => rfl
      | some _ => rw [hPost] at hSome; simp at hSome
  | some _ =>
      rw [hPre] at hSome
      cases hPost : (cancelIpcBlocking st victim tcb).getTcb? victim with
      | none => rw [hPost] at hSome; simp at hSome
      | some _ => rfl

/-- WS-SM SM6.E: a `.ready` victim's cancellation is a pure cross-core
deschedule — the object-level teardown is the identity, so the composite is
`descheduleThread` on the pre-state.  This is the suspend-of-a-running-thread
scenario (the victim was executing or queued, not blocked). -/
theorem cancelIpcBlockingOnCore_ready_eq_descheduleThread
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (st : SystemState) (hReady : tcb.ipcState = .ready) :
    cancelIpcBlockingOnCore victim tcb executingCore st
      = descheduleThread st victim executingCore := by
  have hId : cancelIpcBlocking st victim tcb = st := by
    unfold cancelIpcBlocking
    rw [hReady]
  unfold cancelIpcBlockingOnCore descheduleThread
  rw [hId]

-- ============================================================================
-- §4  SGI emission of the cross-core cancellation composite
-- ============================================================================

/-- WS-SM SM6.E.5: cancelling a victim **actively current on a remote home
core** surfaces a `.reschedule` SGI targeting that core — the cross-core poke
the runtime fires after the state commit, so the remote core stops executing
the cancelled thread. -/
theorem cancelIpcBlockingOnCore_emits_sgi_if_remote_current
    (victim : SeLe4n.ThreadId) (tcb tcb0 : TCB) (executingCore : CoreId)
    (st : SystemState)
    (hTcb : st.getTcb? victim = some tcb0)
    (hCur : st.scheduler.currentOnCore (determineTargetCore st victim) = some victim)
    (hRemote : determineTargetCore st victim ≠ executingCore) :
    (cancelIpcBlockingOnCore victim tcb executingCore st).2
      = some (determineTargetCore st victim, SgiKind.reschedule) := by
  unfold cancelIpcBlockingOnCore
  simp only [hTcb]
  rw [if_pos ⟨hCur, hRemote⟩]

/-- WS-SM SM6.E.5: cancelling a victim whose home core is the executing core
surfaces no SGI — the caller (the suspend pipeline's G7) reschedules
synchronously. -/
theorem cancelIpcBlockingOnCore_no_sgi_if_local
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (st : SystemState)
    (hLocal : determineTargetCore st victim = executingCore) :
    (cancelIpcBlockingOnCore victim tcb executingCore st).2 = none := by
  unfold cancelIpcBlockingOnCore
  cases hT : st.getTcb? victim with
  | none => rfl
  | some _ =>
      simp only []
      rw [if_neg (fun h => h.2 hLocal)]

/-- WS-SM SM6.E.5: cancelling a victim that is **not current** on its home
core — the ordinary case of a genuinely IPC-blocked victim (blocked threads
are neither queued nor current) — surfaces no SGI: the object-level dequeue
plus the (no-op) run-queue removal suffice, no core is executing it. -/
theorem cancelIpcBlockingOnCore_no_sgi_if_not_current
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (st : SystemState)
    (hNotCur : st.scheduler.currentOnCore (determineTargetCore st victim)
        ≠ some victim) :
    (cancelIpcBlockingOnCore victim tcb executingCore st).2 = none := by
  unfold cancelIpcBlockingOnCore
  cases hT : st.getTcb? victim with
  | none => rfl
  | some _ =>
      simp only []
      rw [if_neg (fun h => hNotCur h.1)]

/-- WS-SM SM6.E.5 (ghost-guard): a victim that does not resolve to a TCB pokes
nothing. -/
theorem cancelIpcBlockingOnCore_no_sgi_if_ghost
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (st : SystemState)
    (hGhost : st.getTcb? victim = none) :
    (cancelIpcBlockingOnCore victim tcb executingCore st).2 = none := by
  unfold cancelIpcBlockingOnCore
  simp only [hGhost]

-- ============================================================================
-- §5  Lock-set footprints (plan §3.1) + pre-resolution helpers
-- ============================================================================

/-- WS-SM SM6.E.1: the endpoint a cancellation would dequeue the victim from —
pre-resolved from the victim's `ipcState` (the queue-membership invariant
pins a blocked thread to exactly this queue). -/
def cancelBlockedEndpoint? (tcb : TCB) : Option SeLe4n.ObjId :=
  match tcb.ipcState with
  | .blockedOnSend ep | .blockedOnReceive ep | .blockedOnCall ep => some ep
  | _ => none

/-- WS-SM SM6.E.1: the notification a cancellation would drop the victim's
wait-list entry from — pre-resolved from the victim's `ipcState`. -/
def cancelBlockedNotification? (tcb : TCB) : Option SeLe4n.ObjId :=
  match tcb.ipcState with
  | .blockedOnNotification n => some n
  | _ => none

/-- WS-SM SM6.E.1: the Reply object whose `caller` back-link a cancellation
would sever (`consumeReplyLink`) — present iff the victim is `.blockedOnReply`
holding a live `replyObject` forward link. -/
def cancelConsumedReply? (tcb : TCB) : Option SeLe4n.ReplyId :=
  match tcb.ipcState with
  | .blockedOnReply _ _ => tcb.replyObject
  | _ => none

/-- WS-SM SM6.E.3: the SchedContext a donation cancellation would write —
the victim's bound or donated SC. -/
def cancelBindingSc? (tcb : TCB) : Option SeLe4n.SchedContextId :=
  match tcb.schedContextBinding with
  | .bound scId => some scId
  | .donated scId _ => some scId
  | .unbound => none

/-- WS-SM SM6.E.3: the original-owner TCB a donated-arm cancellation would
re-bind the SC to (the plan row's "receiver TCB"). -/
def cancelDonatedOwner? (tcb : TCB) : Option SeLe4n.ThreadId :=
  match tcb.schedContextBinding with
  | .donated _ owner => some owner
  | _ => none

/-- WS-SM SM6.E.1 (plan §3.1): the `cancelIpcBlocking` lock-set — victim TCB
(write: IPC-field clear), the blocked-on endpoint (write: dual-queue dequeue
+ neighbour link patches) or notification (write: waiter-list drop), and the
consumed Reply object (write: `reply.caller := none`, the SM6.D reply-object
fold).  At most one of the two queue optionals is `some` (they pre-resolve
from mutually exclusive `ipcState` arms). -/
def lockSet_cancelIpcBlocking (victimTid : SeLe4n.ThreadId)
    (blockedEndpointObjId : Option SeLe4n.ObjId)
    (blockedNotificationObjId : Option SeLe4n.ObjId)
    (consumedReplyId : Option SeLe4n.ReplyId) : LockSet :=
  lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt
      (lockSetOfList [(tcbLock victimTid, .write)])
      (blockedEndpointObjId.map (fun ep => (endpointLock ep, .write))))
      (blockedNotificationObjId.map (fun n => (notificationLock n, .write))))
    (consumedReplyId.map (fun r => (replyLock r, .write)))

/-- WS-SM SM6.E.3 (plan §3.1): the `cancelDonation` lock-set — donor (victim)
TCB (write: binding clear), the bound/donated SchedContext (write:
deactivation / owner re-bind), and the donated-arm original-owner TCB
(write: re-bind to `.bound`). -/
def lockSet_cancelDonation (victimTid : SeLe4n.ThreadId)
    (bindingScId : Option SeLe4n.SchedContextId)
    (donatedOriginalOwnerTid : Option SeLe4n.ThreadId) : LockSet :=
  lockSetExtendOpt (lockSetExtendOpt
      (lockSetOfList [(tcbLock victimTid, .write)])
      (bindingScId.map (fun sc => (schedContextLock sc, .write))))
    (donatedOriginalOwnerTid.map (fun ot => (tcbLock ot, .write)))

/-- WS-SM SM6.E.1: the concrete lock-set a cross-core `cancelIpcBlockingOnCore`
on state `st` acquires — the parametric footprint with the blocked-on object
and consumed reply pre-resolved from the victim's TCB.  This is the footprint
the runtime `withLockSet` bracket acquires before invoking the cancellation. -/
def lockSet_cancelIpcBlockingOnCore (st : SystemState)
    (victimTid : SeLe4n.ThreadId) : LockSet :=
  match st.getTcb? victimTid with
  | some tcb =>
      lockSet_cancelIpcBlocking victimTid (cancelBlockedEndpoint? tcb)
        (cancelBlockedNotification? tcb) (cancelConsumedReply? tcb)
  | none => lockSet_cancelIpcBlocking victimTid none none none

/-- WS-SM SM6.E.3: the concrete lock-set a `cancelDonationOnCore` on state
`st` acquires — the parametric footprint with the SC and donated owner
pre-resolved from the victim's TCB. -/
def lockSet_cancelDonationOnCore (st : SystemState)
    (victimTid : SeLe4n.ThreadId) : LockSet :=
  match st.getTcb? victimTid with
  | some tcb =>
      lockSet_cancelDonation victimTid (cancelBindingSc? tcb)
        (cancelDonatedOwner? tcb)
  | none => lockSet_cancelDonation victimTid none none

-- ============================================================================
-- §6  Lock-set hierarchical correctness (SM3.B.4 discipline)
-- ============================================================================

/-- WS-SM SM6.E.1: every lock the `cancelIpcBlocking` footprint declares has a
kind permitted for the enclosing `.tcbSuspend` syscall (the cancellation runs
inside the suspend dispatch), so the acquisitions respect the SM0.I lock
ladder. -/
theorem lockSet_consistent_cancelIpcBlocking (victimTid : SeLe4n.ThreadId)
    (blEp blN : Option SeLe4n.ObjId) (consumedReplyId : Option SeLe4n.ReplyId) :
    ∀ p ∈ (lockSet_cancelIpcBlocking victimTid blEp blN consumedReplyId).pairs,
      p.fst.kind ∈ permittedKinds .tcbSuspend :=
  lockSet_consistent_base_plus_three_opts _ _ _ _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        exact absurd hMem (by intro h; cases h))
    (by intro pp hpp
        cases blEp with
        | none => simp at hpp
        | some ep => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases blN with
        | none => simp at hpp
        | some n => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases consumedReplyId with
        | none => simp at hpp
        | some r => simp at hpp; rw [← hpp]; simp; decide)

/-- WS-SM SM6.E.3: every lock the `cancelDonation` footprint declares has a
kind permitted for the enclosing `.tcbSuspend` syscall. -/
theorem lockSet_consistent_cancelDonation (victimTid : SeLe4n.ThreadId)
    (bindingScId : Option SeLe4n.SchedContextId)
    (donatedOriginalOwnerTid : Option SeLe4n.ThreadId) :
    ∀ p ∈ (lockSet_cancelDonation victimTid bindingScId donatedOriginalOwnerTid).pairs,
      p.fst.kind ∈ permittedKinds .tcbSuspend :=
  lockSet_consistent_base_plus_two_opts _ _ _ _
    (by intro p hMem
        rcases List.mem_cons.mp hMem with h | hMem
        · rw [h]; simp; decide
        exact absurd hMem (by intro h; cases h))
    (by intro pp hpp
        cases bindingScId with
        | none => simp at hpp
        | some sc => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases donatedOriginalOwnerTid with
        | none => simp at hpp
        | some ot => simp at hpp; rw [← hpp]; simp; decide)

/-- WS-SM SM6.E.2: the `cancelIpcBlocking` lock-set is **hierarchically
correct** — every declared lock has a permitted kind and the keys are
duplicate-free (the SM3.B well-formedness `LockSet` carries by construction).
Together these are the structural soundness conditions the deadlock-freedom
theorem (2.1.9) and the 2PL serializability corollary (2.1.11) consume. -/
theorem cancelIpcBlockingOnCore_lockSet_correct (victimTid : SeLe4n.ThreadId)
    (blEp blN : Option SeLe4n.ObjId) (consumedReplyId : Option SeLe4n.ReplyId) :
    (∀ p ∈ (lockSet_cancelIpcBlocking victimTid blEp blN consumedReplyId).pairs,
        p.fst.kind ∈ permittedKinds .tcbSuspend) ∧
    ((lockSet_cancelIpcBlocking victimTid blEp blN consumedReplyId).pairs.map
        (·.fst)).Nodup :=
  ⟨lockSet_consistent_cancelIpcBlocking victimTid blEp blN consumedReplyId,
   (lockSet_cancelIpcBlocking victimTid blEp blN consumedReplyId).hUniqueKeys⟩

/-- WS-SM SM6.E.4: the `cancelDonation` lock-set is hierarchically correct. -/
theorem cancelDonationOnCore_lockSet_correct (victimTid : SeLe4n.ThreadId)
    (bindingScId : Option SeLe4n.SchedContextId)
    (donatedOriginalOwnerTid : Option SeLe4n.ThreadId) :
    (∀ p ∈ (lockSet_cancelDonation victimTid bindingScId donatedOriginalOwnerTid).pairs,
        p.fst.kind ∈ permittedKinds .tcbSuspend) ∧
    ((lockSet_cancelDonation victimTid bindingScId donatedOriginalOwnerTid).pairs.map
        (·.fst)).Nodup :=
  ⟨lockSet_consistent_cancelDonation victimTid bindingScId donatedOriginalOwnerTid,
   (lockSet_cancelDonation victimTid bindingScId donatedOriginalOwnerTid).hUniqueKeys⟩

/-- WS-SM SM6.E.1: the **state-resolved** cancellation lock-set
(`lockSet_cancelIpcBlockingOnCore`, options pre-resolved from `st`) is
hierarchically correct — the form the runtime acquisition consumes. -/
theorem lockSet_cancelIpcBlockingOnCore_correct (st : SystemState)
    (victimTid : SeLe4n.ThreadId) :
    ∀ p ∈ (lockSet_cancelIpcBlockingOnCore st victimTid).pairs,
      p.fst.kind ∈ permittedKinds .tcbSuspend := by
  unfold lockSet_cancelIpcBlockingOnCore
  cases st.getTcb? victimTid with
  | some tcb =>
      exact lockSet_consistent_cancelIpcBlocking victimTid _ _ _
  | none =>
      exact lockSet_consistent_cancelIpcBlocking victimTid none none none

/-- WS-SM SM6.E.3: the state-resolved donation-cancellation lock-set is
hierarchically correct. -/
theorem lockSet_cancelDonationOnCore_correct (st : SystemState)
    (victimTid : SeLe4n.ThreadId) :
    ∀ p ∈ (lockSet_cancelDonationOnCore st victimTid).pairs,
      p.fst.kind ∈ permittedKinds .tcbSuspend := by
  unfold lockSet_cancelDonationOnCore
  cases st.getTcb? victimTid with
  | some tcb => exact lockSet_consistent_cancelDonation victimTid _ _
  | none => exact lockSet_consistent_cancelDonation victimTid none none

-- ============================================================================
-- §7  Write coverage — every cancellation write is under a declared write lock
-- ============================================================================

/-- A **write**-mode pair survives any `insertOrMerge`: the merge branch maps
`(l', .write)` to `(l', .write.lub m) = (l', .write)` when the keys coincide
(write is the `AccessMode.lub` top) and leaves it untouched otherwise; the
prepend branch keeps it in the tail.  The mode-aware strengthening of
`mem_insertOrMerge_of_mem_of_ne` — no key-distinctness side-condition. -/
theorem mem_insertOrMerge_write_of_mem_write (S : LockSet) (l : LockId)
    (m : AccessMode) (l' : LockId)
    (hMem : (l', AccessMode.write) ∈ S.pairs) :
    (l', AccessMode.write) ∈ (S.insertOrMerge l m).pairs := by
  unfold LockSet.insertOrMerge
  split
  · -- Merge branch: the map fixes write-mode pairs.
    apply List.mem_map.mpr
    refine ⟨(l', AccessMode.write), hMem, ?_⟩
    by_cases hEq : l' = l
    · subst hEq
      simp [AccessMode.lub_write_left]
    · simp [hEq]
  · -- Prepend branch.
    exact List.mem_cons_of_mem _ hMem

/-- Write-mode membership survives an optional extension (`none` is identity,
`some` is an `insertOrMerge`). -/
theorem mem_write_lockSetExtendOpt (S : LockSet)
    (opt : Option (LockId × AccessMode)) (l' : LockId)
    (hMem : (l', AccessMode.write) ∈ S.pairs) :
    (l', AccessMode.write) ∈ (lockSetExtendOpt S opt).pairs := by
  cases opt with
  | none => exact hMem
  | some p => exact mem_insertOrMerge_write_of_mem_write S p.fst p.snd l' hMem

/-- WS-SM SM6.E.1 (coverage): the **victim TCB write lock** — under which the
cancellation clears the victim's IPC fields — is a declared member of the
`cancelIpcBlocking` footprint, unconditionally. -/
theorem lockSet_cancelIpcBlocking_victim_tcb_write_mem
    (victimTid : SeLe4n.ThreadId) (blEp blN : Option SeLe4n.ObjId)
    (consumedReplyId : Option SeLe4n.ReplyId) :
    (tcbLock victimTid, AccessMode.write)
      ∈ (lockSet_cancelIpcBlocking victimTid blEp blN consumedReplyId).pairs := by
  unfold lockSet_cancelIpcBlocking
  refine mem_write_lockSetExtendOpt _ _ _ (mem_write_lockSetExtendOpt _ _ _
    (mem_write_lockSetExtendOpt _ _ _ ?_))
  show (tcbLock victimTid, AccessMode.write)
    ∈ ((LockSet.empty.insertOrMerge (tcbLock victimTid) AccessMode.write)).pairs
  exact self_write_mem_insertOrMerge _ (tcbLock victimTid)

/-- WS-SM SM6.E.1 (coverage): the **blocked-on endpoint write lock** — under
which the cancellation dequeues the victim and patches its queue neighbours —
is a declared member whenever the endpoint is resolved. -/
theorem lockSet_cancelIpcBlocking_blocked_endpoint_write_mem
    (victimTid : SeLe4n.ThreadId) (ep : SeLe4n.ObjId)
    (blN : Option SeLe4n.ObjId) (consumedReplyId : Option SeLe4n.ReplyId) :
    (endpointLock ep, AccessMode.write)
      ∈ (lockSet_cancelIpcBlocking victimTid (some ep) blN consumedReplyId).pairs := by
  unfold lockSet_cancelIpcBlocking
  refine mem_write_lockSetExtendOpt _ _ _ (mem_write_lockSetExtendOpt _ _ _ ?_)
  simp only [lockSetExtendOpt, Option.map_some]
  exact self_write_mem_insertOrMerge _ (endpointLock ep)

/-- WS-SM SM6.E.1 (coverage): the **blocked-on notification write lock** —
under which the cancellation drops the victim's waiter-list entry — is a
declared member whenever the notification is resolved. -/
theorem lockSet_cancelIpcBlocking_blocked_notification_write_mem
    (victimTid : SeLe4n.ThreadId) (blEp : Option SeLe4n.ObjId)
    (n : SeLe4n.ObjId) (consumedReplyId : Option SeLe4n.ReplyId) :
    (notificationLock n, AccessMode.write)
      ∈ (lockSet_cancelIpcBlocking victimTid blEp (some n) consumedReplyId).pairs := by
  unfold lockSet_cancelIpcBlocking
  refine mem_write_lockSetExtendOpt _ _ _ ?_
  simp only [lockSetExtendOpt, Option.map_some]
  exact self_write_mem_insertOrMerge _ (notificationLock n)

/-- WS-SM SM6.E.1 (coverage): the **consumed Reply object write lock** — under
which the cancellation severs the single-use `reply.caller` back-link — is a
declared member whenever the reply is resolved. -/
theorem lockSet_cancelIpcBlocking_consumed_reply_write_mem
    (victimTid : SeLe4n.ThreadId) (blEp blN : Option SeLe4n.ObjId)
    (r : SeLe4n.ReplyId) :
    (replyLock r, AccessMode.write)
      ∈ (lockSet_cancelIpcBlocking victimTid blEp blN (some r)).pairs := by
  unfold lockSet_cancelIpcBlocking
  simp only [lockSetExtendOpt, Option.map_some]
  exact self_write_mem_insertOrMerge _ (replyLock r)

/-- WS-SM SM6.E.3 (coverage): the **victim (donor) TCB write lock** is a
declared member of the `cancelDonation` footprint, unconditionally. -/
theorem lockSet_cancelDonation_victim_tcb_write_mem
    (victimTid : SeLe4n.ThreadId) (bindingScId : Option SeLe4n.SchedContextId)
    (donatedOriginalOwnerTid : Option SeLe4n.ThreadId) :
    (tcbLock victimTid, AccessMode.write)
      ∈ (lockSet_cancelDonation victimTid bindingScId donatedOriginalOwnerTid).pairs := by
  unfold lockSet_cancelDonation
  refine mem_write_lockSetExtendOpt _ _ _ (mem_write_lockSetExtendOpt _ _ _ ?_)
  show (tcbLock victimTid, AccessMode.write)
    ∈ ((LockSet.empty.insertOrMerge (tcbLock victimTid) AccessMode.write)).pairs
  exact self_write_mem_insertOrMerge _ (tcbLock victimTid)

/-- WS-SM SM6.E.3 (coverage): the **SchedContext write lock** — under which
the bound arm deactivates the SC and the donated arm re-binds it — is a
declared member whenever the SC is resolved. -/
theorem lockSet_cancelDonation_binding_sc_write_mem
    (victimTid : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (donatedOriginalOwnerTid : Option SeLe4n.ThreadId) :
    (schedContextLock scId, AccessMode.write)
      ∈ (lockSet_cancelDonation victimTid (some scId) donatedOriginalOwnerTid).pairs := by
  unfold lockSet_cancelDonation
  refine mem_write_lockSetExtendOpt _ _ _ ?_
  simp only [lockSetExtendOpt, Option.map_some]
  exact self_write_mem_insertOrMerge _ (schedContextLock scId)

/-- WS-SM SM6.E.3 (coverage): the **original-owner TCB write lock** — under
which the donated arm re-establishes the owner's `.bound` binding — is a
declared member whenever the owner is resolved. -/
theorem lockSet_cancelDonation_donated_owner_tcb_write_mem
    (victimTid : SeLe4n.ThreadId) (bindingScId : Option SeLe4n.SchedContextId)
    (ot : SeLe4n.ThreadId) :
    (tcbLock ot, AccessMode.write)
      ∈ (lockSet_cancelDonation victimTid bindingScId (some ot)).pairs := by
  unfold lockSet_cancelDonation
  simp only [lockSetExtendOpt, Option.map_some]
  exact self_write_mem_insertOrMerge _ (tcbLock ot)

-- ============================================================================
-- §8  Suspend-footprint coverage — the SM6.E.1/SM6.E.3 migration content
-- ============================================================================
-- Every lock the cancellation sub-operations write under is a declared
-- member of the enclosing `lockSet_tcbSuspend` footprint: the cancellation
-- runs inside the `.tcbSuspend` syscall's 2PL bracket with all its writes
-- already covered.  Member-by-member (the SM6.B §6 pattern).

/-- WS-SM SM6.E.1 (coverage in suspend): the victim TCB write lock is a
declared member of the suspend footprint, unconditionally. -/
theorem lockSet_tcbSuspend_victim_tcb_write_mem
    (callerTid : SeLe4n.ThreadId) (cnRoot : SeLe4n.ObjId)
    (targetTcbTid : SeLe4n.ThreadId) (blEp blN : Option SeLe4n.ObjId)
    (bindingScId : Option SeLe4n.SchedContextId)
    (donatedOriginalOwnerTid : Option SeLe4n.ThreadId)
    (consumedReplyId : Option SeLe4n.ReplyId) :
    (tcbLock targetTcbTid, AccessMode.write)
      ∈ (lockSet_tcbSuspend callerTid cnRoot targetTcbTid blEp blN
           bindingScId donatedOriginalOwnerTid consumedReplyId).pairs := by
  unfold lockSet_tcbSuspend
  refine mem_write_lockSetExtendOpt _ _ _ (mem_write_lockSetExtendOpt _ _ _
    (mem_write_lockSetExtendOpt _ _ _ (mem_write_lockSetExtendOpt _ _ _
      (mem_write_lockSetExtendOpt _ _ _ ?_))))
  show (tcbLock targetTcbTid, AccessMode.write)
    ∈ (((LockSet.empty.insertOrMerge (tcbLock callerTid) AccessMode.read).insertOrMerge
        (cnodeLock cnRoot) AccessMode.read).insertOrMerge (tcbLock targetTcbTid)
        AccessMode.write).pairs
  exact self_write_mem_insertOrMerge _ (tcbLock targetTcbTid)

/-- WS-SM SM6.E.1 (coverage in suspend): the blocked-on endpoint write lock is
a declared member of the suspend footprint whenever resolved. -/
theorem lockSet_tcbSuspend_blocked_endpoint_write_mem
    (callerTid : SeLe4n.ThreadId) (cnRoot : SeLe4n.ObjId)
    (targetTcbTid : SeLe4n.ThreadId) (ep : SeLe4n.ObjId)
    (blN : Option SeLe4n.ObjId) (bindingScId : Option SeLe4n.SchedContextId)
    (donatedOriginalOwnerTid : Option SeLe4n.ThreadId)
    (consumedReplyId : Option SeLe4n.ReplyId) :
    (endpointLock ep, AccessMode.write)
      ∈ (lockSet_tcbSuspend callerTid cnRoot targetTcbTid (some ep) blN
           bindingScId donatedOriginalOwnerTid consumedReplyId).pairs := by
  unfold lockSet_tcbSuspend
  refine mem_write_lockSetExtendOpt _ _ _ (mem_write_lockSetExtendOpt _ _ _
    (mem_write_lockSetExtendOpt _ _ _ (mem_write_lockSetExtendOpt _ _ _ ?_)))
  simp only [lockSetExtendOpt, Option.map_some]
  exact self_write_mem_insertOrMerge _ (endpointLock ep)

/-- WS-SM SM6.E.1 (coverage in suspend): the blocked-on notification write
lock is a declared member of the suspend footprint whenever resolved. -/
theorem lockSet_tcbSuspend_blocked_notification_write_mem
    (callerTid : SeLe4n.ThreadId) (cnRoot : SeLe4n.ObjId)
    (targetTcbTid : SeLe4n.ThreadId) (blEp : Option SeLe4n.ObjId)
    (n : SeLe4n.ObjId) (bindingScId : Option SeLe4n.SchedContextId)
    (donatedOriginalOwnerTid : Option SeLe4n.ThreadId)
    (consumedReplyId : Option SeLe4n.ReplyId) :
    (notificationLock n, AccessMode.write)
      ∈ (lockSet_tcbSuspend callerTid cnRoot targetTcbTid blEp (some n)
           bindingScId donatedOriginalOwnerTid consumedReplyId).pairs := by
  unfold lockSet_tcbSuspend
  refine mem_write_lockSetExtendOpt _ _ _ (mem_write_lockSetExtendOpt _ _ _
    (mem_write_lockSetExtendOpt _ _ _ ?_))
  simp only [lockSetExtendOpt, Option.map_some]
  exact self_write_mem_insertOrMerge _ (notificationLock n)

/-- WS-SM SM6.E.3 (coverage in suspend): the SchedContext write lock is a
declared member of the suspend footprint whenever resolved. -/
theorem lockSet_tcbSuspend_binding_sc_write_mem
    (callerTid : SeLe4n.ThreadId) (cnRoot : SeLe4n.ObjId)
    (targetTcbTid : SeLe4n.ThreadId) (blEp blN : Option SeLe4n.ObjId)
    (scId : SeLe4n.SchedContextId)
    (donatedOriginalOwnerTid : Option SeLe4n.ThreadId)
    (consumedReplyId : Option SeLe4n.ReplyId) :
    (schedContextLock scId, AccessMode.write)
      ∈ (lockSet_tcbSuspend callerTid cnRoot targetTcbTid blEp blN
           (some scId) donatedOriginalOwnerTid consumedReplyId).pairs := by
  unfold lockSet_tcbSuspend
  refine mem_write_lockSetExtendOpt _ _ _ (mem_write_lockSetExtendOpt _ _ _ ?_)
  simp only [lockSetExtendOpt, Option.map_some]
  exact self_write_mem_insertOrMerge _ (schedContextLock scId)

/-- WS-SM SM6.E.3 (coverage in suspend): the donated-arm original-owner TCB
write lock is a declared member of the suspend footprint whenever resolved. -/
theorem lockSet_tcbSuspend_donated_owner_tcb_write_mem
    (callerTid : SeLe4n.ThreadId) (cnRoot : SeLe4n.ObjId)
    (targetTcbTid : SeLe4n.ThreadId) (blEp blN : Option SeLe4n.ObjId)
    (bindingScId : Option SeLe4n.SchedContextId) (ot : SeLe4n.ThreadId)
    (consumedReplyId : Option SeLe4n.ReplyId) :
    (tcbLock ot, AccessMode.write)
      ∈ (lockSet_tcbSuspend callerTid cnRoot targetTcbTid blEp blN
           bindingScId (some ot) consumedReplyId).pairs := by
  unfold lockSet_tcbSuspend
  refine mem_write_lockSetExtendOpt _ _ _ ?_
  simp only [lockSetExtendOpt, Option.map_some]
  exact self_write_mem_insertOrMerge _ (tcbLock ot)

/-- WS-SM SM6.E.1 (coverage in suspend): the consumed Reply object write lock —
the SM6.E `lockSet_tcbSuspend` extension closing the SM6.D reply-fold footprint
gap — is a declared member whenever resolved. -/
theorem lockSet_tcbSuspend_consumed_reply_write_mem
    (callerTid : SeLe4n.ThreadId) (cnRoot : SeLe4n.ObjId)
    (targetTcbTid : SeLe4n.ThreadId) (blEp blN : Option SeLe4n.ObjId)
    (bindingScId : Option SeLe4n.SchedContextId)
    (donatedOriginalOwnerTid : Option SeLe4n.ThreadId) (r : SeLe4n.ReplyId) :
    (replyLock r, AccessMode.write)
      ∈ (lockSet_tcbSuspend callerTid cnRoot targetTcbTid blEp blN
           bindingScId donatedOriginalOwnerTid (some r)).pairs := by
  unfold lockSet_tcbSuspend
  simp only [lockSetExtendOpt, Option.map_some]
  exact self_write_mem_insertOrMerge _ (replyLock r)

-- ============================================================================
-- §9  SM6.E.2 / SM6.E.4 — 2PL atomicity of cancellation under its lock-set
-- ============================================================================

/-- WS-SM SM6.E.2 (plan §5 `cancelIpcBlocking_atomic_under_lockSet`, Theorem
2.1.10): under its `cancelIpcBlocking` lock-set the single-core cancellation
teardown is a single two-phase-locked atomic step — wrapping it in
`withLockSet` decomposes deterministically into the acquire fold, the
teardown, and the release fold.  No partially-torn-down victim (dequeued but
IPC fields uncleared, or reply link half-severed) is observable to a
lock-insensitive observer. -/
theorem cancelIpcBlocking_atomic_under_lockSet
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (blEp blN : Option SeLe4n.ObjId) (consumedReplyId : Option SeLe4n.ReplyId)
    (s : SystemState) :
    withLockSet (lockSet_cancelIpcBlocking victim blEp blN consumedReplyId)
        executingCore (fun st => (cancelIpcBlocking st victim tcb, ())) s
      = (releaseAll executingCore
          (lockSet_cancelIpcBlocking victim blEp blN consumedReplyId).lockAcquireSequence.reverse
          (cancelIpcBlocking
            (acquireAll executingCore
              (lockSet_cancelIpcBlocking victim blEp blN consumedReplyId).lockAcquireSequence s)
            victim tcb),
         ()) :=
  lockSet_atomic_under_2pl _ executingCore _ s

/-- WS-SM SM6.E.2 (companion): the cross-core cancellation composite is
likewise a single 2PL-atomic step under the same lock-set — the surfaced SGI
is computed inside the bracket and fired by the runtime after the commit. -/
theorem cancelIpcBlockingOnCore_atomic_under_lockSet
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (blEp blN : Option SeLe4n.ObjId) (consumedReplyId : Option SeLe4n.ReplyId)
    (s : SystemState) :
    withLockSet (lockSet_cancelIpcBlocking victim blEp blN consumedReplyId)
        executingCore (cancelIpcBlockingOnCore victim tcb executingCore) s
      = (releaseAll executingCore
          (lockSet_cancelIpcBlocking victim blEp blN consumedReplyId).lockAcquireSequence.reverse
          (cancelIpcBlockingOnCore victim tcb executingCore
            (acquireAll executingCore
              (lockSet_cancelIpcBlocking victim blEp blN consumedReplyId).lockAcquireSequence s)).1,
         (cancelIpcBlockingOnCore victim tcb executingCore
            (acquireAll executingCore
              (lockSet_cancelIpcBlocking victim blEp blN consumedReplyId).lockAcquireSequence s)).2) :=
  lockSet_atomic_under_2pl _ executingCore _ s

/-- WS-SM SM6.E.4 (plan §5 `cancelDonation_atomic_under_lockSet`, Theorem
2.1.10): under its `cancelDonation` lock-set the single-core donation
cancellation is a single 2PL-atomic step.  The adapter returns the pre-state
on an error so the bracket's release fold applies to a well-defined state on
every path. -/
theorem cancelDonation_atomic_under_lockSet
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (bindingScId : Option SeLe4n.SchedContextId)
    (donatedOriginalOwnerTid : Option SeLe4n.ThreadId)
    (s : SystemState) :
    withLockSet (lockSet_cancelDonation victim bindingScId donatedOriginalOwnerTid)
        executingCore
        (fun st => match cancelDonation st victim tcb with
          | .ok st' => (st', Except.ok ())
          | .error e => (st, Except.error e)) s
      = (releaseAll executingCore
          (lockSet_cancelDonation victim bindingScId donatedOriginalOwnerTid).lockAcquireSequence.reverse
          ((fun st => match cancelDonation st victim tcb with
            | .ok st' => (st', Except.ok ())
            | .error e => (st, Except.error e))
            (acquireAll executingCore
              (lockSet_cancelDonation victim bindingScId donatedOriginalOwnerTid).lockAcquireSequence s)).1,
         ((fun st => match cancelDonation st victim tcb with
            | .ok st' => (st', Except.ok ())
            | .error e => (st, Except.error e))
            (acquireAll executingCore
              (lockSet_cancelDonation victim bindingScId donatedOriginalOwnerTid).lockAcquireSequence s)).2) :=
  lockSet_atomic_under_2pl _ executingCore _ s

/-- WS-SM SM6.E.4 (companion): the per-core donation-cancellation dispatcher
is likewise a single 2PL-atomic step under the same lock-set. -/
theorem cancelDonationOnCore_atomic_under_lockSet
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (bindingScId : Option SeLe4n.SchedContextId)
    (donatedOriginalOwnerTid : Option SeLe4n.ThreadId)
    (s : SystemState) :
    withLockSet (lockSet_cancelDonation victim bindingScId donatedOriginalOwnerTid)
        executingCore (cancelDonationOnCore victim tcb) s
      = (releaseAll executingCore
          (lockSet_cancelDonation victim bindingScId donatedOriginalOwnerTid).lockAcquireSequence.reverse
          (cancelDonationOnCore victim tcb
            (acquireAll executingCore
              (lockSet_cancelDonation victim bindingScId donatedOriginalOwnerTid).lockAcquireSequence s)).1,
         (cancelDonationOnCore victim tcb
            (acquireAll executingCore
              (lockSet_cancelDonation victim bindingScId donatedOriginalOwnerTid).lockAcquireSequence s)).2) :=
  lockSet_atomic_under_2pl _ executingCore _ s

-- ============================================================================
-- §10  Invariant preservation + per-core donation frames
-- ============================================================================

/-- WS-SM SM6.E: the cross-core cancellation preserves `objects.invExt` — the
object-level effect is exactly the single-core teardown's
(`cancelIpcBlocking_preserves_objects_invExt`); the deschedule never touches
`objects`. -/
theorem cancelIpcBlockingOnCore_preserves_objects_invExt
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (st : SystemState) (hInv : st.objects.invExt) :
    (cancelIpcBlockingOnCore victim tcb executingCore st).1.objects.invExt := by
  rw [cancelIpcBlockingOnCore_objects_eq]
  exact cancelIpcBlocking_preserves_objects_invExt st victim tcb hInv

/-- WS-SM SM6.E.3: `cancelBoundDonationOnCore` preserves `objects.invExt` —
the per-core replenish-queue purge does not touch `objects`; the object
writes are the same SchedContext deactivation and TCB unbind inserts as the
single-core arm. -/
theorem cancelBoundDonationOnCore_preserves_objects_invExt
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) (rqCore : CoreId)
    (hInv : st.objects.invExt)
    (h : cancelBoundDonationOnCore st tid tcb rqCore = .ok st') :
    st'.objects.invExt := by
  unfold cancelBoundDonationOnCore at h
  split at h
  · injection h with h
    subst h
    dsimp only
    repeat' first
      | exact hInv
      | exact RobinHood.RHTable.insert_preserves_invExt _ _ _ hInv
      | apply RobinHood.RHTable.insert_preserves_invExt
      | split
  · cases h

/-- WS-SM SM6.E.3: the per-core donation-cancellation dispatcher preserves
`objects.invExt` on every arm and every outcome (the error paths return the
pre-state). -/
theorem cancelDonationOnCore_preserves_objects_invExt
    (tid : SeLe4n.ThreadId) (tcb : TCB) (st : SystemState)
    (hInv : st.objects.invExt) :
    (cancelDonationOnCore tid tcb st).1.objects.invExt := by
  unfold cancelDonationOnCore
  cases hB : tcb.schedContextBinding with
  | unbound => exact hInv
  | bound scId =>
      cases hE : cancelBoundDonationOnCore st tid tcb (determineTargetCore st tid) with
      | ok st' =>
          exact cancelBoundDonationOnCore_preserves_objects_invExt _ _ _ _ _ hInv hE
      | error e => exact hInv
  | donated scId owner =>
      cases hE : cancelDonatedDonation st tid tcb with
      | ok st' =>
          exact cancelDonatedDonation_preserves_objects_invExt _ _ _ _ hInv hE
      | error e => exact hInv

/-- WS-SM SM6.E.3: `cancelDonatedDonation` preserves the **full** scheduler
(the donated-arm return is object writes only) — the ∀-core strengthening of
the bootCore-pinned `cancelDonatedDonation_scheduler_runQueue_eq`. -/
theorem cancelDonatedDonation_scheduler_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (h : cancelDonatedDonation st tid tcb = .ok st') :
    st'.scheduler = st.scheduler := by
  simp only [cancelDonatedDonation] at h
  split at h
  · exact cleanupDonatedSchedContext_scheduler_eq st st' tid h
  · cases h

/-- WS-SM SM6.E.3: the bound arm's per-core purge edits **only** core
`rqCore`'s replenish-queue slot — every core's run queue and current slot are
exactly the pre-state's (the donation cancellation wakes and deschedules
nothing). -/
theorem cancelBoundDonationOnCore_runQueue_current_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) (rqCore : CoreId)
    (c : CoreId)
    (h : cancelBoundDonationOnCore st tid tcb rqCore = .ok st') :
    st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c
    ∧ st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c := by
  simp only [cancelBoundDonationOnCore] at h
  split at h
  · injection h with h
    subst h
    constructor
    · split <;> (split <;> simp)
    · split <;> (split <;> simp)
  · cases h

/-- WS-SM SM6.E.3 (the per-core purge, positively): on the `.bound scId` arm
the SchedContext's pending replenishments are removed from core `rqCore`'s
replenish queue — the cross-core generalisation of the single-core arm's
bootCore-pinned purge. -/
theorem cancelBoundDonationOnCore_replenishQueue_purged
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) (rqCore : CoreId)
    (scId : SeLe4n.SchedContextId)
    (hBind : tcb.schedContextBinding = .bound scId)
    (h : cancelBoundDonationOnCore st tid tcb rqCore = .ok st') :
    st'.scheduler.replenishQueueOnCore rqCore
      = ReplenishQueue.remove (st.scheduler.replenishQueueOnCore rqCore) scId := by
  simp only [cancelBoundDonationOnCore, hBind] at h
  injection h with h
  subst h
  split <;> (split <;> simp)

/-- WS-SM SM6.E.3 (per-core locality of the purge): every **other** core's
replenish queue is exactly the pre-state's. -/
theorem cancelBoundDonationOnCore_replenishQueue_ne
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) (rqCore : CoreId)
    (c' : CoreId) (hOther : rqCore ≠ c')
    (h : cancelBoundDonationOnCore st tid tcb rqCore = .ok st') :
    st'.scheduler.replenishQueueOnCore c'
      = st.scheduler.replenishQueueOnCore c' := by
  simp only [cancelBoundDonationOnCore] at h
  split at h
  · injection h with h
    subst h
    split <;> (split <;>
      simp [SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ _ _ _ hOther])
  · cases h

/-- WS-SM SM6.E.3: the per-core donation-cancellation dispatcher never
disturbs any core's run queue or current slot, on any arm and any outcome —
donation cancellation wakes no thread and never needs an SGI. -/
theorem cancelDonationOnCore_runQueue_current_eq
    (tid : SeLe4n.ThreadId) (tcb : TCB) (st : SystemState) (c : CoreId) :
    (cancelDonationOnCore tid tcb st).1.scheduler.runQueueOnCore c
        = st.scheduler.runQueueOnCore c
    ∧ (cancelDonationOnCore tid tcb st).1.scheduler.currentOnCore c
        = st.scheduler.currentOnCore c := by
  unfold cancelDonationOnCore
  cases hB : tcb.schedContextBinding with
  | unbound => exact ⟨rfl, rfl⟩
  | bound scId =>
      cases hE : cancelBoundDonationOnCore st tid tcb (determineTargetCore st tid) with
      | ok st' => exact cancelBoundDonationOnCore_runQueue_current_eq st st' tid tcb _ c hE
      | error e => exact ⟨rfl, rfl⟩
  | donated scId owner =>
      cases hE : cancelDonatedDonation st tid tcb with
      | ok st' =>
          have hS := cancelDonatedDonation_scheduler_eq st st' tid tcb hE
          exact ⟨congrArg (·.runQueueOnCore c) hS, congrArg (·.currentOnCore c) hS⟩
      | error e => exact ⟨rfl, rfl⟩

-- ============================================================================
-- §11  SM6.E.5 — the cross-core cancellation flagship
-- ============================================================================

/-- WS-SM SM6.E.5 (plan §5 / §10 `cancellation_cross_core_correct`): a
cancellation executed on core `executingCore` of a victim homed on a
**different** core — and actively current there — is fully correct across the
core boundary:

1. **Remote poke** — a `.reschedule` SGI targeting the victim's home core is
   surfaced, so that core stops executing the cancelled thread;
2. **Full home-core deschedule** — the victim is neither in its home core's
   run queue nor its current slot afterwards;
3. **Per-core locality** — every *other* core's run queue and current slot
   are exactly the pre-state's (a concurrent scheduling decision on a
   sibling core observes no change to its own scheduler state);
4. **Object-level fidelity** — the object store is exactly the single-core
   `cancelIpcBlocking` teardown's (endpoint/notification dequeue, reply-link
   consume, TCB IPC-field clear), so every single-core teardown theorem
   (e.g. `cancelIpcBlocking_preserves_objects_invExt` and the
   `suspendThread_transientWindowInvariant` shape) transports to the
   cross-core composite unchanged.

Under the `cancelIpcBlocking` lock-set this whole step is 2PL-atomic
(`cancelIpcBlockingOnCore_atomic_under_lockSet`), which is what makes the
plan's "cancellation interleaves with wake" risk row (§7) unreachable: the
victim TCB write lock is held across all four effects. -/
theorem cancellation_cross_core_correct
    (victim : SeLe4n.ThreadId) (tcb tcb0 : TCB) (executingCore : CoreId)
    (st : SystemState)
    (hTcb : st.getTcb? victim = some tcb0)
    (hCur : st.scheduler.currentOnCore (determineTargetCore st victim) = some victim)
    (hRemote : determineTargetCore st victim ≠ executingCore) :
    (cancelIpcBlockingOnCore victim tcb executingCore st).2
      = some (determineTargetCore st victim, SgiKind.reschedule)
    ∧ victim ∉ (cancelIpcBlockingOnCore victim tcb executingCore st).1.scheduler.runQueueOnCore
        (determineTargetCore st victim)
    ∧ (cancelIpcBlockingOnCore victim tcb executingCore st).1.scheduler.currentOnCore
        (determineTargetCore st victim) ≠ some victim
    ∧ (∀ c', c' ≠ determineTargetCore st victim →
        (cancelIpcBlockingOnCore victim tcb executingCore st).1.scheduler.runQueueOnCore c'
            = st.scheduler.runQueueOnCore c'
        ∧ (cancelIpcBlockingOnCore victim tcb executingCore st).1.scheduler.currentOnCore c'
            = st.scheduler.currentOnCore c')
    ∧ (cancelIpcBlockingOnCore victim tcb executingCore st).1.objects
        = (cancelIpcBlocking st victim tcb).objects := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (1) remote poke
    exact cancelIpcBlockingOnCore_emits_sgi_if_remote_current victim tcb tcb0
      executingCore st hTcb hCur hRemote
  · -- (2a) not in the home run queue
    rw [cancelIpcBlockingOnCore_state_eq]
    exact removeRunnableOnCore_not_mem_self _ victim _
  · -- (2b) not the home current
    rw [cancelIpcBlockingOnCore_state_eq]
    exact removeRunnableOnCore_currentOnCore_ne_self _ victim _
  · -- (3) per-core locality: teardown is scheduler-silent, removal is
    --     home-confined
    intro c' hc'
    rw [cancelIpcBlockingOnCore_state_eq]
    have hNe : determineTargetCore st victim ≠ c' := fun h => hc' h.symm
    constructor
    · rw [removeRunnableOnCore_runQueueOnCore_ne _ victim _ c' hNe,
          cancelIpcBlocking_scheduler_eq]
    · rw [removeRunnableOnCore_currentOnCore_ne _ victim _ c' hNe,
          cancelIpcBlocking_scheduler_eq]
  · -- (4) object-level fidelity
    exact cancelIpcBlockingOnCore_objects_eq victim tcb executingCore st

end SeLe4n.Kernel
