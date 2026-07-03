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
coincidence is explicit in `cancelIpcBlockingOnCore_eq_descheduleThread` and
closed unconditionally (over `invExt`) in
`cancelIpcBlockingOnCore_eq_descheduleThread_closed`.

**TOCTOU caveat (pre-resolution vs. concurrent mutation).**  Pre-state
resolution is check-then-use: between the `determineTargetCore` read and the
home-core removal, a concurrent affinity change could in principle move the
victim.  In the sequential model this window does not exist; on hardware it
is closed *structurally*, not by luck: (1) the whole transition runs inside
the suspend syscall's 2PL bracket holding the victim's TCB **write** lock
(`lockSet_cancelIpcBlocking` ∋ `tcbLock victim`), and any affinity change
goes through `setThreadCpuAffinityOp`, whose dispatch is `.write`-gated on
the same target TCB — the lock conflict serialises the two; and (2) the
AN9-D FFI bracket (`with_interrupts_disabled` around
`suspend_thread_cross_core`) excludes same-core ISR interleavings.  The
same argument covers every pre-resolved read in this module
(`cancelDonationOnCore`'s home resolution, `suspendThreadOnCore`'s
G7-precapture).

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

-- ----------------------------------------------------------------------------
-- §2b  The donated arm across cores — replenishment migration (SM6.E.3)
-- ----------------------------------------------------------------------------
-- `returnDonatedSchedContext` re-binds the SC from the server (victim) back to
-- the original owner with object writes only.  Under the SM5.H affinity
-- discipline (`replenishQueueAffinityConsistentOnCore`) an SC's pending
-- replenishments live on its **bound thread's** home core's queue — per-core
-- ticks enqueue on the tick's core while the server runs — so a cross-core
-- donated return that merely re-binds strands the entries on the *server's*
-- home core.  The per-core donated arm therefore migrates them to the owner's
-- home core after the return (`migrateSchedContextReplenishment`, the same
-- production primitive the live `.tcbSetAffinity` path uses), restoring the
-- affinity invariant at the cancellation boundary.  Self-migration (shared
-- home core — in particular the whole single-core config) is a definitional
-- no-op, so the single-core semantics is recovered exactly
-- (`cancelDonatedDonationOnCore_eq_of_sharedHome`).

/-- Local frame (production twin of the staged SM5.H lemma): the replenishment
migration writes only replenish-queue slots — `objects` is untouched. -/
theorem migrateSchedContextReplenishment_objects_eq (st : SystemState)
    (scId : SeLe4n.SchedContextId) (fromCore toCore : CoreId) :
    (migrateSchedContextReplenishment st scId fromCore toCore).objects
      = st.objects := by
  unfold migrateSchedContextReplenishment
  split <;> rfl

/-- Local frame: the migration is the identity on the self-pair. -/
theorem migrateSchedContextReplenishment_self_eq (st : SystemState)
    (scId : SeLe4n.SchedContextId) (c : CoreId) :
    migrateSchedContextReplenishment st scId c c = st := by
  unfold migrateSchedContextReplenishment
  rw [if_pos rfl]

/-- Local frame: the migration never disturbs any core's run queue or current
slot (it writes only replenish-queue slots). -/
theorem migrateSchedContextReplenishment_runQueue_current_eq (st : SystemState)
    (scId : SeLe4n.SchedContextId) (fromCore toCore c : CoreId) :
    (migrateSchedContextReplenishment st scId fromCore toCore).scheduler.runQueueOnCore c
        = st.scheduler.runQueueOnCore c
    ∧ (migrateSchedContextReplenishment st scId fromCore toCore).scheduler.currentOnCore c
        = st.scheduler.currentOnCore c := by
  unfold migrateSchedContextReplenishment
  split
  · exact ⟨rfl, rfl⟩
  · constructor <;> simp

/-- Local frame: a core that is neither endpoint of the migration keeps its
replenish queue. -/
theorem migrateSchedContextReplenishment_replenishQueue_other_eq (st : SystemState)
    (scId : SeLe4n.SchedContextId) (fromCore toCore c : CoreId)
    (hFrom : fromCore ≠ c) (hTo : toCore ≠ c) :
    (migrateSchedContextReplenishment st scId fromCore toCore).scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
  unfold migrateSchedContextReplenishment
  split
  · rfl
  · simp [SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ _ _ _ hTo,
      SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ _ _ _ hFrom]

/-- Local (production twin of the staged SM5.H purge lemma): on a genuine
cross-core migration the source core's queue is purged of the SC. -/
theorem migrateSchedContextReplenishment_from_eq (st : SystemState)
    (scId : SeLe4n.SchedContextId) (fromCore toCore : CoreId)
    (hne : fromCore ≠ toCore) :
    (migrateSchedContextReplenishment st scId fromCore toCore).scheduler.replenishQueueOnCore fromCore
      = ReplenishQueue.remove (st.scheduler.replenishQueueOnCore fromCore) scId := by
  unfold migrateSchedContextReplenishment
  rw [if_neg hne]
  simp [SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ _ _ _
    (fun h => hne h.symm)]

/-- WS-SM SM6.E.3 (donated arm across cores): cancel a donated SchedContext
binding **and migrate its pending replenishments home**.

The R5.A `cancelDonatedDonation` return (`cleanupDonatedSchedContext` →
`returnDonatedSchedContext`, object writes only) followed by the
replenishment migration from the **victim's** home core (where per-core ticks
enqueued them while the server ran on the donated budget) to the **original
owner's** home core — the SC's post-return bound thread, whose home core the
SM5.H affinity invariant names as the entries' required residence.  The
victim's home is pre-resolved from the pre-state (the return never touches
`cpuAffinity`); the owner's home is read post-return.  Self-migration —
shared home core, and in particular every single-core configuration — is a
definitional no-op (`migrateSchedContextReplenishment_self_eq`), recovering
the single-core arm exactly (`cancelDonatedDonationOnCore_eq_of_sharedHome`).

Returns `.error .illegalState` on a non-`.donated` binding, exactly like the
single-core arm. -/
def cancelDonatedDonationOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) : Except KernelError SystemState :=
  match tcb.schedContextBinding with
  | .donated scId originalOwner =>
      match cleanupDonatedSchedContext st tid with
      | .error e => .error e
      | .ok st' =>
          .ok (migrateSchedContextReplenishment st' scId
                (determineTargetCore st tid) (determineTargetCore st' originalOwner))
  | _ => .error .illegalState

/-- WS-SM SM6.E.3: when the victim and the original owner share a home core —
in particular in every single-core configuration — the per-core donated arm
is exactly the single-core `cancelDonatedDonation` (the migration self-pair
is a definitional no-op). -/
theorem cancelDonatedDonationOnCore_eq_of_sharedHome (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (owner : SeLe4n.ThreadId)
    (hBind : tcb.schedContextBinding = .donated scId owner)
    (hHome : ∀ st', cleanupDonatedSchedContext st tid = .ok st' →
        determineTargetCore st' owner = determineTargetCore st tid) :
    cancelDonatedDonationOnCore st tid tcb = cancelDonatedDonation st tid tcb := by
  unfold cancelDonatedDonationOnCore cancelDonatedDonation
  simp only [hBind]
  cases hC : cleanupDonatedSchedContext st tid with
  | error e => rfl
  | ok st' =>
      simp only []
      rw [hHome st' hC, migrateSchedContextReplenishment_self_eq]

/-- WS-SM SM6.E.3: the per-core donated arm preserves `objects.invExt` — the
return preserves it and the migration never touches `objects`. -/
theorem cancelDonatedDonationOnCore_preserves_objects_invExt
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : st.objects.invExt)
    (h : cancelDonatedDonationOnCore st tid tcb = .ok st') :
    st'.objects.invExt := by
  unfold cancelDonatedDonationOnCore at h
  split at h
  · -- `.donated` arm.
    split at h
    · cases h
    · injection h with h
      subst h
      rw [migrateSchedContextReplenishment_objects_eq]
      exact cleanupDonatedSchedContext_preserves_objects_invExt _ _ _ hInv (by assumption)
  · cases h

/-- WS-SM SM6.E.3: the per-core donated arm never disturbs any core's run
queue or current slot (return: object writes only; migration: replenish
slots only). -/
theorem cancelDonatedDonationOnCore_runQueue_current_eq
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) (c : CoreId)
    (h : cancelDonatedDonationOnCore st tid tcb = .ok st') :
    st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c
    ∧ st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c := by
  unfold cancelDonatedDonationOnCore at h
  split at h
  · split at h
    · cases h
    · injection h with h
      subst h
      rename_i st1 hClean
      have hS := cleanupDonatedSchedContext_scheduler_eq st st1 tid hClean
      obtain ⟨hRQ, hCur⟩ := migrateSchedContextReplenishment_runQueue_current_eq
        st1 _ (determineTargetCore st tid) _ c
      constructor
      · rw [hRQ, hS]
      · rw [hCur, hS]
  · cases h

/-- WS-SM SM6.E.3 (plan §3.1): donation cancellation across cores — the R5.A
dispatcher, per-core.

Dispatches on the victim's `schedContextBinding` exactly as the single-core
`cancelDonation`: `.unbound` is a no-op, `.bound` routes to the per-core
unbind arm (replenish-queue purge on the victim's *home* core,
`determineTargetCore`), `.donated` routes to the per-core donated arm
`cancelDonatedDonationOnCore` (the R5.A return **plus** the replenishment
migration to the original owner's home core — see §2b).

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
      match cancelDonatedDonationOnCore st tid tcb with
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

/-- WS-SM SM6.E (resolution frame): the teardown never moves the victim's
home core — `cancelIpcBlocking` preserves TCB-kind and `cpuAffinity` at
every key (`cancelIpcBlocking_tcb_lookup`) and never materialises a TCB at
an unresolved key (`cancelIpcBlocking_getTcb?_none`), so
`determineTargetCore` reads the same affinity before and after. -/
theorem cancelIpcBlocking_determineTargetCore_eq
    (st : SystemState) (victim : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : st.objects.invExt) :
    determineTargetCore (cancelIpcBlocking st victim tcb) victim
      = determineTargetCore st victim := by
  cases hT : st.getTcb? victim with
  | none =>
    have hPost := cancelIpcBlocking_getTcb?_none st victim tcb hInv hT
    simp only [determineTargetCore, hPost, hT]
  | some t0 =>
    obtain ⟨t', hL', hAff'⟩ := cancelIpcBlocking_tcb_lookup st victim tcb
      victim.toObjId t0 hInv
      ((SystemState.getTcb?_eq_some_iff st victim t0).mp hT)
    have hPost : (cancelIpcBlocking st victim tcb).getTcb? victim = some t' :=
      (SystemState.getTcb?_eq_some_iff _ victim t').mpr hL'
    simp only [determineTargetCore, hPost, hT, hAff']

/-- WS-SM SM6.E (resolution frame): the teardown preserves the victim's
`getTcb?`-resolution status — a resolvable victim stays resolvable (the
IPC-field rewrites keep the TCB kind) and an unresolvable one stays
unresolvable. -/
theorem cancelIpcBlocking_getTcb?_isSome_eq
    (st : SystemState) (victim : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : st.objects.invExt) :
    ((cancelIpcBlocking st victim tcb).getTcb? victim).isSome
      = (st.getTcb? victim).isSome := by
  cases hT : st.getTcb? victim with
  | none => rw [cancelIpcBlocking_getTcb?_none st victim tcb hInv hT]
  | some t0 =>
    obtain ⟨t', hL', _⟩ := cancelIpcBlocking_tcb_lookup st victim tcb
      victim.toObjId t0 hInv
      ((SystemState.getTcb?_eq_some_iff st victim t0).mp hT)
    rw [(SystemState.getTcb?_eq_some_iff _ victim t').mpr hL']
    rfl

/-- WS-SM SM6.E (closed form): the pre-resolved cross-core cancellation
composite **is** `descheduleThread ∘ cancelIpcBlocking`, conditioned only on
the standing Robin-Hood store invariant — the two resolution-coincidence
hypotheses of `cancelIpcBlockingOnCore_eq_descheduleThread` are discharged
unconditionally by the teardown's TCB lookup frames
(`cancelIpcBlocking_tcb_lookup` / `cancelIpcBlocking_getTcb?_none`,
`Lifecycle.Invariant.SuspendPreservation`). -/
theorem cancelIpcBlockingOnCore_eq_descheduleThread_closed
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (st : SystemState) (hInv : st.objects.invExt) :
    cancelIpcBlockingOnCore victim tcb executingCore st
      = descheduleThread (cancelIpcBlocking st victim tcb) victim executingCore :=
  cancelIpcBlockingOnCore_eq_descheduleThread victim tcb executingCore st
    (cancelIpcBlocking_determineTargetCore_eq st victim tcb hInv)
    (cancelIpcBlocking_getTcb?_isSome_eq st victim tcb hInv)

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

-- The mode-aware membership helpers `mem_insertOrMerge_write_of_mem_write`
-- (`Concurrency/Locks/LockSet.lean`, next to `mem_insertOrMerge_of_mem_of_ne`)
-- and `mem_write_lockSetExtendOpt` (`Concurrency/Locks/LockSetTransitions.lean`,
-- next to `lockSetExtendOpt`) live with the generic `LockSet` algebra they
-- belong to; the coverage families below consume them.

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
      cases hE : cancelDonatedDonationOnCore st tid tcb with
      | ok st' =>
          exact cancelDonatedDonationOnCore_preserves_objects_invExt _ _ _ _ hInv hE
      | error e => exact hInv

/-- WS-SM SM6.E: the cross-core deschedule preserves `ipcInvariant` — it
never touches the object store. -/
theorem descheduleThread_preserves_ipcInvariant
    (st : SystemState) (tid : SeLe4n.ThreadId) (executingCore : CoreId)
    (hIpc : ipcInvariant st) :
    ipcInvariant (descheduleThread st tid executingCore).1 :=
  ipcInvariant_of_objects_eq (descheduleThread_objects_eq st tid executingCore) hIpc

/-- WS-SM SM6.E: the cross-core cancellation preserves `ipcInvariant` — the
object-level effect is exactly the single-core teardown's
(`cancelIpcBlocking_preserves_ipcInvariant`), including the notification
sweep's state-correcting waiter filter; the deschedule never touches
`objects`. -/
theorem cancelIpcBlockingOnCore_preserves_ipcInvariant
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (st : SystemState) (hInv : st.objects.invExt) (hIpc : ipcInvariant st) :
    ipcInvariant (cancelIpcBlockingOnCore victim tcb executingCore st).1 :=
  ipcInvariant_of_objects_eq
    (cancelIpcBlockingOnCore_objects_eq victim tcb executingCore st)
    (cancelIpcBlocking_preserves_ipcInvariant st victim tcb hInv hIpc)

/-- WS-SM SM6.E.3: `cancelBoundDonationOnCore` preserves `ipcInvariant` — the
per-core replenish-queue purge does not touch `objects`; the object writes
are the SchedContext deactivation and TCB unbind inserts, both
non-notification. -/
theorem cancelBoundDonationOnCore_preserves_ipcInvariant
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) (rqCore : CoreId)
    (hInv : st.objects.invExt) (hIpc : ipcInvariant st)
    (h : cancelBoundDonationOnCore st tid tcb rqCore = .ok st') :
    ipcInvariant st' := by
  cases hB : tcb.schedContextBinding with
  | bound scId =>
    simp only [cancelBoundDonationOnCore, hB] at h
    injection h with h
    subst h
    cases st.getSchedContext? scId with
    | none =>
      split
      · intro oid ntfn hL
        exact hIpc oid ntfn (notification_lookup_of_insert_no_notification
          _ tid.toObjId _ hInv (fun _ hEq => KernelObject.noConfusion hEq) oid ntfn hL)
      · exact ipcInvariant_of_objects_eq rfl hIpc
    | some sc =>
      have hInv1 : (st.objects.insert scId.toObjId
          (.schedContext { sc with boundThread := none, isActive := false })).invExt :=
        RobinHood.RHTable.insert_preserves_invExt _ _ _ hInv
      split
      · intro oid ntfn hL
        have hL1 := notification_lookup_of_insert_no_notification
          _ tid.toObjId _ hInv1 (fun _ hEq => KernelObject.noConfusion hEq) oid ntfn hL
        exact hIpc oid ntfn (notification_lookup_of_insert_no_notification
          _ scId.toObjId _ hInv (fun _ hEq => KernelObject.noConfusion hEq) oid ntfn hL1)
      · intro oid ntfn hL
        exact hIpc oid ntfn (notification_lookup_of_insert_no_notification
          _ scId.toObjId _ hInv (fun _ hEq => KernelObject.noConfusion hEq) oid ntfn hL)
  | unbound =>
    simp only [cancelBoundDonationOnCore, hB] at h
    cases h
  | donated _ _ =>
    simp only [cancelBoundDonationOnCore, hB] at h
    cases h

/-- WS-SM SM6.E.3: the per-core donated arm preserves `ipcInvariant` — the
return writes SchedContext/TCB objects only and the replenishment migration
never touches `objects`. -/
theorem cancelDonatedDonationOnCore_preserves_ipcInvariant
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : st.objects.invExt) (hIpc : ipcInvariant st)
    (h : cancelDonatedDonationOnCore st tid tcb = .ok st') :
    ipcInvariant st' := by
  unfold cancelDonatedDonationOnCore at h
  split at h
  · split at h
    · cases h
    · injection h with h
      subst h
      exact ipcInvariant_of_objects_eq
        (migrateSchedContextReplenishment_objects_eq _ _ _ _)
        (cleanupDonatedSchedContext_preserves_ipcInvariant _ _ _ hInv hIpc
          (by assumption))
  · cases h

/-- WS-SM SM6.E.3: the per-core donation-cancellation dispatcher preserves
`ipcInvariant` on every arm and every outcome (the error paths return the
pre-state). -/
theorem cancelDonationOnCore_preserves_ipcInvariant
    (tid : SeLe4n.ThreadId) (tcb : TCB) (st : SystemState)
    (hInv : st.objects.invExt) (hIpc : ipcInvariant st) :
    ipcInvariant (cancelDonationOnCore tid tcb st).1 := by
  unfold cancelDonationOnCore
  cases hB : tcb.schedContextBinding with
  | unbound => exact hIpc
  | bound scId =>
      cases hE : cancelBoundDonationOnCore st tid tcb (determineTargetCore st tid) with
      | ok st' =>
          exact cancelBoundDonationOnCore_preserves_ipcInvariant _ _ _ _ _ hInv hIpc hE
      | error e => exact hIpc
  | donated scId owner =>
      cases hE : cancelDonatedDonationOnCore st tid tcb with
      | ok st' =>
          exact cancelDonatedDonationOnCore_preserves_ipcInvariant _ _ _ _ hInv hIpc hE
      | error e => exact hIpc

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
      cases hE : cancelDonatedDonationOnCore st tid tcb with
      | ok st' =>
          exact cancelDonatedDonationOnCore_runQueue_current_eq st st' tid tcb c hE
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

-- ============================================================================
-- §12  SM6.E — Scheduler-domain (`SchedLockId`) lock footprints
-- ============================================================================
-- The SM3.B object-domain `LockSet` footprints (§5) cover the cancellation's
-- kernel-object writes; the scheduler-slot writes — the home core's run-queue
-- and current slots (the deschedule) and the replenish-queue slots (the
-- donation purge / migration) — live in the SM5 `SchedLockId` domain
-- (`object < runQueue < replenishQueue`, plan §4.4).  These are the
-- cancellation counterparts of SM5.C's `wakeThreadLockSet` and SM5.D's
-- `timerTickOnCoreLockSet`: declarative footprints with the standard
-- length / write-only / membership / Nodup / ascending-order lemma family,
-- consumed by the future `SchedLockId`-level `withLockSet` bracket (the
-- tracked SM5.I closure target).  Per the SM5.B convention, a core's
-- `runQueue ⟨c⟩` lock guards **all** of core `c`'s scheduler slots (run
-- queue *and* current slot — cf. `switchToThreadOnCoreLockSet`, which writes
-- the current slot under the same two-lock footprint).

/-- WS-SM SM6.E: the scheduler-domain footprint of `descheduleThread` — the
object-store table **write** lock (the `getTcb?` ghost-guard resolution and
`determineTargetCore` read ride the same table discipline as the wake's) and
the home core's run-queue **write** lock (the dequeue + current-slot clear).
Definitionally the `wakeThreadLockSet` — the deschedule is the wake's dual
and touches exactly the dual slots
(`descheduleThreadLockSet_eq_wakeThreadLockSet`). -/
def descheduleThreadLockSet (target : CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  [ (SchedLockId.object schedObjStoreLockId, .write)
  , (SchedLockId.runQueue ⟨target⟩, .write) ]

/-- WS-SM SM6.E: the deschedule footprint **is** the wake footprint — the
dual operations serialise against each other on exactly the same two locks,
which is what makes a concurrent wake/cancel race on the same victim
impossible under the `SchedLockId` bracket (the plan §7 "cancellation
interleaves with wake" risk row, scheduler-domain half). -/
theorem descheduleThreadLockSet_eq_wakeThreadLockSet (target : CoreId) :
    descheduleThreadLockSet target = wakeThreadLockSet target := rfl

/-- SM6.E: the deschedule footprint is the two-lock set. -/
@[simp] theorem descheduleThreadLockSet_length (target : CoreId) :
    (descheduleThreadLockSet target).length = 2 := rfl

/-- SM6.E: every lock in the deschedule footprint is acquired in **write**
mode. -/
theorem descheduleThreadLockSet_write_only (target : CoreId) :
    ∀ p ∈ descheduleThreadLockSet target, p.2 = Concurrency.AccessMode.write :=
  wakeThreadLockSet_write_only target

/-- SM6.E: the object-store write lock is in the deschedule footprint. -/
theorem descheduleThreadLockSet_contains_objStore_write (target : CoreId) :
    (SchedLockId.object schedObjStoreLockId, Concurrency.AccessMode.write)
      ∈ descheduleThreadLockSet target :=
  wakeThreadLockSet_contains_objStore_write target

/-- SM6.E: the home core's run-queue write lock is in the deschedule
footprint — it guards the dequeue and the current-slot clear. -/
theorem descheduleThreadLockSet_contains_runQueue_write (target : CoreId) :
    (SchedLockId.runQueue ⟨target⟩, Concurrency.AccessMode.write)
      ∈ descheduleThreadLockSet target :=
  wakeThreadLockSet_contains_runQueue_write target

/-- SM6.E: the deschedule footprint's projected keys are duplicate-free. -/
theorem descheduleThreadLockSet_keys_nodup (target : CoreId) :
    ((descheduleThreadLockSet target).map (·.1)).Nodup :=
  wakeThreadLockSet_keys_nodup target

/-- SM6.E: the deschedule footprint's keys form a `SchedLockId`-ascending
acquisition sequence. -/
theorem descheduleThreadLockSet_pairwise_le (target : CoreId) :
    ((descheduleThreadLockSet target).map (·.1)).Pairwise (· ≤ ·) :=
  wakeThreadLockSet_pairwise_le target

/-- WS-SM SM6.E: the scheduler-domain footprint of `cancelIpcBlockingOnCore`
— exactly the deschedule footprint at the victim's home core (the object
teardown's kernel-object writes are the §5 object-domain `LockSet`'s
concern; the composite's only scheduler-slot writes are the home-core
deschedule). -/
def cancelIpcBlockingOnCoreSchedLockSet (home : CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  descheduleThreadLockSet home

/-- WS-SM SM6.E: the scheduler-domain footprint of `cancelBoundDonationOnCore`
— the object-store table write lock (the SC + TCB rebinding rides the table
discipline) and the purge core's replenish-queue **write** lock. -/
def cancelBoundDonationOnCoreSchedLockSet (rqCore : CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  [ (SchedLockId.object schedObjStoreLockId, .write)
  , (SchedLockId.replenishQueue ⟨rqCore⟩, .write) ]

/-- SM6.E: the bound-arm footprint is the two-lock set. -/
@[simp] theorem cancelBoundDonationOnCoreSchedLockSet_length (rqCore : CoreId) :
    (cancelBoundDonationOnCoreSchedLockSet rqCore).length = 2 := rfl

/-- SM6.E: every lock in the bound-arm footprint is acquired in **write**
mode. -/
theorem cancelBoundDonationOnCoreSchedLockSet_write_only (rqCore : CoreId) :
    ∀ p ∈ cancelBoundDonationOnCoreSchedLockSet rqCore,
      p.2 = Concurrency.AccessMode.write := by
  intro p hp
  simp only [cancelBoundDonationOnCoreSchedLockSet, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with h | h <;> subst h <;> rfl

/-- SM6.E: the object-store write lock is in the bound-arm footprint. -/
theorem cancelBoundDonationOnCoreSchedLockSet_contains_objStore_write
    (rqCore : CoreId) :
    (SchedLockId.object schedObjStoreLockId, Concurrency.AccessMode.write)
      ∈ cancelBoundDonationOnCoreSchedLockSet rqCore := by
  simp [cancelBoundDonationOnCoreSchedLockSet]

/-- SM6.E: the purge core's replenish-queue write lock is in the bound-arm
footprint — it guards the SC-entry removal. -/
theorem cancelBoundDonationOnCoreSchedLockSet_contains_replenishQueue_write
    (rqCore : CoreId) :
    (SchedLockId.replenishQueue ⟨rqCore⟩, Concurrency.AccessMode.write)
      ∈ cancelBoundDonationOnCoreSchedLockSet rqCore := by
  simp [cancelBoundDonationOnCoreSchedLockSet]

/-- SM6.E: the bound-arm footprint's projected keys are duplicate-free. -/
theorem cancelBoundDonationOnCoreSchedLockSet_keys_nodup (rqCore : CoreId) :
    ((cancelBoundDonationOnCoreSchedLockSet rqCore).map (·.1)).Nodup := by
  simp [cancelBoundDonationOnCoreSchedLockSet]

/-- SM6.E: the bound-arm footprint's keys form a `SchedLockId`-ascending
acquisition sequence (object < replenishQueue, plan §4.4). -/
theorem cancelBoundDonationOnCoreSchedLockSet_pairwise_le (rqCore : CoreId) :
    ((cancelBoundDonationOnCoreSchedLockSet rqCore).map (·.1)).Pairwise (· ≤ ·) := by
  have hle : SchedLockId.object schedObjStoreLockId
      ≤ SchedLockId.replenishQueue (⟨rqCore⟩ : ReplenishQueueLockId) :=
    (SchedLockId.object_lt_replenishQueue _ _).1
  simp only [cancelBoundDonationOnCoreSchedLockSet, List.map_cons, List.map_nil]
  exact List.Pairwise.cons
    (fun a ha => by rcases List.mem_singleton.mp ha with rfl; exact hle)
    (List.Pairwise.cons (fun a ha => by simp at ha) List.Pairwise.nil)

/-- WS-SM SM6.E: the scheduler-domain footprint of the per-core **donated**
arm `cancelDonatedDonationOnCore` — the object-store table write lock plus
the replenish-queue write locks of **both** migration endpoints (the
victim's home core, purged, and the original owner's home core, receiving),
emitted in `CoreId`-ascending order so the list is itself the canonical
acquisition sequence.  On a shared home core the two endpoints coincide and
the footprint collapses to the bound-arm shape. -/
def cancelDonatedDonationOnCoreSchedLockSet (victimHome ownerHome : CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  (SchedLockId.object schedObjStoreLockId, .write) ::
    (if victimHome = ownerHome then
      [ (SchedLockId.replenishQueue ⟨victimHome⟩, .write) ]
    else if victimHome ≤ ownerHome then
      [ (SchedLockId.replenishQueue ⟨victimHome⟩, .write)
      , (SchedLockId.replenishQueue ⟨ownerHome⟩, .write) ]
    else
      [ (SchedLockId.replenishQueue ⟨ownerHome⟩, .write)
      , (SchedLockId.replenishQueue ⟨victimHome⟩, .write) ])

/-- SM6.E: every lock in the donated-arm footprint is acquired in **write**
mode. -/
theorem cancelDonatedDonationOnCoreSchedLockSet_write_only
    (victimHome ownerHome : CoreId) :
    ∀ p ∈ cancelDonatedDonationOnCoreSchedLockSet victimHome ownerHome,
      p.2 = Concurrency.AccessMode.write := by
  intro p hp
  simp only [cancelDonatedDonationOnCoreSchedLockSet, List.mem_cons] at hp
  rcases hp with h | hp
  · subst h; rfl
  · split at hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp; rfl
    · split at hp <;>
        (simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
         rcases hp with h | h <;> subst h <;> rfl)

/-- SM6.E: the victim's home-core replenish-queue write lock is in the
donated-arm footprint (the migration source / purge slot). -/
theorem cancelDonatedDonationOnCoreSchedLockSet_contains_victimHome_write
    (victimHome ownerHome : CoreId) :
    (SchedLockId.replenishQueue ⟨victimHome⟩, Concurrency.AccessMode.write)
      ∈ cancelDonatedDonationOnCoreSchedLockSet victimHome ownerHome := by
  unfold cancelDonatedDonationOnCoreSchedLockSet
  by_cases hEq : victimHome = ownerHome
  · simp [hEq]
  · by_cases hLe : victimHome ≤ ownerHome <;> simp [hEq, hLe]

/-- SM6.E: the owner's home-core replenish-queue write lock is in the
donated-arm footprint (the migration destination). -/
theorem cancelDonatedDonationOnCoreSchedLockSet_contains_ownerHome_write
    (victimHome ownerHome : CoreId) :
    (SchedLockId.replenishQueue ⟨ownerHome⟩, Concurrency.AccessMode.write)
      ∈ cancelDonatedDonationOnCoreSchedLockSet victimHome ownerHome := by
  unfold cancelDonatedDonationOnCoreSchedLockSet
  by_cases hEq : victimHome = ownerHome
  · simp [hEq]
  · by_cases hLe : victimHome ≤ ownerHome <;> simp [hEq, hLe]

/-- SM6.E: the donated-arm footprint's projected keys are duplicate-free —
the two replenish endpoints are distinct locks exactly when the homes
differ, and the shared-home branch carries the slot once. -/
theorem cancelDonatedDonationOnCoreSchedLockSet_keys_nodup
    (victimHome ownerHome : CoreId) :
    ((cancelDonatedDonationOnCoreSchedLockSet victimHome ownerHome).map (·.1)).Nodup := by
  unfold cancelDonatedDonationOnCoreSchedLockSet
  by_cases hEq : victimHome = ownerHome
  · subst hEq
    simp
  · by_cases hLe : victimHome ≤ ownerHome
    · simp only [hEq, hLe, if_true, if_false, List.map_cons, List.map_nil]
      refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩⟩⟩
      · intro h
        rcases List.mem_cons.mp h with h | h
        · cases h
        · rcases List.mem_singleton.mp h with h; cases h
      · intro h
        have h' := List.mem_singleton.mp h
        injection h' with h''
        exact hEq (congrArg ReplenishQueueLockId.core h'')
    · simp only [hEq, hLe, if_false, List.map_cons, List.map_nil]
      refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩⟩⟩
      · intro h
        rcases List.mem_cons.mp h with h | h
        · cases h
        · rcases List.mem_singleton.mp h with h; cases h
      · intro h
        have h' := List.mem_singleton.mp h
        injection h' with h''
        exact hEq (congrArg ReplenishQueueLockId.core h'').symm

/-- SM6.E: the donated-arm footprint's keys form a `SchedLockId`-ascending
acquisition sequence — object < replenishQueue cross-domain, and the two
replenish endpoints are emitted in `CoreId`-ascending order. -/
theorem cancelDonatedDonationOnCoreSchedLockSet_pairwise_le
    (victimHome ownerHome : CoreId) :
    ((cancelDonatedDonationOnCoreSchedLockSet victimHome ownerHome).map (·.1)).Pairwise (· ≤ ·) := by
  have hObjLe : ∀ (c : CoreId), SchedLockId.object schedObjStoreLockId
      ≤ SchedLockId.replenishQueue (⟨c⟩ : ReplenishQueueLockId) :=
    fun c => (SchedLockId.object_lt_replenishQueue _ _).1
  unfold cancelDonatedDonationOnCoreSchedLockSet
  by_cases hEq : victimHome = ownerHome
  · subst hEq
    simp only [List.map_cons]
    exact List.Pairwise.cons
      (fun a ha => by rcases List.mem_singleton.mp ha with rfl; exact hObjLe _)
      (List.Pairwise.cons (fun a ha => by simp at ha) List.Pairwise.nil)
  · by_cases hLe : victimHome ≤ ownerHome
    · simp only [hEq, hLe, if_true, if_false, List.map_cons, List.map_nil]
      refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_
        (List.Pairwise.cons (fun a ha => by simp at ha) List.Pairwise.nil))
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hObjLe _
        · rcases List.mem_singleton.mp ha with rfl; exact hObjLe _
      · intro a ha
        rcases List.mem_singleton.mp ha with rfl
        exact hLe
    · simp only [hEq, hLe, if_false, List.map_cons, List.map_nil]
      have hGe : ownerHome ≤ victimHome :=
        (Nat.le_total victimHome.val ownerHome.val).resolve_left hLe
      refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_
        (List.Pairwise.cons (fun a ha => by simp at ha) List.Pairwise.nil))
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hObjLe _
        · rcases List.mem_singleton.mp ha with rfl; exact hObjLe _
      · intro a ha
        rcases List.mem_singleton.mp ha with rfl
        exact hGe

/-- WS-SM SM6.E: the scheduler-domain footprint of the donation-cancellation
**dispatcher** `cancelDonationOnCore` — the union over its arms: the
`.unbound` arm touches no scheduler slot, the `.bound` arm purges the
victim's home-core replenish queue (the `victimHome` member), and the
`.donated` arm additionally writes the owner's home-core queue (the
migration destination).  The donated-arm footprint is exactly that union. -/
def cancelDonationOnCoreSchedLockSet (victimHome ownerHome : CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  cancelDonatedDonationOnCoreSchedLockSet victimHome ownerHome

/-- WS-SM SM6.E (PR #831 review 3): a `CoreId`-ascending sorted pair of
same-kind scheduler locks — the shared shape of the suspend footprint's
run-queue and replenish-queue segments (one entry when the cores coincide,
two in `CoreId`-ascending order otherwise). -/
def sortedSchedCorePair (f : CoreId → SchedLockId) (a b : CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  if a = b then [ (f a, .write) ]
  else if a ≤ b then [ (f a, .write), (f b, .write) ]
  else [ (f b, .write), (f a, .write) ]

/-- Every key of a sorted pair is one of the two endpoints. -/
theorem sortedSchedCorePair_map_fst_mem {f : CoreId → SchedLockId}
    {a b : CoreId} {x : SchedLockId}
    (hx : x ∈ (sortedSchedCorePair f a b).map (·.1)) : x = f a ∨ x = f b := by
  unfold sortedSchedCorePair at hx
  split at hx
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hx
    exact Or.inl hx
  · split at hx
    · simp only [List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      exact hx
    · simp only [List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      exact hx.symm

/-- A sorted pair's keys ascend under any `CoreId`-monotone lock constructor. -/
theorem sortedSchedCorePair_pairwise_le (f : CoreId → SchedLockId) (a b : CoreId)
    (hMono : ∀ c d : CoreId, c ≤ d → f c ≤ f d) :
    ((sortedSchedCorePair f a b).map (·.1)).Pairwise (· ≤ ·) := by
  unfold sortedSchedCorePair
  split
  · simp
  · split
    · rename_i hne hle
      simp only [List.map_cons, List.map_nil]
      exact List.Pairwise.cons
        (fun x hx => by rcases List.mem_singleton.mp hx with rfl; exact hMono _ _ hle)
        (List.Pairwise.cons (fun x hx => by simp at hx) List.Pairwise.nil)
    · rename_i hne hnle
      have hge : b ≤ a := (Nat.le_total a.val b.val).resolve_left hnle
      simp only [List.map_cons, List.map_nil]
      exact List.Pairwise.cons
        (fun x hx => by rcases List.mem_singleton.mp hx with rfl; exact hMono _ _ hge)
        (List.Pairwise.cons (fun x hx => by simp at hx) List.Pairwise.nil)

/-- WS-SM SM6.E: the scheduler-domain footprint of the cross-core suspend
pipeline (`suspendThreadOnCore`, the G2..G7 composite): the object-store
table write lock, the **run-queue** write locks of the victim's home core
(the G4 deschedule + G7 current handling) AND the executing core (the G7
local-disinheritance preemption gate `handleRescheduleSgiOnCore` may
switch/re-enqueue under the executing core's queue when the G2b PIP revert
deboosted its current thread — PR #831 review 3; one entry when
`home = executingCore`), and the replenish-queue write locks of the donation
arms (victim home = purge/migration source, owner home = the migration
destination), in the plan §4.4 cross-domain ascending order
`object < runQueue < replenishQueue` with each same-kind segment in
`CoreId`-ascending order.

**Dynamic chain extension (declared, not static — PR #831 review 3).**  The
G2b PIP revert (`propagatePipChainCrossCore` from the captured blocking
server) re-buckets each chain member's run queue on **that member's** home
core (`updatePipBoostOnCore`).  The chain is state-discovered, so no static
footprint can enumerate those cores — exactly the SM3.C.11 argument for the
chain members' TCB locks.  The obligation is declared by
`pipChainStart_tcbSuspend` (SM3.B.3): the SM3.C.11 walker must acquire, per
chain step, the member's TCB **write** lock *and* its home-core
`SchedLockId.runQueue` **write** lock together (see the amended SM3.C
consumer contract in `LockSetTransitions.lean`).  The same declaration
covers the `.call`/`.reply`/`.replyRecv` walks, which run the identical
`updatePipBoostOnCore` re-bucketing. -/
def suspendThreadOnCoreSchedLockSet (home executingCore ownerHome : CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  (SchedLockId.object schedObjStoreLockId, .write) ::
  (sortedSchedCorePair (fun c => SchedLockId.runQueue ⟨c⟩) home executingCore
    ++ sortedSchedCorePair (fun c => SchedLockId.replenishQueue ⟨c⟩) home ownerHome)

/-- SM6.E: the suspend footprint's keys form a `SchedLockId`-ascending
acquisition sequence — the full three-domain ladder
`object < runQueue < replenishQueue` with each same-kind segment's endpoints
in `CoreId`-ascending order. -/
theorem suspendThreadOnCoreSchedLockSet_pairwise_le
    (home executingCore ownerHome : CoreId) :
    ((suspendThreadOnCoreSchedLockSet home executingCore ownerHome).map (·.1)).Pairwise
      (· ≤ ·) := by
  have hObjRQ : ∀ (c : CoreId), SchedLockId.object schedObjStoreLockId
      ≤ SchedLockId.runQueue (⟨c⟩ : RunQueueLockId) :=
    fun c => (SchedLockId.object_lt_runQueue _ _).1
  have hObjRep : ∀ (c : CoreId), SchedLockId.object schedObjStoreLockId
      ≤ SchedLockId.replenishQueue (⟨c⟩ : ReplenishQueueLockId) :=
    fun c => (SchedLockId.object_lt_replenishQueue _ _).1
  have hRQRep : ∀ (c d : CoreId), SchedLockId.runQueue (⟨c⟩ : RunQueueLockId)
      ≤ SchedLockId.replenishQueue (⟨d⟩ : ReplenishQueueLockId) :=
    fun c d => (SchedLockId.runQueue_lt_replenishQueue _ _).1
  unfold suspendThreadOnCoreSchedLockSet
  rw [List.map_cons, List.map_append, List.pairwise_cons]
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases sortedSchedCorePair_map_fst_mem hx with rfl | rfl <;> exact hObjRQ _
    · rcases sortedSchedCorePair_map_fst_mem hx with rfl | rfl <;> exact hObjRep _
  · rw [List.pairwise_append]
    refine ⟨sortedSchedCorePair_pairwise_le _ _ _ (fun c d h => h),
      sortedSchedCorePair_pairwise_le _ _ _ (fun c d h => h), ?_⟩
    intro x hx y hy
    rcases sortedSchedCorePair_map_fst_mem hx with rfl | rfl <;>
    rcases sortedSchedCorePair_map_fst_mem hy with rfl | rfl <;> exact hRQRep _ _

-- ============================================================================
-- §13  SM6.E — the live per-core suspend (the `.tcbSuspend` dispatch target)
-- ============================================================================

namespace Lifecycle.Suspend

/-- WS-SM SM6.E: the per-core suspend's **G7 dispatch** — the local/remote
reschedule seam factored out of `suspendThreadOnCore` so the SGI discipline is
provable arm-by-arm.  Four arms:

* victim was current on a **local** home (`wasCurrentHome ∧ home = ec`):
  reschedule inline, surface nothing;
* victim was current on a **remote** home: surface the home-core
  `.reschedule` SGI — running the local preemption gate first iff the G2b
  PIP revert deboosted the executing core's own current thread
  (`localDeboosted`, PR #831 review 2);
* victim not current anywhere relevant: surface nothing — but still run the
  local preemption gate on a local disinheritance. -/
def suspendRescheduleOnCore (st : SystemState) (home executingCore : CoreId)
    (wasCurrentHome localDeboosted : Bool)
    : Except KernelError (SystemState × Option (CoreId × SgiKind)) :=
  if wasCurrentHome then
    if home == executingCore then
      match handleRescheduleSgiOnCore st executingCore with
      | .ok st' => .ok (st', none)
      | .error e => .error e
    else
      if localDeboosted then
        match handleRescheduleSgiOnCore st executingCore with
        | .ok st' => .ok (st', some (home, SgiKind.reschedule))
        | .error e => .error e
      else
        .ok (st, some (home, SgiKind.reschedule))
  else
    if localDeboosted then
      match handleRescheduleSgiOnCore st executingCore with
      | .ok st' => .ok (st', none)
      | .error e => .error e
    else
      .ok (st, none)

/-- WS-SM SM6.E (SGI discipline, G7-dispatch level): every SGI the dispatch
surfaces is a `.reschedule` targeting `home`, and only when `home` is remote. -/
theorem suspendRescheduleOnCore_sgi_shape (st st' : SystemState)
    (home ec : CoreId) (wc ld : Bool) (c : CoreId) (k : SgiKind)
    (h : suspendRescheduleOnCore st home ec wc ld = .ok (st', some (c, k))) :
    c = home ∧ k = SgiKind.reschedule ∧ home ≠ ec := by
  unfold suspendRescheduleOnCore at h
  split at h
  · split at h
    · split at h
      · injection h with h; injection h with h1 h2; cases h2
      · cases h
    · rename_i hNotLocal
      have hne : home ≠ ec := fun hEq => hNotLocal (by simp [hEq])
      split at h
      · split at h
        · injection h with h; injection h with h1 h2
          injection h2 with h2; injection h2 with hc hk
          exact ⟨hc.symm, hk.symm, hne⟩
        · cases h
      · injection h with h; injection h with h1 h2
        injection h2 with h2; injection h2 with hc hk
        exact ⟨hc.symm, hk.symm, hne⟩
  · split at h
    · split at h
      · injection h with h; injection h with h1 h2; cases h2
      · cases h
    · injection h with h; injection h with h1 h2; cases h2

/-- WS-SM SM6.E (G7-dispatch level): a local home surfaces no SGI. -/
theorem suspendRescheduleOnCore_local_no_sgi (st st' : SystemState)
    (home ec : CoreId) (wc ld : Bool) (sgi : Option (CoreId × SgiKind))
    (hLocal : home = ec)
    (h : suspendRescheduleOnCore st home ec wc ld = .ok (st', sgi)) :
    sgi = none := by
  unfold suspendRescheduleOnCore at h
  split at h
  · split at h
    · split at h
      · injection h with h; injection h with h1 h2; exact h2.symm
      · cases h
    · rename_i hNotLocal
      exact absurd (by simp [hLocal]) hNotLocal
  · split at h
    · split at h
      · injection h with h; injection h with h1 h2; exact h2.symm
      · cases h
    · injection h with h; injection h with h1 h2; exact h2.symm

/-- WS-SM SM6.E (live wiring): the **complete** per-core suspend — the
cross-core analogue of `suspendThread`, exactly as `resumeThreadOnCore`
(SM5.F.6) is the cross-core analogue of `resumeThread`.

The single-core G1–G7 pipeline generalised across cores:

* **G1** — TCB lookup + `.Inactive` rejection (unchanged).
* **G7-precapture** — whether the victim is actively current is read on its
  **home** core (`determineTargetCore`, pre-state resolution per the SM3.B
  discipline) instead of the boot core.
* **G2 (IPC teardown) + G2b (per-core PIP revert)** — the upstream blocking
  server is captured BEFORE `cancelIpcBlocking` clears the victim's
  `ipcState` (the D4-N capture → clear → revert-from-server order
  `timeoutThread` uses; see the `suspendThread` ordering-fix note), and the
  revert then walks the chain from that server on the post-teardown state —
  `waitersOf` no longer includes the victim, so each chain member's
  `pipBoost` genuinely drops the victim's donation.  Per-core: the walk is
  the SM5.F.4 `propagatePipChainCrossCore` (functionally revert-capable —
  `revert_eq_propagate`'s recompute-from-current-`waitersOf` argument),
  which migrates each chain member's run-queue bucket on **its** home core
  via `updatePipBoostOnCore` — not the boot-pinned `updatePipBoost` — and
  the cross-core `.reschedule` pokes the re-bucketing warrants are
  re-derived by the diff seam (`computeCrossCoreSgis`, fired by both
  `.tcbSuspend` entry paths).
* **G3 (donation)** — dispatches to the **per-core** arms:
  `cancelBoundDonationOnCore` purges the replenish queue of the victim's
  *home* core (the SM5.H affinity discipline) and
  `cancelDonatedDonationOnCore` migrates the returned SchedContext's
  replenishments to the original owner's home core (§2b).
* **G4** — `removeRunnableOnCore` on the victim's **home** core.  The
  single-core form's bootCore-pinned `removeRunnable` left a remote victim
  queued/current on its home core — the multi-core correctness gap this
  wiring closes.
* **G5/G6** — pending-state clear + `.Inactive` write (unchanged).
* **G7 (reschedule)** — mirrors `resumeThreadOnCore`'s H5 local/remote seam:
  * **LOCAL** (home = `executingCore`): the executing core suspended its own
    current thread — run the per-core reschedule handler inline
    (`handleRescheduleSgiOnCore`; the current slot was just vacated, so the
    preemption gate passes unconditionally and the successor is dispatched,
    or the core stays idle when its queue is empty).
  * **REMOTE** (home ≠ `executingCore`): return the `.reschedule` SGI the
    home core must receive so it stops executing the suspended thread — the
    same SGI the diff seam re-derives (`crossCoreSgiBody`'s SM6.E
    descheduled-current rule) on the generic syscall path.
  * **LOCAL DISINHERITANCE** (PR #831 review 2): independent of the victim's
    placement, if the G2b PIP revert lowered the **executing core's own
    current thread's** effective priority (the executing core may be running
    a chain member — e.g. the victim's server), G7 also runs the local
    preemption gate (`handleRescheduleSgiOnCore`): a ready local thread whose
    priority sits between the server's base and its old donation must
    preempt now, not at the next timer tick.  No SGI can deliver this — the
    diff seam pokes only remote cores (its still-current companion rule
    `crossCoreSgiBody_remote_deboost_current` covers the *remote* deboosted
    server).  A priority raise triggers nothing (the running choice can only
    outrank strictly more).

Errors mirror `suspendThread`: `invalidArgument` for a non-TCB target,
`illegalState` for an already-`.Inactive` one, and the G3 donation-arm
errors propagate. -/
def suspendThreadOnCore (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (executingCore : CoreId)
    : Except KernelError (SystemState × Option (CoreId × SgiKind)) :=
  let tid : SeLe4n.ThreadId := vtid.val
  -- AK7-clean: every TCB read goes through the typed `getTcb?` accessor
  -- (unlike the single-core `suspendThread`'s raw G1/G6 lookups —
  -- `resumeThreadOnCore`'s reader discipline, mirrored).
  match st.getTcb? tid with
  | some tcb =>
    if tcb.threadState == .Inactive then .error .illegalState
    else
      -- home core of the victim (pre-state resolution; the teardown never
      -- moves it — `cancelIpcBlocking_determineTargetCore_eq`)
      let home := determineTargetCore st tid
      let wasCurrentHome : Bool := (st.scheduler.currentOnCore home) == some tid
      -- Local-disinheritance precapture (PR #831 review 2): the executing
      -- core's current thread's entry-time effective priority.  G2b's PIP
      -- revert can LOWER it (the current thread may be a chain member — e.g.
      -- the executing core is running the victim's server), and a
      -- deboosted-but-still-current thread receives no SGI (the diff seam
      -- pokes only *remote* cores), so the drop is re-checked at G7 and a
      -- LOCAL scheduling point is run.
      let execCurPre := currentEffectivePrio? st executingCore
      -- G2-precapture (D4-N, SM6.E ordering fix — see `suspendThread`): the
      -- reply-blocking edge is read before G2 clears it.
      let maybeBlockingServer := PriorityInheritance.blockingServer st tid
      let st := cancelIpcBlockingValid st vtid tcb
      -- G2b (D4-N × SM5.F.4): revert the PIP chain from the captured server
      -- on the post-teardown state, migrating each chain member's run-queue
      -- bucket on its OWN home core (the boot-pinned `revertPriorityInheritance`
      -- migrated only the boot queue — the SM5.F per-core-PIP-migration gap).
      let st := match maybeBlockingServer with
        | some serverId =>
          (PriorityInheritance.propagatePipChainCrossCore st serverId executingCore).1
        | none => st
      let tcb' := (st.getTcb? tid).getD tcb
      match (match tcb'.schedContextBinding with
             | .unbound => (Except.ok st : Except KernelError SystemState)
             | .bound _ => cancelBoundDonationOnCore st tid tcb' home
             | .donated _ _ => cancelDonatedDonationOnCore st tid tcb') with
      | .error e => .error e
      | .ok st =>
      let st := removeRunnableOnCore st tid home
      let st := clearPendingStateValid st vtid
      let st := match st.getTcb? tid with
        | some tcb'' =>
          { st with objects := st.objects.insert tid.toObjId (.tcb { tcb'' with
              threadState := .Inactive }) }
        | none => st
      -- Local-disinheritance recheck (PR #831 review 2): the executing core's
      -- entry-time current thread is STILL current and its effective priority
      -- dropped across the pipeline (the G2b revert deboosted it) — a ready
      -- local thread may now outrank the running choice, and no SGI ever
      -- reaches the executing core, so G7 must run the local preemption gate.
      suspendRescheduleOnCore st home executingCore wasCurrentHome
        (currentDeboostedFrom st executingCore execCurPre)
  | none => .error .invalidArgument

/-- WS-SM SM6.E: a target that does not resolve to a TCB is rejected with
`invalidArgument`, exactly as `suspendThread`. -/
theorem suspendThreadOnCore_rejects_absent (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) (ec : CoreId)
    (hGet : st.getTcb? vtid.val = none) :
    suspendThreadOnCore st vtid ec = .error .invalidArgument := by
  simp only [suspendThreadOnCore, hGet]

/-- WS-SM SM6.E: an already-`.Inactive` victim is rejected with
`illegalState`, exactly as `suspendThread`. -/
theorem suspendThreadOnCore_rejects_inactive (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) (ec : CoreId) (tcb : TCB)
    (hGet : st.getTcb? vtid.val = some tcb)
    (hInactive : tcb.threadState = .Inactive) :
    suspendThreadOnCore st vtid ec = .error .illegalState := by
  simp only [suspendThreadOnCore, hGet, hInactive, beq_self_eq_true, if_true]

/-- WS-SM SM6.E (SGI discipline): every SGI the per-core suspend surfaces is
a `.reschedule` targeting the victim's **home** core, emitted only when that
home is **remote** (home ≠ `executingCore`) — the local case reschedules
inline and surfaces nothing. -/
theorem suspendThreadOnCore_sgi_remote_reschedule (st st' : SystemState)
    (vtid : SeLe4n.ValidThreadId) (ec : CoreId) (c : CoreId) (k : SgiKind)
    (h : suspendThreadOnCore st vtid ec = .ok (st', some (c, k))) :
    c = determineTargetCore st vtid.val ∧ k = SgiKind.reschedule ∧ c ≠ ec := by
  simp only [suspendThreadOnCore] at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · obtain ⟨hc, hk, hne⟩ := suspendRescheduleOnCore_sgi_shape _ _ _ _ _ _ _ _ h
        exact ⟨hc, hk, hc ▸ hne⟩
  · cases h

/-- WS-SM SM6.E: a victim homed on the executing core surfaces no SGI — the
reschedule (when needed) happened inline. -/
theorem suspendThreadOnCore_local_no_sgi (st st' : SystemState)
    (vtid : SeLe4n.ValidThreadId) (ec : CoreId) (sgi : Option (CoreId × SgiKind))
    (hLocal : determineTargetCore st vtid.val = ec)
    (h : suspendThreadOnCore st vtid ec = .ok (st', sgi)) :
    sgi = none := by
  simp only [suspendThreadOnCore] at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · exact suspendRescheduleOnCore_local_no_sgi _ _ _ _ _ _ _ hLocal h
  · cases h

end Lifecycle.Suspend

-- ============================================================================
-- §14  SM6.E — observational atomicity of the cancellation (SM3.C.7 guarded)
-- ============================================================================
-- The §8/§9 atomicity theorems record the 2PL 3-phase shape structurally;
-- this section gives the *observational* content for the cancellation's
-- decisive business observable: the victim's `ipcState`.  Lock acquire /
-- release write only per-object `lock` fields (`updateObjectLockAt`), so an
-- `ipcState` observer — guarded by the store invariant `invExt`, which the
-- lock writes preserve — sees exactly the cancellation's own transition
-- through the whole `withLockSet` bracket, never a lock-machinery
-- intermediate (`lockSet_observer_atomic_on`, the SM3.C.7 guarded capstone).

/-- WS-SM SM6.E: acquiring a per-object lock preserves the store invariant —
its only store write is an `updateObjectAt` insert. -/
theorem acquireLockOnObject_preserves_objects_invExt (s : SystemState)
    (core : CoreId) (l : LockId) (m : Concurrency.AccessMode)
    (h : s.objects.invExt) :
    (acquireLockOnObject s core l m).objects.invExt := by
  unfold acquireLockOnObject
  split
  all_goals first
    | exact h
    | (unfold updateObjectLockAt
       split
       · unfold updateObjectAt
         split
         · exact RobinHood.RHTable.insert_preserves_invExt _ _ _ h
         · exact h
       · exact h)

/-- WS-SM SM6.E: releasing a per-object lock preserves the store invariant. -/
theorem releaseLockOnObject_preserves_objects_invExt (s : SystemState)
    (core : CoreId) (l : LockId) (m : Concurrency.AccessMode)
    (h : s.objects.invExt) :
    (releaseLockOnObject s core l m).objects.invExt := by
  unfold releaseLockOnObject
  split
  all_goals first
    | exact h
    | (unfold updateObjectLockAt
       split
       · unfold updateObjectAt
         split
         · exact RobinHood.RHTable.insert_preserves_invExt _ _ _ h
         · exact h
       · exact h)

/-- WS-SM SM6.E: a lock-only object write is invisible to the victim's
`ipcState` observer — `updateObjectLockAt` rewrites only the stored object's
`lock` field, preserving every business field and every other key. -/
theorem updateObjectLockAt_getTcb?_ipcState (s : SystemState) (l : LockId)
    (op : Concurrency.RwLockOp) (tid : SeLe4n.ThreadId)
    (hExt : s.objects.invExt) :
    ((updateObjectLockAt s l op).getTcb? tid).map TCB.ipcState
      = (s.getTcb? tid).map TCB.ipcState := by
  unfold updateObjectLockAt
  split
  · unfold updateObjectAt
    cases hg : s.objects.get? l.objId with
    | none => rfl
    | some obj =>
      simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
      by_cases hk : (l.objId == tid.toObjId) = true
      · have hk' : l.objId = tid.toObjId := eq_of_beq hk
        rw [← hk',
            SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self
              s.objects l.objId _ hExt,
            hg]
        cases obj <;> rfl
      · rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne
              s.objects l.objId tid.toObjId _ hk hExt]
  · rfl

/-- WS-SM SM6.E: the cancellation's decisive business observable — the
victim's `ipcState` (the field the teardown transitions and the wake/suspend
race would corrupt). -/
def cancellationVictimIpcStateObserver (victim : SeLe4n.ThreadId) :=
  fun s : SystemState => (s.getTcb? victim).map TCB.ipcState

/-- WS-SM SM6.E: the victim-`ipcState` observer is `invExt`-guardedly
acquire-insensitive — every lock acquire is a lock-field-only write. -/
theorem cancellationObserver_acquireInsensitiveOn (core : CoreId)
    (victim : SeLe4n.ThreadId) :
    AcquireInsensitiveOn (fun s => s.objects.invExt) core
      (cancellationVictimIpcStateObserver victim) := by
  intro s l m hExt
  show ((acquireLockOnObject s core l m).getTcb? victim).map TCB.ipcState
    = (s.getTcb? victim).map TCB.ipcState
  unfold acquireLockOnObject
  split
  all_goals first
    | rfl
    | exact updateObjectLockAt_getTcb?_ipcState s l _ victim hExt

/-- WS-SM SM6.E: the victim-`ipcState` observer is `invExt`-guardedly
release-insensitive. -/
theorem cancellationObserver_releaseInsensitiveOn (core : CoreId)
    (victim : SeLe4n.ThreadId) :
    ReleaseInsensitiveOn (fun s => s.objects.invExt) core
      (cancellationVictimIpcStateObserver victim) := by
  intro s l m hExt
  show ((releaseLockOnObject s core l m).getTcb? victim).map TCB.ipcState
    = (s.getTcb? victim).map TCB.ipcState
  unfold releaseLockOnObject
  split
  all_goals first
    | rfl
    | exact updateObjectLockAt_getTcb?_ipcState s l _ victim hExt

/-- WS-SM SM6.E (observational atomicity, plan §5.3 for the cancellation):
under the cancellation's declared 2PL lock-set the victim-`ipcState`
observer sees exactly the cancellation transition — the acquire fold shows
it the pre-state view and the release fold is invisible; no lock-machinery
intermediate is ever observable.  Instantiates the SM3.C.7 guarded capstone
(`lockSet_observer_atomic_on`) at the `invExt` guard, discharged by the lock
primitives' own store-invariant stability and the cancellation's `invExt`
preservation. -/
theorem cancelIpcBlockingOnCore_observer_atomic
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (blEp blN : Option SeLe4n.ObjId) (consumedReplyId : Option SeLe4n.ReplyId)
    (s : SystemState) (hInv : s.objects.invExt) :
    cancellationVictimIpcStateObserver victim
        (acquireAll executingCore
          (lockSet_cancelIpcBlocking victim blEp blN
            consumedReplyId).lockAcquireSequence s)
      = cancellationVictimIpcStateObserver victim s
    ∧ cancellationVictimIpcStateObserver victim
        (withLockSet (lockSet_cancelIpcBlocking victim blEp blN consumedReplyId)
          executingCore (cancelIpcBlockingOnCore victim tcb executingCore) s).1
      = cancellationVictimIpcStateObserver victim
          (cancelIpcBlockingOnCore victim tcb executingCore
            (acquireAll executingCore
              (lockSet_cancelIpcBlocking victim blEp blN
                consumedReplyId).lockAcquireSequence s)).1 := by
  have hAcqStable : ∀ (s' : SystemState) l m, s'.objects.invExt →
      (acquireLockOnObject s' executingCore l m).objects.invExt :=
    fun s' l m h => acquireLockOnObject_preserves_objects_invExt s' executingCore l m h
  have hInvAcq : (acquireAll executingCore
      (lockSet_cancelIpcBlocking victim blEp blN
        consumedReplyId).lockAcquireSequence s).objects.invExt :=
    (acquireAll_lockInsensitiveOn _ executingCore _
      (cancellationObserver_acquireInsensitiveOn executingCore victim) hAcqStable
      _ s hInv).2
  exact lockSet_observer_atomic_on _ executingCore _ s
    (fun st => st.objects.invExt)
    (cancellationVictimIpcStateObserver victim)
    (cancellationObserver_acquireInsensitiveOn executingCore victim)
    (cancellationObserver_releaseInsensitiveOn executingCore victim)
    hAcqStable
    (fun s' l m h => releaseLockOnObject_preserves_objects_invExt s' executingCore l m h)
    hInv
    (cancelIpcBlockingOnCore_preserves_objects_invExt victim tcb executingCore _ hInvAcq)

-- ============================================================================
-- §15  SM6.E — boot-instance bridges + placement/affinity corollaries
-- ============================================================================

/-- WS-SM SM6.E: at a bootCore-homed victim (in particular every single-core
configuration) the cross-core cancellation's state is exactly the boot-pinned
`removeRunnable` over the single-core teardown. -/
theorem cancelIpcBlockingOnCore_bootHome_state_eq
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (st : SystemState)
    (hHome : determineTargetCore st victim = bootCoreId) :
    (cancelIpcBlockingOnCore victim tcb executingCore st).1
      = removeRunnable (cancelIpcBlocking st victim tcb) victim := by
  rw [cancelIpcBlockingOnCore_state_eq, hHome, removeRunnableOnCore_bootCoreId]

/-- WS-SM SM6.E (placement corollary): under the run-queue placement
discipline — the victim is queued/current only on its home core — the
deschedule removes it from **every** core: the home core by the removal, and
every other core vacuously by the pre-state placement plus the per-core
locality frames. -/
theorem descheduleThread_fully_descheduled
    (st : SystemState) (tid : SeLe4n.ThreadId) (executingCore : CoreId)
    (hPlacement : ∀ c : CoreId, c ≠ determineTargetCore st tid →
        tid ∉ st.scheduler.runQueueOnCore c
        ∧ st.scheduler.currentOnCore c ≠ some tid) :
    ∀ c : CoreId,
      tid ∉ (descheduleThread st tid executingCore).1.scheduler.runQueueOnCore c
      ∧ (descheduleThread st tid executingCore).1.scheduler.currentOnCore c
          ≠ some tid := by
  intro c
  by_cases hc : c = determineTargetCore st tid
  · subst hc
    exact descheduleThread_descheduled_on_home st tid executingCore
  · obtain ⟨hRQ, hCur⟩ :=
      descheduleThread_independent_of_other_core st tid executingCore c
        (fun h => hc h.symm)
    rw [hRQ, hCur]
    exact hPlacement c hc

/-- WS-SM SM6.E (affinity corollary, the SM5.H purge-completeness): under the
replenishment-affinity discipline — the SchedContext's pending replenishments
live only on the purge core's queue — the per-core bound arm removes **all**
of them system-wide: the purge core's by the `remove`, every other core's
vacuously by the pre-state affinity plus the per-core frames. -/
theorem cancelBoundDonationOnCore_replenishments_purged
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) (rqCore : CoreId)
    (scId : SeLe4n.SchedContextId)
    (hB : tcb.schedContextBinding = .bound scId)
    (hOnlyHome : ∀ c : CoreId, c ≠ rqCore →
        ∀ e ∈ (st.scheduler.replenishQueueOnCore c).entries, e.1 ≠ scId)
    (h : cancelBoundDonationOnCore st tid tcb rqCore = .ok st') :
    ∀ c : CoreId, ∀ e ∈ (st'.scheduler.replenishQueueOnCore c).entries,
      e.1 ≠ scId := by
  simp only [cancelBoundDonationOnCore, hB] at h
  injection h with h
  subst h
  intro c e hMem
  cases hSC : st.getSchedContext? scId with
  | none =>
    revert hMem
    simp only [hSC]
    split
    all_goals
      (by_cases hc : c = rqCore
       · subst hc
         simp only [SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_self]
         intro hMem hEq
         have hf := (List.mem_filter.mp hMem).2
         simp [hEq] at hf
       · simp only [SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne
             _ _ _ _ (fun hEq => hc hEq.symm)]
         intro hMem
         exact hOnlyHome c hc e hMem)
  | some sc =>
    revert hMem
    simp only [hSC]
    split
    all_goals
      (by_cases hc : c = rqCore
       · subst hc
         simp only [SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_self]
         intro hMem hEq
         have hf := (List.mem_filter.mp hMem).2
         simp [hEq] at hf
       · simp only [SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne
             _ _ _ _ (fun hEq => hc hEq.symm)]
         intro hMem
         exact hOnlyHome c hc e hMem)

/-- WS-SM SM6.E: at a bootCore-homed victim with a shared-home donated owner
(in particular every single-core configuration), the per-core donation
dispatcher's success outcome is exactly the single-core `cancelDonation`'s. -/
theorem cancelDonationOnCore_bootHome_ok
    (tid : SeLe4n.ThreadId) (tcb : TCB) (st st' : SystemState)
    (hHome : determineTargetCore st tid = bootCoreId)
    (hOwnerHome : ∀ scId owner, tcb.schedContextBinding = .donated scId owner →
        ∀ stR, cleanupDonatedSchedContext st tid = .ok stR →
          determineTargetCore stR owner = determineTargetCore st tid)
    (hOk : cancelDonation st tid tcb = .ok st') :
    cancelDonationOnCore tid tcb st = (st', .ok ()) := by
  cases hB : tcb.schedContextBinding with
  | unbound =>
    simp only [cancelDonation, hB] at hOk
    injection hOk with hOk
    subst hOk
    simp only [cancelDonationOnCore, hB]
  | bound scId =>
    simp only [cancelDonation, hB] at hOk
    simp only [cancelDonationOnCore, hB, hHome, cancelBoundDonationOnCore_bootCoreId,
      hOk]
  | donated scId owner =>
    simp only [cancelDonation, hB] at hOk
    simp only [cancelDonationOnCore, hB,
      cancelDonatedDonationOnCore_eq_of_sharedHome st tid tcb scId owner hB
        (hOwnerHome scId owner hB)]
    simp only [hOk]

/-- WS-SM SM6.E: the error twin of `cancelDonationOnCore_bootHome_ok` — the
dispatcher returns the pre-state with the single-core arm's error. -/
theorem cancelDonationOnCore_bootHome_error
    (tid : SeLe4n.ThreadId) (tcb : TCB) (st : SystemState) (e : KernelError)
    (hHome : determineTargetCore st tid = bootCoreId)
    (hOwnerHome : ∀ scId owner, tcb.schedContextBinding = .donated scId owner →
        ∀ stR, cleanupDonatedSchedContext st tid = .ok stR →
          determineTargetCore stR owner = determineTargetCore st tid)
    (hErr : cancelDonation st tid tcb = .error e) :
    cancelDonationOnCore tid tcb st = (st, .error e) := by
  cases hB : tcb.schedContextBinding with
  | unbound =>
    simp only [cancelDonation, hB] at hErr
    cases hErr
  | bound scId =>
    simp only [cancelDonation, hB] at hErr
    simp only [cancelDonationOnCore, hB, hHome, cancelBoundDonationOnCore_bootCoreId,
      hErr]
  | donated scId owner =>
    simp only [cancelDonation, hB] at hErr
    simp only [cancelDonationOnCore, hB,
      cancelDonatedDonationOnCore_eq_of_sharedHome st tid tcb scId owner hB
        (hOwnerHome scId owner hB)]
    simp only [hErr]

end SeLe4n.Kernel
