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
import SeLe4n.Kernel.SchedContext.ReplenishAffinity

/-!
# WS-SM SM6.E — Cancellation across cores

This module is the SM6.E deliverable of the WS-SM Phase 6 cross-core IPC
workstream (plan `docs/planning/SMP_CROSS_CORE_IPC_PLAN.md` §3.1, §5).  It
lifts the two cancellation sub-operations of the suspend pipeline
(`Lifecycle.Suspend`) to *cross-core* transitions under the SM3.B per-object
lock-set discipline:

* **`descheduleThread`** — the SM5.C `wakeThread` dual: removes a thread from
  the run queue / current slot of the core the state **places** it on
  (`descheduleAtPlacement` over `placedCoreOf?` — WS-RR RR8.6; its *home*
  core, `determineTargetCore`, until then), surfacing a `.reschedule` SGI when
  the thread was *actively current on a remote core* — the poke that stops that
  core from continuing to execute a cancelled/suspended thread.  A merely-queued
  remote victim needs no poke (the dequeue suffices); a victim current on the
  *executing* core is rescheduled synchronously by the caller (the suspend
  pipeline's G7), so no self-SGI is surfaced — mirroring `wakeThread`'s SGI
  discipline.  The poke reads the same placement the removal acts on, and
  nothing else (`descheduleSgi?`): the wake's ghost-guard is not mirrored,
  because a removal takes a placed thread off its core whether or not a TCB
  backs it, so a guard on the TCB would clear a slot and poke nobody.
* **`cancelIpcBlockingOnCore`** — the cross-core cancellation composite
  (plan SM6.E.5): the single-core `cancelIpcBlocking` object-level teardown
  (endpoint/notification dequeue, reply-link consume, TCB IPC-field clear),
  WS-RR RR7.22's replenishment migration and WS-OD OD1.7's holder wake,
  followed by the placement deschedule + remote poke — definitionally
  `descheduleThread` on the post-wake state
  (`cancelIpcBlockingOnCore_eq_descheduleThread`).  This is the G2+G4+G7 slice
  of `suspendThread` generalised across cores: on a single core G4's
  `removeRunnable` is bootCore-pinned and G7 reschedules locally; across cores
  the deschedule must target the core the victim is actually on and an
  actively-running remote victim must be interrupted.  The footprint is
  declared on the **pre-state** (the SM3.B lock-set pre-resolution discipline)
  and the removal resolves on the state it acts on;
  `cancelIpcBlockingOnCoreSchedLockSet_covers_deschedule` is the relation
  between the two, resting on `cancelIpcBlocking_scheduler_eq` (the teardown
  never touches the scheduler) and on the wake inserting a thread that is not a
  placed victim.
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
  notification (W), pre-resolved from the victim's `ipcState`; (SM6.D
  reply-object fold) the consumed Reply object (W) when the victim is
  `.blockedOnReply` with a live `replyObject` link; (WS-RR RR7.22 residual) the
  returned SchedContext (W) and the donation holder's TCB (W); (WS-OD OD1.5)
  the **holder's** endpoint (W) and its two queue neighbours (W), which the
  reclaim's abort prefix splices; (WS-OD OD3.7) the frame below the
  reply-stack head — a **write** since WS-OD `v0.35.4`, when the pop began
  re-heading it — and the outer caller's TCB (R); and (WS-OD `v0.35.4`) the
  head the reclaim clears (W) and the frame above the cancelled caller's own,
  which the splice rewrites (W).
* `lockSet_cancelDonation` — donor (victim) TCB (W); bound/donated
  SchedContext (W); donated-arm original-owner TCB (W) (the plan row's
  "receiver TCB"); and (WS-OD `v0.35.4`) the donated arm's pop: the head it
  clears (W), the frame below it re-heads (W) and the outer caller it validates
  (R).

The `.tcbSuspend` syscall's footprint, `lockSet_tcbSuspendOnCore` (§8), is
**defined over** the state-resolved `lockSet_cancelIpcBlockingOnCore` — the
formal content of "the cancellation sub-operations run inside the suspend
syscall's 2PL bracket" (plan SM6.E.1/SM6.E.3) is one lift
(`lockSet_tcbSuspendOnCore_covers_cancelIpcBlockingOnCore`) rather than a
member-by-member family, and the donation cancellation's members are resolved
on the binding the teardown leaves rather than on the one the victim entered
with (WS-OD `v0.35.4`).

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
lock.  This is the same rationale under which the parametric
`lockSet_tcbSuspend` footprint (SM3.B.3, audit-pass-3; retired at WS-OD
`v0.35.4`) declared its optional single-endpoint/notification locks for the same
sweeps.

**Live wiring status (audit-corrected; re-corrected at WS-RR RR8.12).**  The
live `.tcbSuspend` dispatch landed at v0.32.61 through `suspendThreadOnCore`
(§13 of this module, behind `API.dispatchCapabilityOnly` and the
`suspend_thread_cross_core` FFI seam) — NOT through
`cancelIpcBlockingOnCore`/`descheduleThread`, which remain the theorem-level
composites.  **Do not wire those live as-is**: the pipeline performs its own
placement deschedule at G4 and its own G7 reschedule, so composing the whole
composite would remove the victim twice.

**What that reading cost, and the rule it earns.**  Because the *composite* was
where WS-OD OD1.7's holder wake and WS-RR RR7.22/RR8.11's replenishment migration
were added, and because it has no production caller, **neither fix was on the path
a syscall takes** — measured at RR8.12, an aborted donation holder was left
`.ready` and `.unbound` on no run queue on any core.  The remedy is not to wire
the composite but to name its *prefix* (`cancelIpcBlockingReclaimed`), which G2
now reads: a composite whose prefix a second consumer needs is a shared answer
that consumer cannot reach, and the two then drift in the direction of whichever
one a later cut happens to edit.  A step added to the cancellation *teardown* goes
in the prefix; only a step about the victim's own placement belongs to the
composite.

The remaining tracked follow-on is the `withLockSet` 2PL bracket around the live
path (the SM3.C.9/SM5.I deferral); this module proves the SM6.E theorems that
bracket consumes.

**Neighbour-lock convention bridge (audit note, closed at WS-OD `v0.35.4`).**
Until `v0.35.4` the syscall-level footprint was the parametric
`lockSet_tcbSuspend`, which covered the splice's neighbour queue-link writes
only under the *endpoint* write lock (the queue-owning-object discipline
above), while the sub-operation-level `lockSet_cancelIpcBlockingOnCore`
declared the same writes explicitly as neighbour-TCB locks
(`queueSpliceNeighbors?`, PR #831 review 4) — two footprints for one
transition, reconciled by prose.  The syscall footprint is now rooted at the
sub-operation footprint (§8), so the neighbour locks the runtime bracket
acquires are the ones the sub-operation declares, and the endpoint lock is the
exclusion mechanism WS-RR RR7.38 made it rather than a stand-in for members.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency
open SeLe4n.Kernel.Lifecycle.Suspend

-- ============================================================================
-- §1  The per-core deschedule primitive — `descheduleThread` (wakeThread dual)
-- ============================================================================

/-- **WS-RR RR8.6**: the `.reschedule` poke a deschedule owes, resolved on the
SAME placement the removal acts on.

`some (c, .reschedule)` exactly when the state places `tid` on core `c`
(`placedCoreOf?`), `tid` is **current** there, and `c` is not the executing
core: `c` is executing a thread the kernel has just taken off its scheduler and
must re-run its selection.  A merely-queued victim needs no poke (the dequeue
suffices — the remote core simply never dispatches it again), and a victim
current on the executing core is rescheduled synchronously by the caller (the
suspend pipeline's G7), so no self-SGI is surfaced — `wakeThread`'s SGI
discipline, mirrored.

Two things this resolver deliberately does NOT read.  Not `determineTargetCore`:
that is the thread's *home* (its affinity, `bootCoreId` when unpinned), which is
where a wake places it and not where a removal finds it — `preemptCurrentOnCore`
re-enqueues a preempted thread on the core that ran it, and an unpinned thread
may run on any core, so its queue can sit on a core its home never names.  And
not the object store: `wakeThread`'s ghost-guard (`getTcb? = none` ⇒ no SGI) is
*consistency with the state effect* there, because a wake of a thread with no
TCB inserts nothing; a removal takes a placed thread off its core whether or not
a TCB backs it, so the same guard here cleared a remote core's current slot and
poked nobody — the fail-open direction, inert on every reachable state (a
current thread resolves to a TCB under the per-core scheduler invariants) and
gone regardless.  The poke is a function of the two scheduler slices the
removal edits, and of nothing else. -/
def descheduleSgi? (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) : Option (CoreId × SgiKind) :=
  match placedCoreOf? st tid with
  | some c =>
      if st.scheduler.currentOnCore c = some tid ∧ c ≠ executingCore
      then some (c, SgiKind.reschedule)
      else none
  | none => none

/-- WS-SM SM6.E (plan §3.1), re-keyed at **WS-RR RR8.6**: deschedule a thread
from wherever the state places it, across cores.

Removes `tid` from the run queue and current slot of the core the state
**places** it on (`descheduleAtPlacement`, over `placedCoreOf?`: queued or
current, the first such core in the model's order), and surfaces the
`.reschedule` SGI that placement owes (`descheduleSgi?`).  The removal and the
poke read ONE resolver, so the SGI targets exactly the core whose current slot
the removal cleared.

Until RR8.6 both halves were keyed on `determineTargetCore` — the thread's
*home* — which PR #895 review round 10 records as a proxy for placement:
`affinityAdmitsCore` is `true` on every core for an unpinned thread, so nothing
pins such a thread's queue to its home, and a deschedule at the home of a
thread queued elsewhere removed nothing and poked nobody.
`descheduleAtPlacement` is the remedy that review chose for the reply path;
this is the same remedy at the cancellation path, which the review named and
did not sweep.

Pure function of `(st, tid, executingCore)`; deterministic; total. -/
def descheduleThread (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) : SystemState × Option (CoreId × SgiKind) :=
  (descheduleAtPlacement st tid, descheduleSgi? st tid executingCore)

/-- WS-SM SM6.E: the post-state of `descheduleThread` is exactly the placement
removal — the SGI decision never alters the state. -/
theorem descheduleThread_state_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) :
    (descheduleThread st tid executingCore).1 = descheduleAtPlacement st tid := rfl

/-- WS-RR RR8.6: ...and its SGI is the placement's poke. -/
theorem descheduleThread_sgi_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) :
    (descheduleThread st tid executingCore).2 = descheduleSgi? st tid executingCore := rfl

/-- WS-SM SM6.E: `descheduleThread` never touches `objects`. -/
theorem descheduleThread_objects_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) :
    (descheduleThread st tid executingCore).1.objects = st.objects :=
  descheduleAtPlacement_preserves_objects st tid

/-- WS-SM SM6.E: a victim **actively current on a remote core** — the core the
state places it on — surfaces a `.reschedule` SGI targeting that core: the poke
that stops the remote core from continuing to execute it. -/
theorem descheduleThread_emits_sgi_if_remote_current
    (st : SystemState) (tid : SeLe4n.ThreadId) (executingCore c : CoreId)
    (hPlaced : placedCoreOf? st tid = some c)
    (hCur : st.scheduler.currentOnCore c = some tid)
    (hRemote : c ≠ executingCore) :
    (descheduleThread st tid executingCore).2 = some (c, SgiKind.reschedule) := by
  unfold descheduleThread descheduleSgi?
  simp only [hPlaced]
  rw [if_pos ⟨hCur, hRemote⟩]

/-- WS-SM SM6.E: a victim the state places on the executing core surfaces no
SGI — the caller reschedules synchronously. -/
theorem descheduleThread_no_sgi_if_local
    (st : SystemState) (tid : SeLe4n.ThreadId) (executingCore : CoreId)
    (hLocal : placedCoreOf? st tid = some executingCore) :
    (descheduleThread st tid executingCore).2 = none := by
  unfold descheduleThread descheduleSgi?
  simp only [hLocal]
  rw [if_neg (fun h => h.2 rfl)]

/-- WS-SM SM6.E: a victim that is **current nowhere** — merely queued, or
blocked and in no queue at all, which is every thread the state places nowhere
— surfaces no SGI: removing it from its run queue suffices, no core is
executing it. -/
theorem descheduleThread_no_sgi_if_not_current
    (st : SystemState) (tid : SeLe4n.ThreadId) (executingCore : CoreId)
    (hNotCur : runningOnSomeCore st tid = false) :
    (descheduleThread st tid executingCore).2 = none := by
  unfold descheduleThread descheduleSgi?
  cases hP : placedCoreOf? st tid with
  | none => rfl
  | some c =>
      simp only []
      rw [if_neg]
      intro h
      have hRun : runningOnSomeCore st tid = true := by
        unfold runningOnSomeCore
        exact List.any_eq_true.mpr ⟨c, Concurrency.mem_allCores c, by simp [h.1]⟩
      rw [hNotCur] at hRun
      exact Bool.false_ne_true hRun

/-- WS-RR RR8.6: a thread the state places nowhere is removed from nothing and
pokes nobody — the step is the identity.  Every genuinely blocked thread is such
a thread (blocked threads are neither queued nor current), which is why the
ordinary cancellation of an IPC-blocked victim performs the object teardown and
no scheduler write at all. -/
theorem descheduleThread_unplaced (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) (h : placedCoreOf? st tid = none) :
    descheduleThread st tid executingCore = (st, none) := by
  unfold descheduleThread descheduleAtPlacement descheduleAt descheduleSgi?
  simp only [h]

/-- Audit closure: `removeRunnableOnCore` preserves current-uniqueness — it
only *clears* current slots (core `k`'s slot becomes `none` or keeps its
pre value; every other core is untouched), and clearing can never create a
duplicate. -/
theorem removeRunnableOnCore_preserves_currentThreadUniqueAcrossCores
    (st : SystemState) (tid : SeLe4n.ThreadId) (k : CoreId)
    (h : currentThreadUniqueAcrossCores st) :
    currentThreadUniqueAcrossCores (removeRunnableOnCore st tid k) := by
  intro c c' t hc hc'
  have hred : ∀ d : CoreId,
      (removeRunnableOnCore st tid k).scheduler.currentOnCore d = some t →
      st.scheduler.currentOnCore d = some t := by
    intro d hd
    by_cases hdk : k = d
    · subst hdk
      rw [removeRunnableOnCore_currentOnCore_self] at hd
      split at hd
      · cases hd
      · exact hd
    · rwa [removeRunnableOnCore_currentOnCore_ne st tid k d hdk] at hd
  exact h c c' t (hred c hc) (hred c' hc')

/-- Audit closure: the per-core deschedule preserves current-uniqueness. -/
theorem descheduleThread_preserves_currentThreadUniqueAcrossCores
    (st : SystemState) (tid : SeLe4n.ThreadId) (executingCore : CoreId)
    (h : currentThreadUniqueAcrossCores st) :
    currentThreadUniqueAcrossCores (descheduleThread st tid executingCore).1 := by
  rw [descheduleThread_state_eq]
  unfold descheduleAtPlacement descheduleAt
  split
  · exact removeRunnableOnCore_preserves_currentThreadUniqueAcrossCores st tid _ h
  · exact h

/-- WS-SM SM6.E, re-keyed at WS-RR RR8.6: after `descheduleThread`, the thread
is fully descheduled on the core the state placed it on — not in that core's
run queue and not its current thread. -/
theorem descheduleThread_descheduled_at_placement
    (st : SystemState) (tid : SeLe4n.ThreadId) (executingCore c : CoreId)
    (hPlaced : placedCoreOf? st tid = some c) :
    tid ∉ (descheduleThread st tid executingCore).1.scheduler.runQueueOnCore c
    ∧ (descheduleThread st tid executingCore).1.scheduler.currentOnCore c ≠ some tid := by
  rw [descheduleThread_state_eq]
  unfold descheduleAtPlacement descheduleAt
  simp only [hPlaced]
  exact ⟨removeRunnableOnCore_not_mem_self st tid c,
         removeRunnableOnCore_currentOnCore_ne_self st tid c⟩

/-- WS-SM SM6.E: `descheduleThread` is confined to the placed core — every
other core's run queue and current slot are exactly the pre-state's (the
per-core locality dual of `wakeThread_independent_of_other_core`). -/
theorem descheduleThread_independent_of_other_core
    (st : SystemState) (tid : SeLe4n.ThreadId) (executingCore : CoreId)
    (c' : CoreId) (hOther : placedCoreOf? st tid ≠ some c') :
    (descheduleThread st tid executingCore).1.scheduler.runQueueOnCore c'
        = st.scheduler.runQueueOnCore c'
    ∧ (descheduleThread st tid executingCore).1.scheduler.currentOnCore c'
        = st.scheduler.currentOnCore c' := by
  rw [descheduleThread_state_eq]
  unfold descheduleAtPlacement descheduleAt
  cases hP : placedCoreOf? st tid with
  | none => exact ⟨rfl, rfl⟩
  | some c =>
      have hne : c ≠ c' := fun hEq => hOther (by rw [hP, hEq])
      exact ⟨removeRunnableOnCore_runQueueOnCore_ne st tid c c' hne,
             removeRunnableOnCore_currentOnCore_ne st tid c c' hne⟩

-- ============================================================================
-- §2  The cross-core cancellation transitions (plan SM6.E.1 / SM6.E.3 / SM6.E.5)
-- ============================================================================

-- ============================================================================
-- WS-RR RR8.12 (fifth cut): the reclaim moved to `Lifecycle/Suspend.lean`
-- ============================================================================
--
-- `cancelIpcBlockingMigrated`, the holder-wake family and `cancelIpcBlockingReclaimed`
-- were declared here and are now declared in `SeLe4n/Kernel/Lifecycle/Suspend.lean`,
-- beside the teardown they complete.  Their names are unchanged — they were and are
-- in the `SeLe4n.Kernel` namespace — so every reference in the tree is untouched.
--
-- The move is this project's *a shared answer must be reachable from every asker*
-- rule, not tidying.  The single-core `Lifecycle.Suspend.suspendThread`'s G2 needs
-- the reclaim-complete teardown and could not see it: this module **imports**
-- `Lifecycle/Suspend.lean`, so the second asker reached for the bare teardown and
-- the holder strand WS-OD OD1.7 exists to prevent was reachable on it.  When a
-- question has one owner and an asker that cannot see it, the owner is in the
-- wrong layer — and it was: every one of these definitions reads a `TCB`, a run
-- queue or a replenish queue, and none reads anything cross-core.



/-- WS-SM SM6.E.5 (plan §3.1): IPC-blocking cancellation across cores.

The single-core `cancelIpcBlocking` object-level teardown (endpoint /
notification dequeue, reply-link consume, TCB IPC-field clear — the suspend
pipeline's G2), WS-RR RR7.22's replenishment migration and WS-OD OD1.7's holder
wake, composed with the cross-core deschedule: the victim is removed from the
run queue / current slot of the core the state **places** it on
(`descheduleAtPlacement` — WS-RR RR8.6; the cross-core generalisation of G4's
bootCore-pinned `removeRunnable`), and a `.reschedule` SGI is surfaced when the
victim was actively current on a *remote* core (the cross-core generalisation
of G7's local reschedule).  Definitionally `descheduleThread` on the post-wake
state (`cancelIpcBlockingOnCore_eq_descheduleThread`).

**The placement is resolved on the state the removal acts on**, after the wake,
and that is deliberate: the reclaim's wake is a run-queue insert, and resolving
before it would leave the degenerate `holder = victim` insert standing (no
reachable state produces one — a reply-blocked victim is not a holder blocked
sending or calling — and the composite undoes it regardless).  The footprint
(`cancelIpcBlockingOnCoreSchedLockSet`) is declared on the **pre**-state, as
every footprint is, and covers the removal's core by
`cancelIpcBlockingOnCoreSchedLockSet_covers_deschedule`: the pre-state
placement, or — on that degenerate insert alone — the declared wake core.  A
victim the pre-state places somewhere is removed exactly there
(`cancelIpcBlockingOnCore_placedCoreOf?_of_some`), since the teardown writes no
scheduler slot (`cancelIpcBlocking_scheduler_eq`), the migration writes only
replenish queues, and the wake inserts a thread that is never a placed victim.

**TOCTOU caveat (resolution vs. concurrent mutation).**  On hardware the whole
transition runs inside the suspend syscall's 2PL bracket holding the victim's
TCB **write** lock (`lockSet_cancelIpcBlocking` ∋ `tcbLock victim`), and the
AN9-D FFI bracket (`with_interrupts_disabled` around
`suspend_thread_cross_core`) excludes same-core ISR interleavings.  The
placement scan reads OTHER cores' run queues and current slots, which the
victim's TCB lock does not serialise — its declared guard is the placed core's
`SchedLockId.runQueue` write lock in the scheduler-domain footprint, and in the
current runtime every transition is serialised through the single global state
ref (`modifyGetKernelState`; the per-object runtime acquisition is the
SM3.C.9/SM5.I deferral).  The same argument covers `suspendThreadOnCore`'s
pre-resolved reads (`placedCoreOf?`, `runningCoreOf?`, the `execCurPre`
capture) and `cancelDonationOnCore`'s home resolution.

Returns the post-state paired with the optional cross-core SGI to emit after
the state commit.  Total (the single-core teardown is pure), so a
`withLockSet` bracket always releases cleanly. -/
def cancelIpcBlockingOnCore (victim : SeLe4n.ThreadId) (tcb : TCB)
    (executingCore : CoreId) (st : SystemState) :
    SystemState × Option (CoreId × SgiKind) :=
  -- WS-OD OD1.7: the reclaim's abort unblocks the donation holder but places it
  -- nowhere; without this step no run queue ever holds it again and no kernel
  -- path can recover it.  Before the victim's removal, so that the degenerate
  -- `holder = victim` resolution is undone rather than left standing.
  descheduleThread (cancelIpcBlockingReclaimed victim tcb st) victim executingCore

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
    let st1 : SystemState := st.updateSchedContext scId fun sc =>
      -- **WS-HP HP10.4**: and the origin, as the single-core spelling does — the
      -- `_bootCoreId` bridge below is `rfl`, so the two cannot differ by a field.
      { sc with boundThread := none, isActive := false, donationOrigin := none }
    let st2 := { st1 with scheduler := st1.scheduler.setReplenishQueueOnCore rqCore (ReplenishQueue.remove (st1.scheduler.replenishQueueOnCore rqCore) scId) }
    let st2 := { st2 with scThreadIndex :=
      (scThreadIndexRemove st2.scThreadIndex scId tid) }
    .ok (st2.updateTcb tid fun tcb' => { tcb' with schedContextBinding := .unbound })
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

-- WS-RR RR2.3: the five hand-written production twins of the SM5.H migration
-- frames that used to sit here (`…_objects_eq`, `…_self_eq`,
-- `…_runQueue_current_eq`, `…_replenishQueue_other_eq`, `…_from_eq`) are gone.
-- They existed because the canonical forms lived in the staged
-- `Scheduler/Operations/PerCoreCbs.lean`, which production may not import; the
-- canonical forms now live in the production
-- `SeLe4n.Kernel.SchedContext.ReplenishAffinity` (imported above), so this arm
-- consumes `migrateSchedContextReplenishment_{noop,objects,machine,
-- runQueue_current_eq,replenishQueueOnCore_{to,from,other}}` directly and the
-- migration's frame is stated once for the whole tree.


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
definitional no-op (`migrateSchedContextReplenishment_noop`), recovering
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
      rw [hHome st' hC, migrateSchedContextReplenishment_noop]

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
      rw [migrateSchedContextReplenishment_objects]
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

/-- WS-SM SM6.E, re-keyed at WS-RR RR8.6: the post-state of the cross-core
cancellation is exactly the single-core teardown, the reclaim's holder wake, and
the placement removal — the SGI decision never alters the state. -/
theorem cancelIpcBlockingOnCore_state_eq (victim : SeLe4n.ThreadId) (tcb : TCB)
    (executingCore : CoreId) (st : SystemState) :
    (cancelIpcBlockingOnCore victim tcb executingCore st).1
      = descheduleAtPlacement
          (wakeAbortedDonationHolder st (cancelIpcBlockingMigrated victim tcb st) victim tcb)
          victim := rfl

/-- WS-SM SM6.E, the pre-remediation shape: when the caller donated nothing —
every arm but a reply arm whose caller had — the composite is exactly the
single-core teardown followed by the placement removal. -/
theorem cancelIpcBlockingOnCore_state_eq_of_no_donation (victim : SeLe4n.ThreadId) (tcb : TCB)
    (executingCore : CoreId) (st : SystemState)
    (h : Lifecycle.Suspend.cancelledCallerDonation? st victim tcb = none) :
    (cancelIpcBlockingOnCore victim tcb executingCore st).1
      = descheduleAtPlacement (cancelIpcBlocking st victim tcb) victim := by
  rw [cancelIpcBlockingOnCore_state_eq,
    wakeAbortedDonationHolder_of_no_donation _ _ victim tcb h,
    cancelIpcBlockingMigrated_of_no_donation victim tcb st h]

/-- WS-SM SM6.E: the cross-core cancellation's **object-level** effect is
exactly the single-core `cancelIpcBlocking`'s — the deschedule touches only
the scheduler. -/
theorem cancelIpcBlockingOnCore_objects_eq (victim : SeLe4n.ThreadId) (tcb : TCB)
    (executingCore : CoreId) (st : SystemState) :
    (cancelIpcBlockingOnCore victim tcb executingCore st).1.objects
      = (cancelIpcBlocking st victim tcb).objects := by
  rw [cancelIpcBlockingOnCore_state_eq, descheduleAtPlacement_preserves_objects,
    wakeAbortedDonationHolder_objects, cancelIpcBlockingMigrated_objects]

/-- WS-SM SM6.E, definitional since WS-RR RR8.6: the composite **is**
`descheduleThread` on the post-wake state.  Until RR8.6 this needed two
resolution-coincidence hypotheses — the home core and the `getTcb?` status
agree before and after the teardown — because the composite pre-resolved the
victim's home while `descheduleThread` resolved it afresh; both now read the
placement at the state the removal acts on, so there is nothing to reconcile,
and the closed form those hypotheses were discharged into is gone with them. -/
theorem cancelIpcBlockingOnCore_eq_descheduleThread
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (st : SystemState) :
    cancelIpcBlockingOnCore victim tcb executingCore st
      = descheduleThread
          (wakeAbortedDonationHolder st (cancelIpcBlockingMigrated victim tcb st) victim tcb)
          victim executingCore := rfl

/-- **WS-RR RR8.12**: and stated over the named prefix, which is the form the
suspend pipeline's G2 reads.

The relation between the two consumers of the reclaim-complete teardown, so
"`suspendThreadOnCore`'s G2 is this composite's teardown half" is a theorem
rather than a reading of two bodies.  `rfl`, because the prefix *is* the
composite minus its deschedule. -/
theorem cancelIpcBlockingOnCore_eq_reclaimed_deschedule
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (st : SystemState) :
    cancelIpcBlockingOnCore victim tcb executingCore st
      = descheduleThread (cancelIpcBlockingReclaimed victim tcb st) victim executingCore := rfl

/-- WS-SM SM6.E: a `.ready` victim's cancellation is a pure cross-core
deschedule — the object-level teardown is the identity, so the composite is
`descheduleThread` on the pre-state.  This is the suspend-of-a-running-thread
scenario (the victim was executing or queued, not blocked). -/
theorem cancelIpcBlockingOnCore_ready_eq_descheduleThread
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (st : SystemState) (hReady : tcb.ipcState = .ready) :
    cancelIpcBlockingOnCore victim tcb executingCore st
      = descheduleThread st victim executingCore := by
  have hId : cancelIpcBlockingMigrated victim tcb st = st := by
    have hNone : Lifecycle.Suspend.cancelledCallerDonation? st victim tcb = none := by
      unfold Lifecycle.Suspend.cancelledCallerDonation?
      rw [hReady]
    rw [cancelIpcBlockingMigrated_of_no_donation victim tcb st hNone]
    unfold cancelIpcBlocking
    rw [hReady]
  have hNoWake : wakeAbortedDonationHolder st (cancelIpcBlockingMigrated victim tcb st)
      victim tcb = cancelIpcBlockingMigrated victim tcb st :=
    wakeAbortedDonationHolder_of_no_donation _ _ victim tcb (by
      unfold Lifecycle.Suspend.cancelledCallerDonation?
      rw [hReady])
  rw [cancelIpcBlockingOnCore_eq_descheduleThread, hNoWake, hId]

-- WS-RR RR8.11: `cancelIpcBlocking_determineTargetCore_eq` moved to
-- `SeLe4n/Kernel/IPC/Invariant/CancellationBundle.lean` and was generalised there
-- from the victim to an arbitrary thread.  The proof it had here could only be
-- stated at the victim, because `cancelIpcBlocking_getTcb?_none` is: the general
-- form needs the teardown's whole affinity frame, which is built from the
-- per-step frames that module has the imports for.  The name is unchanged, so
-- the citation in `suspendThreadOnCore`'s G1 comment still resolves.


/-- WS-RR RR8.6: neither the teardown nor the replenishment migration writes a
run queue or a current slot, so every thread's placement on the migrated
teardown is the pre-state's. -/
theorem cancelIpcBlockingMigrated_placedCoreOf? (victim : SeLe4n.ThreadId) (tcb : TCB)
    (st : SystemState) (x : SeLe4n.ThreadId) :
    placedCoreOf? (cancelIpcBlockingMigrated victim tcb st) x = placedCoreOf? st x := by
  apply placedCoreOf?_congr_of_runQueue_current_eq
  intro c
  rw [cancelIpcBlockingMigrated_runQueueOnCore, cancelIpcBlockingMigrated_currentOnCore,
    cancelIpcBlocking_scheduler_eq]
  exact ⟨rfl, rfl⟩

/-- Inserting one thread into a run queue changes no other thread's membership. -/
private theorem runQueue_contains_insert_of_ne (rq : RunQueue) (tid : SeLe4n.ThreadId)
    (prio : Priority) (x : SeLe4n.ThreadId) (h : x ≠ tid) :
    (rq.insert tid prio).contains x = rq.contains x := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    rcases (RunQueue.mem_insert rq tid prio x).mp hx with hm | hm
    · exact hm
    · exact absurd hm h
  · intro hx
    exact (RunQueue.mem_insert rq tid prio x).mpr (Or.inl hx)

/-- The elementwise reading of "placed nowhere": on every core, neither queued
nor current. -/
private theorem not_placed_of_unplaced (st : SystemState) (tid : SeLe4n.ThreadId)
    (hQ : runnableOnSomeCore st tid = false) (hR : runningOnSomeCore st tid = false)
    (c : CoreId) :
    ((st.scheduler.runQueueOnCore c).contains tid
      || st.scheduler.currentOnCore c == some tid) = false := by
  unfold runnableOnSomeCore at hQ
  unfold runningOnSomeCore at hR
  rw [List.any_eq_false] at hQ hR
  have h1 := hQ c (Concurrency.mem_allCores c)
  have h2 := hR c (Concurrency.mem_allCores c)
  simp only [Bool.not_eq_true] at h1 h2
  rw [h1, h2]
  rfl

/-- **WS-RR RR8.6: the placement the composite deschedules at, read off the
pre-state.**  The transition resolves the victim's placement on the post-wake
state, and the footprint — declared before anything runs — on the pre-state.
The two agree, with one exception the second disjunct names: the reclaim's wake
is a run-queue insert, and if the holder it wakes *is* the victim (the
degenerate `holder = victim` resolution, which no reachable state produces — a
reply-blocked victim is not a holder blocked sending or calling) and the victim
was placed nowhere, that insert is the victim's only placement and sits on the
declared wake core.  Either way every core the removal may write is declared
(`cancelIpcBlockingOnCoreSchedLockSet_covers_deschedule`), and a victim the
pre-state places somewhere is removed exactly there
(`cancelIpcBlockingOnCore_placedCoreOf?_of_some`). -/
theorem cancelIpcBlockingOnCore_placedCoreOf?_cases (victim : SeLe4n.ThreadId) (tcb : TCB)
    (st : SystemState) :
    placedCoreOf?
        (wakeAbortedDonationHolder st (cancelIpcBlockingMigrated victim tcb st) victim tcb)
        victim
      = placedCoreOf? st victim
    ∨ (placedCoreOf? st victim = none
        ∧ placedCoreOf?
            (wakeAbortedDonationHolder st (cancelIpcBlockingMigrated victim tcb st) victim tcb)
            victim
          = cancelAbortedHolderWakeCore? st (cancelIpcBlockingMigrated victim tcb st)
              victim tcb) := by
  have hM : placedCoreOf? (cancelIpcBlockingMigrated victim tcb st) victim
      = placedCoreOf? st victim :=
    cancelIpcBlockingMigrated_placedCoreOf? victim tcb st victim
  unfold wakeAbortedDonationHolder cancelAbortedHolderWakeCore?
  generalize hStM : cancelIpcBlockingMigrated victim tcb st = stM at hM ⊢
  split
  · exact Or.inl hM
  · rename_i holder hW
    rw [hW, Option.map_some]
    unfold enqueueAbortedHolderOnCore
    split
    · exact Or.inl hM
    · rename_i t hT
      split
      · exact Or.inl hM
      · rename_i hG
        by_cases hHV : holder = victim
        · rw [hHV] at hG ⊢
          right
          have hRun : runnableOnSomeCore stM victim = false
              ∧ runningOnSomeCore stM victim = false := by
            simpa [Bool.or_eq_false_iff] using hG
          refine ⟨?_, ?_⟩
          · rw [← hM]
            cases hp : placedCoreOf? stM victim with
            | none => rfl
            | some c =>
              have hIs := placedCoreOf?_isSome_iff stM victim
              rw [hp, hRun.1, hRun.2] at hIs
              simp at hIs
          · apply placedCoreOf?_eq_some_of_unique
            · refine Bool.or_eq_true_iff.mpr (Or.inl ?_)
              show ((stM.scheduler.setRunQueueOnCore (determineTargetCore st victim)
                ((stM.scheduler.runQueueOnCore (determineTargetCore st victim)).insert victim
                  t.boostedPriority)).runQueueOnCore
                    (determineTargetCore st victim)).contains victim = true
              rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
              exact (RunQueue.mem_insert _ victim _ victim).mpr (Or.inr rfl)
            · intro c hc
              show (((stM.scheduler.setRunQueueOnCore (determineTargetCore st victim)
                ((stM.scheduler.runQueueOnCore (determineTargetCore st victim)).insert victim
                  t.boostedPriority)).runQueueOnCore c).contains victim
                || (stM.scheduler.setRunQueueOnCore (determineTargetCore st victim)
                ((stM.scheduler.runQueueOnCore (determineTargetCore st victim)).insert victim
                  t.boostedPriority)).currentOnCore c == some victim) = false
              rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ (Ne.symm hc),
                SchedulerState.setRunQueueOnCore_currentOnCore]
              exact not_placed_of_unplaced stM victim hRun.1 hRun.2 c
        · left
          rw [← hM]
          apply placedCoreOf?_congr_of_contains_current_eq
          intro c
          refine ⟨?_, by simp⟩
          show ((stM.scheduler.setRunQueueOnCore (determineTargetCore st holder)
            ((stM.scheduler.runQueueOnCore (determineTargetCore st holder)).insert holder
              t.boostedPriority)).runQueueOnCore c).contains victim
            = (stM.scheduler.runQueueOnCore c).contains victim
          by_cases hc : c = determineTargetCore st holder
          · rw [hc, SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
            exact runQueue_contains_insert_of_ne _ holder _ victim (fun h => hHV h.symm)
          · rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ (Ne.symm hc)]

/-- WS-RR RR8.6: a victim the PRE-state places on core `c` is descheduled at
`c` by the composite — the reclaim's holder wake, which runs between the
teardown and the removal, inserts a thread that is never a placed victim. -/
theorem cancelIpcBlockingOnCore_placedCoreOf?_of_some (victim : SeLe4n.ThreadId) (tcb : TCB)
    (st : SystemState) (c : CoreId) (h : placedCoreOf? st victim = some c) :
    placedCoreOf?
        (wakeAbortedDonationHolder st (cancelIpcBlockingMigrated victim tcb st) victim tcb)
        victim = some c := by
  rcases cancelIpcBlockingOnCore_placedCoreOf?_cases victim tcb st with hEq | ⟨hPre, _⟩
  · rw [hEq, h]
  · rw [h] at hPre
    cases hPre

/-- WS-RR RR8.6: the teardown, the migration and the wake leave every core's
current thread as it was, so "current nowhere" carries to the state the
composite deschedules at. -/
theorem cancelIpcBlockingOnCore_runningOnSomeCore (victim : SeLe4n.ThreadId) (tcb : TCB)
    (st : SystemState) (x : SeLe4n.ThreadId) :
    runningOnSomeCore
        (wakeAbortedDonationHolder st (cancelIpcBlockingMigrated victim tcb st) victim tcb) x
      = runningOnSomeCore st x := by
  unfold runningOnSomeCore
  simp only [wakeAbortedDonationHolder_currentOnCore, cancelIpcBlockingMigrated_currentOnCore,
    cancelIpcBlocking_scheduler_eq]

-- ============================================================================
-- §4  SGI emission of the cross-core cancellation composite
-- ============================================================================

/-- WS-SM SM6.E.5, re-keyed at WS-RR RR8.6: cancelling a victim **actively
current on a remote core** — the core the pre-state places it on — surfaces a
`.reschedule` SGI targeting that core: the cross-core poke the runtime fires
after the state commit, so the remote core stops executing the cancelled
thread. -/
theorem cancelIpcBlockingOnCore_emits_sgi_if_remote_current
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore c : CoreId)
    (st : SystemState)
    (hPlaced : placedCoreOf? st victim = some c)
    (hCur : st.scheduler.currentOnCore c = some victim)
    (hRemote : c ≠ executingCore) :
    (cancelIpcBlockingOnCore victim tcb executingCore st).2
      = some (c, SgiKind.reschedule) := by
  rw [cancelIpcBlockingOnCore_eq_descheduleThread]
  refine descheduleThread_emits_sgi_if_remote_current _ victim executingCore c
    (cancelIpcBlockingOnCore_placedCoreOf?_of_some victim tcb st c hPlaced) ?_ hRemote
  rw [wakeAbortedDonationHolder_currentOnCore, cancelIpcBlockingMigrated_currentOnCore,
    cancelIpcBlocking_scheduler_eq]
  exact hCur

/-- WS-SM SM6.E.5: cancelling a victim the pre-state places on the executing
core surfaces no SGI — the caller (the suspend pipeline's G7) reschedules
synchronously. -/
theorem cancelIpcBlockingOnCore_no_sgi_if_local
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (st : SystemState)
    (hLocal : placedCoreOf? st victim = some executingCore) :
    (cancelIpcBlockingOnCore victim tcb executingCore st).2 = none := by
  rw [cancelIpcBlockingOnCore_eq_descheduleThread]
  exact descheduleThread_no_sgi_if_local _ victim executingCore
    (cancelIpcBlockingOnCore_placedCoreOf?_of_some victim tcb st executingCore hLocal)

/-- WS-SM SM6.E.5: cancelling a victim that is **current nowhere** — the
ordinary case of a genuinely IPC-blocked victim (blocked threads are neither
queued nor current) — surfaces no SGI: the object-level dequeue plus the
(no-op) run-queue removal suffice, no core is executing it. -/
theorem cancelIpcBlockingOnCore_no_sgi_if_not_current
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (st : SystemState)
    (hNotCur : runningOnSomeCore st victim = false) :
    (cancelIpcBlockingOnCore victim tcb executingCore st).2 = none := by
  rw [cancelIpcBlockingOnCore_eq_descheduleThread]
  exact descheduleThread_no_sgi_if_not_current _ victim executingCore
    (by rw [cancelIpcBlockingOnCore_runningOnSomeCore]; exact hNotCur)

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

/-- WS-OD OD3.5: **the queue-neighbour TCBs *this arm* relinks.**

`queueSpliceNeighbors?` above reads the victim's interior links whatever state
it is in, and it was the one resolver in this family that did not key on
`tcb.ipcState`: `cancelBlockedEndpoint?`, `cancelBlockedNotification?`,
`cancelConsumedReply?` and `cancelledCallerDonation?` all select an arm, and the
neighbour pair was *summed* over every arm.  Only the endpoint arm splices —
`cancelIpcBlocking`'s three endpoint-blocking cases run
`removeFromAllEndpointQueues`, whose `spliceOutMidQueueNode` step is the sole
writer of a neighbour's `queueNext` / `queuePrev`.  The notification arm rewrites
notification objects and the victim; the reply arm rewrites the victim, the
donation holder, the holder's own endpoint and *its* two neighbours (all four
already declared); the `.ready` arm commits nothing.

So on three of the four arms the summed form declared two TCB write locks the
operation does not take, which costs headroom — the reply arm sat at nine of
nine, `maxLockSetSize` exactly — and, because lock contention is an observable
channel (SM8.D's CC-5), costs contention that carries no information about the
cancellation.  A footprint that is too wide is sound and not free.

Derived from `cancelBlockedEndpoint?` rather than re-matching `ipcState`: the
arm question is asked once, so the two cannot answer it differently. -/
def cancelArmSpliceNeighbors? (tcb : TCB) :
    Option SeLe4n.ThreadId × Option SeLe4n.ThreadId :=
  if (cancelBlockedEndpoint? tcb).isSome then queueSpliceNeighbors? tcb
  else (none, none)

/-- WS-OD OD3.5: on the arm that splices, the narrowed resolver **is** the
summed one — so every statement taken over `queueSpliceNeighbors?` on an
endpoint-blocked victim (SM8.D.5's
`suspendFootprint_splice_neighbors_under_endpoint_lock`, for one) transfers
unchanged. -/
@[simp] theorem cancelArmSpliceNeighbors?_of_blockedEndpoint (tcb : TCB)
    (ep : SeLe4n.ObjId) (h : cancelBlockedEndpoint? tcb = some ep) :
    cancelArmSpliceNeighbors? tcb = queueSpliceNeighbors? tcb := by
  unfold cancelArmSpliceNeighbors?
  rw [h]
  rfl

/-- WS-OD OD3.5: and on every other arm it is empty. -/
@[simp] theorem cancelArmSpliceNeighbors?_of_not_blockedEndpoint (tcb : TCB)
    (h : cancelBlockedEndpoint? tcb = none) :
    cancelArmSpliceNeighbors? tcb = (none, none) := by
  unfold cancelArmSpliceNeighbors?
  rw [h]
  rfl

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
from mutually exclusive `ipcState` arms).

**WS-OD OD1.5** adds the reclaim's abort prefix: `abortHolderPendingIpc` splices
the *holder* out of the *holder's* endpoint queue, so that endpoint and both of
the holder's queue neighbours are writes too.  All three are `none` unless a
donation is resolved and its holder is blocked sending or calling — which is the
abort's own guard, so the footprint names exactly what runs.

The **summed** arity is eleven, over `maxLockSetSize`; the resolved bound holds
because the donation-derived members and the victim's own blocked-object members
are mutually exclusive, both keying on `tcb.ipcState`
(`lockSet_cancelIpcBlockingOnCore_size_le`).

**WS-OD OD3.5**: the resolved footprint is now **arm-selected** rather than
summed — `cancelArmSpliceNeighbors?` gives the victim's own neighbours only on
the arm that splices — so the reply arm dropped from ten members to eight rather
than carrying two TCB write locks for a splice it does not perform.

**WS-OD OD3.7** took that arm to **ten**: the reclaim's hand-back reads the
Reply one frame below the reply-stack head and that frame's caller's TCB, and at
call depth ≥ 2 neither is covered by another member.

**WS-OD (`v0.35.4`)** takes the arm to **twelve** over all argument values, and
changes one mode.  The reply stack is doubly linked now, so the pop *writes* the
frame below the head (`storeReplyReHead`: it becomes the new head) — the
below-head member is **write**, not read.  Two members join: the **head** the
reclaim clears (`reclaimHeadReplyId`, resolved through `replyStackHead?` on the
returned context — on every reachable state it is the cancelled caller's own
reply object and merges with `consumedReplyId` by key, but a footprint is the
union over all argument values and the operation writes whatever `scReply`
names), and the **frame above** the cancelled caller's own
(`splicedFrameAboveReplyId`), which `spliceThreadReplyFrameOut` unlinks when
the caller is not the head of its stack — seL4's `reply_remove_tcb`, non-head
arm.  The two are mutually exclusive on every reachable state (a caller whose
frame has something above it is not the innermost live caller, so no reclaim is
resolved for it) and are declared independently because the footprint does not
get to assume that.  The outer caller stays **read**: the pop validates it
(`outerCallerAcceptable`) and names it as the new owner without writing its TCB.
`lockSet_cancelIpcBlockingOnCore_size_le_thirteen` is the bound over all argument
values (`lockSet_cancelIpcBlockingOnCore_size_le` is its corollary at the
ceiling); the reachable reply-arm figure is still ten, by the two merges above. -/
def lockSet_cancelIpcBlocking (victimTid : SeLe4n.ThreadId)
    (blockedEndpointObjId : Option SeLe4n.ObjId)
    (blockedNotificationObjId : Option SeLe4n.ObjId)
    (consumedReplyId : Option SeLe4n.ReplyId)
    (returnedDonationSc : Option SeLe4n.SchedContextId)
    (donationHolderTid : Option SeLe4n.ThreadId)
    (holderEndpointObjId : Option SeLe4n.ObjId)
    (holderSpliceNeighbors : Option SeLe4n.ThreadId × Option SeLe4n.ThreadId)
    (belowHeadReplyId : Option SeLe4n.ReplyId)
    (outerCallerTid : Option SeLe4n.ThreadId)
    (reclaimHeadReplyId : Option SeLe4n.ReplyId)
    (splicedFrameAboveReplyId : Option SeLe4n.ReplyId)
    -- **WS-HP HP3.1**: and the frame **below** the cancelled caller's own, which
    -- the removal's splice re-links upward in the same step -- the cancellation
    -- twin of `lockSet_endpointReply`'s member, for the same write, since HP6
    -- makes `spliceThreadReplyFrameOut` a splice.  No default: a call site that
    -- omits it must fail to elaborate.
    (splicedFrameBelowReplyId : Option SeLe4n.ReplyId) : LockSet :=
  lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt
    (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt
    (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt
      (lockSetOfList [(tcbLock victimTid, .write)])
      (blockedEndpointObjId.map (fun ep => (endpointLock ep, .write))))
      (blockedNotificationObjId.map (fun n => (notificationLock n, .write))))
      (consumedReplyId.map (fun r => (replyLock r, .write))))
      -- WS-RR RR7.22 (residual, remediation): the donation the reply arm hands
      -- back is two more writes — the SchedContext's `boundThread` and the
      -- holder's `schedContextBinding` — and a footprint that does not name them
      -- would be *false*, which is worse than a wide one.  Both are `none` on
      -- every arm but a reply arm whose caller had donated.
      (returnedDonationSc.map (fun sc => (schedContextLock sc, .write))))
      (donationHolderTid.map (fun h => (tcbLock h, .write))))
      -- WS-OD OD1.5: the reclaim's abort prefix splices the *holder* out of the
      -- holder's endpoint queue, so the endpoint object and both queue
      -- neighbours are writes too.  All three are `none` unless a donation is
      -- resolved **and** its holder is blocked sending or calling, which is the
      -- abort's own guard; a footprint that omitted them would be false on the
      -- one arm where the abort runs.
      (holderEndpointObjId.map (fun ep => (endpointLock ep, .write))))
      (holderSpliceNeighbors.1.map (fun p => (tcbLock p, .write))))
      (holderSpliceNeighbors.2.map (fun n => (tcbLock n, .write))))
      -- **WS-OD OD3.7**: the two objects the hand-back reaches *below* the
      -- reply-stack head — the Reply one frame down, and that frame's caller's
      -- TCB, which `outerCallerAcceptable` validates before the pop binds it.
      -- **WS-OD (`v0.35.4`)**: the frame below is a **write** — the pop re-heads
      -- it (`storeReplyReHead`, `next := .head scId`); OD3.7 declared it read
      -- when the stack was singly linked and the pop only followed the link.
      -- The outer caller's TCB stays read.  Both are `none` below the first
      -- donating `Call`; load-bearing at depth >= 2 and inert at depth 1.
      (belowHeadReplyId.map (fun r => (replyLock r, AccessMode.write))))
      (outerCallerTid.map (fun ot => (tcbLock ot, AccessMode.read))))
      -- **WS-OD (`v0.35.4`)**: the head the reclaim clears
      -- (`storeDonationHeadClear`, through `storeDonationHeadPop`), resolved
      -- from the returned context rather than assumed to be the consumed reply.
      (reclaimHeadReplyId.map (fun r => (replyLock r, AccessMode.write))))
      -- **WS-OD (`v0.35.4`)**: the frame above the cancelled caller's own,
      -- which `spliceThreadReplyFrameOut` unlinks (`prev := none`) when the
      -- caller is a middle caller of its stack — the write that stops a dead
      -- frame from heading a stack forever.
      (splicedFrameAboveReplyId.map (fun r => (replyLock r, AccessMode.write))))
      -- **WS-HP HP3.1**: and the frame below it, which the splice re-links
      -- upward (`next := .frame above`) in the same step -- the second half of
      -- the removal's write set.
      (splicedFrameBelowReplyId.map (fun r => (replyLock r, AccessMode.write))))
    -- **WS-OD OD3.5**: the reply arm's donation hand-back runs
    -- `returnDonatedSchedContext`, whose last step maintains
    -- `SystemState.scThreadIndex` — an `RHTable` whose insert may rehash and
    -- back-shift the whole table, so it does not decompose by object and its
    -- declared subject is `stateLevelLock` (SM3.A.10).  Conditioned on the
    -- SchedContext member's own resolver, so the two answer one question.
    (if returnedDonationSc.isSome then some (stateLevelLock, AccessMode.write) else none)

/-- WS-SM SM6.E.3 (plan §3.1): the `cancelDonation` lock-set — donor (victim)
TCB (write: binding clear), the bound/donated SchedContext (write:
deactivation / owner re-bind), and the donated-arm original-owner TCB
(write: re-bind to `.bound`).

**WS-OD (`v0.35.4`)**: the donated arm is `returnDonatedSchedContextResolved`
— the reply-stack **pop** — so it writes the stack head it clears and the frame
below it re-heads, and reads the frame below's caller to validate it
(`outerCallerAcceptable`).  Three members the footprint named nowhere while the
arm ran them: `headReplyId` (write), `belowHeadReplyId` (write),
`outerCallerTid` (read).  All three are `none` on the bound arm, which pops
nothing, and on a donated context that heads no stack. -/
def lockSet_cancelDonation (victimTid : SeLe4n.ThreadId)
    (bindingScId : Option SeLe4n.SchedContextId)
    (donatedOriginalOwnerTid : Option SeLe4n.ThreadId)
    (headReplyId : Option SeLe4n.ReplyId)
    (belowHeadReplyId : Option SeLe4n.ReplyId)
    (outerCallerTid : Option SeLe4n.ThreadId) : LockSet :=
  -- **WS-OD OD3.5**: with the state-level lock when a binding is cancelled, for
  -- the reason given at `lockSet_cancelIpcBlocking` — both arms maintain
  -- `SystemState.scThreadIndex`, an `RHTable` that does not decompose by object.
  lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt
    (lockSetExtendOpt
      (lockSetOfList [(tcbLock victimTid, .write)])
      (bindingScId.map (fun sc => (schedContextLock sc, .write))))
      (donatedOriginalOwnerTid.map (fun ot => (tcbLock ot, .write))))
      -- WS-OD (`v0.35.4`): the pop's own three stack objects, in the modes the
      -- pop takes them.
      (headReplyId.map (fun r => (replyLock r, AccessMode.write))))
      (belowHeadReplyId.map (fun r => (replyLock r, AccessMode.write))))
      (outerCallerTid.map (fun ot => (tcbLock ot, AccessMode.read))))
    (if bindingScId.isSome then some (stateLevelLock, AccessMode.write) else none)

/-- **WS-OD OD3.7**: the two objects the reply arm's reclaim reads *below* the
reply-stack head.

`returnDonationToCancelledCaller` hands the victim's donation back through
`returnDonatedSchedContext`, and at call depth ≥ 2 that walks one link past the
head to find the outer caller and then reads that caller's TCB to validate it.
Derived from `cancelledCallerDonation?` — the reclaim's own resolver for *which*
SchedContext is handed back — so the footprint and the operation cannot disagree
about which stack is walked.

Inert on every state this tree reaches (`replyStackBelowHead?_of_no_stack`),
and inert on every arm but the reply arm, since no other arm resolves a
donation. -/
def cancelBelowHeadReads? (st : SystemState) (victimTid : SeLe4n.ThreadId) (tcb : TCB) :
    Option SeLe4n.ReplyId × Option SeLe4n.ThreadId :=
  match (Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb).map Prod.fst with
  | none => (none, none)
  | some scId => replyStackBelowHead? st scId

/-- WS-OD OD3.7: **no donation, nothing below a head.**  The reclaim's two extra
reads exist only on the arm that hands a SchedContext back, so on every other
arm both members are `none` and the extensions reduce definitionally. -/
@[simp] theorem cancelBelowHeadReads?_of_no_donation (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB)
    (h : Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb = none) :
    cancelBelowHeadReads? st victimTid tcb = (none, none) := by
  unfold cancelBelowHeadReads?
  rw [h]
  rfl

/-- WS-OD (`v0.35.4`): on a resolved donation the two below-head members **are**
the reply-stack resolver's answer on the returned context — one question, one
answer, stated so a consumer can move between the two spellings. -/
theorem cancelBelowHeadReads?_of_donation (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (holder : SeLe4n.ThreadId)
    (h : Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb = some (scId, holder)) :
    cancelBelowHeadReads? st victimTid tcb = replyStackBelowHead? st scId := by
  unfold cancelBelowHeadReads?
  rw [h]
  rfl

/-- **WS-OD (`v0.35.4`)**: the **head** of the returned context's reply stack —
the frame the reclaim's pop clears (`storeDonationHeadPop` →
`storeDonationHeadClear`).  Derived from `cancelledCallerDonation?`, the reclaim's
own resolver for *which* context is handed back, through the same
`replyStackHead?` every push and pop footprint reads the head with.

It **is** the cancelled caller's own reply object — the frame its `Call` pushed —
so it merges with `cancelConsumedReply?` by key.  Until WS-HP HP5.1 that was a
claim about reachable states; the head-driven trigger makes it a theorem
(`cancelReclaimHead?_eq_replyObject`), because the resolver reaches the context
*through* that frame and `replyFrameHeadContext?` validates the context's `scReply`
against it.  The member is still declared on its own, because the pop writes
whatever the context's `scReply` names and a footprint is the union over all
argument values, not over the states an invariant admits. -/
def cancelReclaimHead? (st : SystemState) (victimTid : SeLe4n.ThreadId) (tcb : TCB) :
    Option SeLe4n.ReplyId :=
  ((Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb).map Prod.fst).bind
    (replyStackHead? st)

/-- WS-OD (`v0.35.4`): no donation, no head to clear. -/
@[simp] theorem cancelReclaimHead?_of_no_donation (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB)
    (h : Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb = none) :
    cancelReclaimHead? st victimTid tcb = none := by
  unfold cancelReclaimHead?
  rw [h]
  rfl

/-- WS-OD (`v0.35.4`): and on a resolved donation it is the head of the returned
context's stack. -/
theorem cancelReclaimHead?_of_donation (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (holder : SeLe4n.ThreadId)
    (h : Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb = some (scId, holder)) :
    cancelReclaimHead? st victimTid tcb = replyStackHead? st scId := by
  unfold cancelReclaimHead?
  rw [h]
  rfl

/-- **WS-HP HP5.4: the head the reclaim's pop clears is the cancelled caller's own
reply object** — a theorem of the head-driven trigger, where it used to be a
sentence about the states `ipcInvariantFull` admits.

This is the content of the retired `replyStackHeadIsAnsweredReply` seen from the
cancellation end — that predicate was **deleted** at WS-HP HP7 (`v0.35.46`), having
become a *theorem* on both paths rather than a hypothesis — and it holds for the
same reason HP2.4's reply-side twin
(`answeredFrameHeadContext?_head_is_answered_reply`) does: the resolver reaches
the context *through* the victim's frame, and `replyFrameHeadContext?` accepts the
`.head` link only when the context's own `scReply` names that frame back.  So the
two footprint members `cancelReclaimHead?` and `cancelConsumedReply?` provably
carry the same key, rather than doing so on every state somebody has checked.

The binding-driven reclaim could not state this at all: it reached the context out
of the holder's stored binding, which says nothing about any reply object. -/
theorem cancelReclaimHead?_eq_replyObject (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (holder : SeLe4n.ThreadId)
    (h : Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb = some (scId, holder)) :
    cancelReclaimHead? st victimTid tcb = tcb.replyObject := by
  rw [cancelReclaimHead?_of_donation st victimTid tcb scId holder h]
  -- Unfolded here rather than through `cancelledCallerDonation?_some`, which lives
  -- in a module downstream of this one; the two extract the same three facts.
  unfold Lifecycle.Suspend.cancelledCallerDonation? at h
  cases hIpc : tcb.ipcState with
  | blockedOnReply ep rt =>
    rw [hIpc] at h
    cases hRO : tcb.replyObject with
    | none => rw [hRO] at h; cases h
    | some rid =>
      rw [hRO] at h
      obtain ⟨hHead, _⟩ := replyFrameHeadHolder?_eq_some h
      obtain ⟨_, sc, _, _, hSc, hRec⟩ := replyFrameHeadContext?_eq_some hHead
      unfold replyStackHead?
      rw [hSc]
      simpa using hRec
  | _ => rw [hIpc] at h; cases h

/-- **WS-OD (`v0.35.4`)**: the **frame above the cancelled caller's own** — the
Reply `spliceThreadReplyFrameOut` rewrites when the caller is a *middle* caller of
its stack (`prev := some below` since WS-HP HP6.3, so that the frame above links
down past the cut; `prev := none` at a bottom frame, where nothing lies below),
and the cancelled frame leaves the structure when its caller link is consumed.
Keyed on the reply arm, since only that arm splices, and resolved
through `replyFrameAbove?` — the same two fields the splice reads
(`replyFrameAbove?_of_splice_store` ties the member to the store).

`none` for a head frame (`next = .head _`): a head is popped by the reclaim, never
detached, so this member and `cancelReclaimHead?` are never both `some` — since
WS-HP HP5.4 a theorem (`cancelSplicedFrameAbove?_of_donation`) rather than an
observation about reachable states.  The footprint declares them independently
because it does not get to assume that. -/
def cancelSplicedFrameAbove? (st : SystemState) (tcb : TCB) : Option SeLe4n.ReplyId :=
  match tcb.ipcState with
  | .blockedOnReply _ _ => tcb.replyObject.bind (replyFrameAbove? st)
  | _ => none

/-- **WS-HP HP3.1**: the frame **below** the cancelled caller's own -- the second
Reply the removal writes; declared at HP3 ahead of HP6.3 (`v0.35.45`), the cut
that made the cancellation's removal a splice.

Derived from `cancelSplicedFrameAbove?`'s own two inputs -- the reply arm and the
victim's `replyObject` -- composed with `replyFrameBelow?`, which is itself
`replyFrameAbove?` plus the cut frame's `prev`.  So "is this a splice at all" is
answered once for the footprint, the splice resolver and the operation.

`none` on every arm but the reply arm, `none` for a head frame (a head is popped,
never spliced) and `none` for a frame with nothing above it. -/
def cancelSplicedFrameBelow? (st : SystemState) (tcb : TCB) : Option SeLe4n.ReplyId :=
  match tcb.ipcState with
  | .blockedOnReply _ _ => tcb.replyObject.bind (replyFrameBelow? st)
  | _ => none

/-- **WS-HP HP5.4: a reclaim and a removal are structurally exclusive** — the pop
clears a head, the splice rewrites a frame above one, and no frame is both.

Under the head-driven trigger this is a theorem rather than a sentence about the
states the invariants admit.  The reclaim resolves a context only through the
victim's own frame's `.head` link, and a frame that heads a context has no frame
above it (`replyFrameAbove?_of_headContext`, HP1.2's "a frame with a frame above it
heads nothing" read the other way) — so on any state where the reclaim fires, both
removal members are `none`, and the *reachable* cancellation footprint stays below
the ceiling the members raise between them.

The binding-driven reclaim could not state this: it reached the context out of the
holder's stored binding, which relates to no reply frame at all, so "never both
`some`" was an observation about the fixtures.  The footprint still declares the
members independently, because it is the union over all argument values rather than
over the states a theorem covers. -/
theorem cancelSplicedFrameAbove?_of_donation (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (holder : SeLe4n.ThreadId)
    (h : Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb = some (scId, holder)) :
    cancelSplicedFrameAbove? st tcb = none := by
  unfold cancelSplicedFrameAbove?
  unfold Lifecycle.Suspend.cancelledCallerDonation? at h
  cases hIpc : tcb.ipcState with
  | blockedOnReply ep rt =>
    rw [hIpc] at h
    cases hRO : tcb.replyObject with
    | none => rw [hRO] at h; cases h
    | some rid =>
      rw [hRO] at h
      obtain ⟨hHead, _⟩ := replyFrameHeadHolder?_eq_some h
      simpa using replyFrameAbove?_of_headContext st rid scId hHead
  -- Every other arm returns `none` outright, so the member agrees with no appeal
  -- to the resolved donation.
  | _ => rfl

/-- **WS-HP HP5.4**: and so is the splice's frame below, which composes the same
`replyFrameAbove?` (`replyFrameBelow?_of_headContext`).  Stated beside its sibling
rather than derived from it, because the two members read different fields and a
consumer of one should not have to unfold the other. -/
theorem cancelSplicedFrameBelow?_of_donation (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (holder : SeLe4n.ThreadId)
    (h : Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb = some (scId, holder)) :
    cancelSplicedFrameBelow? st tcb = none := by
  unfold cancelSplicedFrameBelow?
  unfold Lifecycle.Suspend.cancelledCallerDonation? at h
  cases hIpc : tcb.ipcState with
  | blockedOnReply ep rt =>
    rw [hIpc] at h
    cases hRO : tcb.replyObject with
    | none => rw [hRO] at h; cases h
    | some rid =>
      rw [hRO] at h
      obtain ⟨hHead, _⟩ := replyFrameHeadHolder?_eq_some h
      simpa using replyFrameBelow?_of_headContext st rid scId hHead
  -- Every other arm returns `none` outright, so the member agrees with no appeal
  -- to the resolved donation.
  | _ => rfl

/-- WS-HP HP3.1: the endpoint arms splice nothing. -/
@[simp] theorem cancelSplicedFrameBelow?_of_blockedEndpoint (st : SystemState) (tcb : TCB)
    (ep : SeLe4n.ObjId) (h : cancelBlockedEndpoint? tcb = some ep) :
    cancelSplicedFrameBelow? st tcb = none := by
  unfold cancelBlockedEndpoint? at h
  unfold cancelSplicedFrameBelow?
  cases hIp : tcb.ipcState <;> simp_all

/-- WS-HP HP3.1: nor does the notification arm. -/
@[simp] theorem cancelSplicedFrameBelow?_of_blockedNotification (st : SystemState) (tcb : TCB)
    (n : SeLe4n.ObjId) (h : cancelBlockedNotification? tcb = some n) :
    cancelSplicedFrameBelow? st tcb = none := by
  unfold cancelBlockedNotification? at h
  unfold cancelSplicedFrameBelow?
  cases hIp : tcb.ipcState <;> simp_all

/-- **WS-HP HP3.1**: and no frame above means no frame below -- the exclusion that
keeps the cancellation's reply-arm bound where it was, and which needs no
invariant: the splice's member is declared only on a *mid-stack* removal. -/
@[simp] theorem cancelSplicedFrameBelow?_of_no_frameAbove (st : SystemState) (tcb : TCB)
    (h : cancelSplicedFrameAbove? st tcb = none) :
    cancelSplicedFrameBelow? st tcb = none := by
  unfold cancelSplicedFrameBelow?
  unfold cancelSplicedFrameAbove? at h
  cases hIp : tcb.ipcState with
  | blockedOnReply ep rt =>
    rw [hIp] at h
    cases hRO : tcb.replyObject with
    | none => rfl
    | some rid =>
      rw [hRO] at h
      exact replyFrameBelow?_of_no_frame_above st rid h
  | _ => rfl

/-- **WS-HP HP6.6: the cancellation path's lifting of the containment** -- the
frame the victim's removal splices below the cut is the one this arm's footprint
declares.

Lifted through the victim's own `replyObject` under the reply-arm gate, which is
where `cancelSplicedFrameBelow?` reads it, so the footprint and the operation
cannot disagree about which frame is cut.  The `.blockedOnReply` gate is the arm
selector every exclusivity lemma in this family reads; on any other arm the
declared member is `none` and the removal is the identity, so there is nothing to
contain. -/
theorem spliceFrameBelow?_mem_cancelSplicedFrameBelow? (st : SystemState) (tcb : TCB)
    (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId)
    (rid above below : SeLe4n.ReplyId) (r b : Reply)
    (hIp : tcb.ipcState = .blockedOnReply ep rt)
    (hRO : tcb.replyObject = some rid)
    (hR : st.getReply? rid = some r)
    (hAbove : replyFrameAbove? st rid = some above)
    (h : spliceFrameBelow? st rid r above = some (below, b)) :
    cancelSplicedFrameBelow? st tcb = some below := by
  unfold cancelSplicedFrameBelow?
  rw [hIp, hRO]
  exact spliceFrameBelow?_mem_replyFrameBelow? hR hAbove h

/-- WS-OD (`v0.35.4`): the endpoint arms splice nothing. -/
@[simp] theorem cancelSplicedFrameAbove?_of_blockedEndpoint (st : SystemState) (tcb : TCB)
    (ep : SeLe4n.ObjId) (h : cancelBlockedEndpoint? tcb = some ep) :
    cancelSplicedFrameAbove? st tcb = none := by
  unfold cancelBlockedEndpoint? at h
  unfold cancelSplicedFrameAbove?
  cases hIp : tcb.ipcState <;> simp_all

/-- WS-OD (`v0.35.4`): nor does the notification arm. -/
@[simp] theorem cancelSplicedFrameAbove?_of_blockedNotification (st : SystemState) (tcb : TCB)
    (n : SeLe4n.ObjId) (h : cancelBlockedNotification? tcb = some n) :
    cancelSplicedFrameAbove? st tcb = none := by
  unfold cancelBlockedNotification? at h
  unfold cancelSplicedFrameAbove?
  cases hIp : tcb.ipcState <;> simp_all

/-- WS-OD (`v0.35.4`): a resolved donation witnesses a `.blockedOnReply` victim —
the shape fact every arm-exclusivity argument below rests on, stated once. -/
theorem cancelledCallerDonation?_some_blockedOnReply
    {st : SystemState} {tid : SeLe4n.ThreadId} {tcb : TCB}
    {scId : SeLe4n.SchedContextId} {holder : SeLe4n.ThreadId}
    (h : Lifecycle.Suspend.cancelledCallerDonation? st tid tcb = some (scId, holder)) :
    ∃ ep rt, tcb.ipcState = .blockedOnReply ep rt := by
  unfold Lifecycle.Suspend.cancelledCallerDonation? at h
  repeat' split at h
  all_goals simp_all

/-- WS-OD (`v0.35.4`): and conversely, an endpoint-blocked victim resolves no
donation — the reclaim is a reply-arm fact. -/
theorem cancelledCallerDonation?_of_blockedEndpoint (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (ep : SeLe4n.ObjId)
    (h : cancelBlockedEndpoint? tcb = some ep) :
    Lifecycle.Suspend.cancelledCallerDonation? st tid tcb = none := by
  unfold cancelBlockedEndpoint? at h
  unfold Lifecycle.Suspend.cancelledCallerDonation?
  cases hIp : tcb.ipcState <;> simp_all

/-- WS-OD (`v0.35.4`): nor does a notification-blocked one. -/
theorem cancelledCallerDonation?_of_blockedNotification (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (n : SeLe4n.ObjId)
    (h : cancelBlockedNotification? tcb = some n) :
    Lifecycle.Suspend.cancelledCallerDonation? st tid tcb = none := by
  unfold cancelBlockedNotification? at h
  unfold Lifecycle.Suspend.cancelledCallerDonation?
  cases hIp : tcb.ipcState <;> simp_all

/-- WS-SM SM6.E.1: the concrete lock-set a cross-core `cancelIpcBlockingOnCore`
on state `st` acquires — the parametric footprint with the blocked-on object
and consumed reply pre-resolved from the victim's TCB.  This is the footprint
the runtime `withLockSet` bracket acquires before invoking the cancellation.

**WS-OD OD3.5 — arm-selected, not summed.**  Every member is now resolved
through a predicate that keys on the victim's `ipcState`, so the set a given
cancellation declares is the set that arm writes:

* endpoint arm (`.blockedOnSend` / `.blockedOnReceive` / `.blockedOnCall`) —
  the victim, the endpoint and the two neighbours its splice relinks: **four**;
* notification arm — the victim and the notification: **two**;
* reply arm — the victim, its consumed Reply, the returned SchedContext, the
  donation holder, and the holder's endpoint plus *its* two splice neighbours:
  **seven**;
* `.ready` — the victim alone, and the operation commits no write at all.

The victim's own neighbours used to be appended unconditionally, which put two
TCB write locks on the reply arm for a splice that arm does not perform and
took it to nine of nine.  See `cancelArmSpliceNeighbors?` for why widening a
footprint is sound but not free. -/
def lockSet_cancelIpcBlockingOnCore (st : SystemState)
    (victimTid : SeLe4n.ThreadId) : LockSet :=
  match st.getTcb? victimTid with
  | some tcb =>
      -- PR #831 review 4: the splice's neighbour-TCB writes (`queuePrev`'s
      -- `queueNext` patch + `queueNext`'s `queuePrev` patch) are footprint
      -- members, resolved from the victim's interior links.
      lockSetExtendOpt
        (lockSetExtendOpt
          (lockSet_cancelIpcBlocking victimTid (cancelBlockedEndpoint? tcb)
            (cancelBlockedNotification? tcb) (cancelConsumedReply? tcb)
            ((Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb).map Prod.fst)
            ((Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb).map Prod.snd)
            (cancelHolderBlockedEndpoint? st
              ((Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb).map Prod.snd))
            (cancelHolderSpliceNeighbors? st
              ((Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb).map Prod.snd))
            -- **WS-OD OD3.7**: the two below-head reads, resolved through the
            -- same resolver the reply and replyRecv arms use, on the very
            -- SchedContext this reclaim hands back.  One question, one answer.
            (cancelBelowHeadReads? st victimTid tcb).1
            (cancelBelowHeadReads? st victimTid tcb).2
            -- **WS-OD (`v0.35.4`)**: the head the reclaim clears and the frame
            -- above the cancelled caller's own, which the splice rewrites --
            -- each through the resolver it is derived from.
            (cancelReclaimHead? st victimTid tcb)
            (cancelSplicedFrameAbove? st tcb)
            -- **WS-HP HP3.1**: and the frame below the cut, which the splice
            -- re-links upward.  Derived from `cancelSplicedFrameAbove?`'s own
            -- resolver, so the two cannot disagree about which arm removes.
            (cancelSplicedFrameBelow? st tcb))
          -- WS-OD OD3.5: the *arm-selected* neighbours, not the summed pair.
          -- Only the endpoint arm splices, so on the reply, notification and
          -- `.ready` arms these two extensions are `none` and the footprint
          -- stops declaring write locks on threads the operation never touches.
          ((cancelArmSpliceNeighbors? tcb).1.map (fun p => (tcbLock p, .write))))
        ((cancelArmSpliceNeighbors? tcb).2.map (fun n => (tcbLock n, .write)))
  | none =>
      lockSet_cancelIpcBlocking victimTid none none none none none none (none, none) none none
        none none none

/-- **WS-OD OD3.5: the reply arm's resolved footprint has no neighbour members
at all.**

Stated as an equation rather than as a `∉`, because a `∉` would be false for an
accidental reason — the victim's `queuePrev` could happen to *be* the donation
holder, which the footprint declares on its own account.  The equation says the
right thing: on a `.blockedOnReply` victim the resolved set **is** the parametric
footprint at the reply arm's arguments, with the two neighbour extensions gone
rather than merged away.

That is sound because the arm relinks nothing:
`cancelIpcBlocking_replyArm_noDonation_tcb_frame`
(`Lifecycle/Invariant/CancellationReplyShape.lean`) checks it on the shape where
the reclaim is inert, and where a donation is resolved the arm's extra writes
land on the holder, its endpoint and *its* two neighbours — all four declared
here since OD1.5. -/
theorem lockSet_cancelIpcBlockingOnCore_replyArm_eq (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB) (ep : SeLe4n.ObjId)
    (rt : Option SeLe4n.ThreadId)
    (hT : st.getTcb? victimTid = some tcb)
    (hIp : tcb.ipcState = .blockedOnReply ep rt) :
    lockSet_cancelIpcBlockingOnCore st victimTid
      = lockSet_cancelIpcBlocking victimTid none none (cancelConsumedReply? tcb)
          ((Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb).map Prod.fst)
          ((Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb).map Prod.snd)
          (cancelHolderBlockedEndpoint? st
            ((Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb).map Prod.snd))
          (cancelHolderSpliceNeighbors? st
            ((Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb).map Prod.snd))
          (cancelBelowHeadReads? st victimTid tcb).1
          (cancelBelowHeadReads? st victimTid tcb).2
          (cancelReclaimHead? st victimTid tcb)
          (cancelSplicedFrameAbove? st tcb)
          (cancelSplicedFrameBelow? st tcb) := by
  have hE : cancelBlockedEndpoint? tcb = none := by
    unfold cancelBlockedEndpoint?; rw [hIp]
  have hN : cancelBlockedNotification? tcb = none := by
    unfold cancelBlockedNotification?; rw [hIp]
  unfold lockSet_cancelIpcBlockingOnCore
  rw [hT]
  simp only [hE, hN, cancelArmSpliceNeighbors?_of_not_blockedEndpoint tcb hE,
    Option.map_none, lockSetExtendOpt]

/-- **WS-OD OD3.5**: …and the arm that *does* splice keeps both members.  The
narrowing is a change of *which arm* declares them, not a removal: on an
endpoint-blocked victim the predecessor's TCB write lock is still there. -/
theorem lockSet_cancelIpcBlockingOnCore_endpointArm_covers_prev (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB) (ep : SeLe4n.ObjId) (p : SeLe4n.ThreadId)
    (hT : st.getTcb? victimTid = some tcb)
    (hE : cancelBlockedEndpoint? tcb = some ep)
    (hPrev : tcb.queuePrev = some p) :
    (tcbLock p, AccessMode.write) ∈ (lockSet_cancelIpcBlockingOnCore st victimTid).pairs := by
  unfold lockSet_cancelIpcBlockingOnCore
  rw [hT]
  simp only [cancelArmSpliceNeighbors?_of_blockedEndpoint tcb ep hE, queueSpliceNeighbors?,
    hPrev]
  exact mem_write_lockSetExtendOpt _ _ _ (LockSet.mem_insertOrMerge_write_self _ _)

/-- **WS-OD OD3.5**: and the successor's. -/
theorem lockSet_cancelIpcBlockingOnCore_endpointArm_covers_next (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB) (ep : SeLe4n.ObjId) (n : SeLe4n.ThreadId)
    (hT : st.getTcb? victimTid = some tcb)
    (hE : cancelBlockedEndpoint? tcb = some ep)
    (hNext : tcb.queueNext = some n) :
    (tcbLock n, AccessMode.write) ∈ (lockSet_cancelIpcBlockingOnCore st victimTid).pairs := by
  unfold lockSet_cancelIpcBlockingOnCore
  rw [hT]
  simp only [cancelArmSpliceNeighbors?_of_blockedEndpoint tcb ep hE, queueSpliceNeighbors?,
    hNext]
  exact LockSet.mem_insertOrMerge_write_self _ _

/-- **WS-OD (`v0.35.4`)**: the three reply-stack objects the donated arm's pop
touches — the head it clears, the frame below it re-heads, and that frame's
caller it validates — resolved from the victim's own `.donated` binding through
the stack resolvers the pop reads.  `(none, none, none)` on every other binding:
the bound arm pops nothing. -/
def cancelDonationPopMembers? (st : SystemState) (tcb : TCB) :
    Option SeLe4n.ReplyId × Option SeLe4n.ReplyId × Option SeLe4n.ThreadId :=
  match tcb.schedContextBinding with
  | .donated scId _ =>
      (replyStackHead? st scId, (replyStackBelowHead? st scId).1,
       (replyStackBelowHead? st scId).2)
  | _ => (none, none, none)

/-- WS-OD (`v0.35.4`): the bound arm pops nothing. -/
@[simp] theorem cancelDonationPopMembers?_of_bound (st : SystemState) (tcb : TCB)
    (scId : SeLe4n.SchedContextId) (h : tcb.schedContextBinding = .bound scId) :
    cancelDonationPopMembers? st tcb = (none, none, none) := by
  unfold cancelDonationPopMembers?; rw [h]

/-- WS-OD (`v0.35.4`): nor does an unbound victim. -/
@[simp] theorem cancelDonationPopMembers?_of_unbound (st : SystemState) (tcb : TCB)
    (h : tcb.schedContextBinding = .unbound) :
    cancelDonationPopMembers? st tcb = (none, none, none) := by
  unfold cancelDonationPopMembers?; rw [h]

/-- WS-OD (`v0.35.4`): and the donated arm's three are the stack resolvers'
answers on its own context. -/
theorem cancelDonationPopMembers?_of_donated (st : SystemState) (tcb : TCB)
    (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId)
    (h : tcb.schedContextBinding = .donated scId owner) :
    cancelDonationPopMembers? st tcb
      = (replyStackHead? st scId, (replyStackBelowHead? st scId).1,
         (replyStackBelowHead? st scId).2) := by
  unfold cancelDonationPopMembers?; rw [h]

/-- WS-SM SM6.E.3: the concrete lock-set a `cancelDonationOnCore` on state
`st` acquires — the parametric footprint with the SC and donated owner
pre-resolved from the victim's TCB, and (WS-OD `v0.35.4`) the donated arm's
pop members resolved from the same binding. -/
def lockSet_cancelDonationOnCore (st : SystemState)
    (victimTid : SeLe4n.ThreadId) : LockSet :=
  match st.getTcb? victimTid with
  | some tcb =>
      lockSet_cancelDonation victimTid (cancelBindingSc? tcb)
        (cancelDonatedOwner? tcb)
        (cancelDonationPopMembers? st tcb).1
        (cancelDonationPopMembers? st tcb).2.1
        (cancelDonationPopMembers? st tcb).2.2
  | none => lockSet_cancelDonation victimTid none none none none none

-- ============================================================================
-- §6  Lock-set hierarchical correctness (SM3.B.4 discipline)
-- ============================================================================

/-- WS-SM SM6.E.1: every lock the `cancelIpcBlocking` footprint declares has a
kind permitted for the enclosing `.tcbSuspend` syscall (the cancellation runs
inside the suspend dispatch), so the acquisitions respect the SM0.I lock
ladder. -/
theorem lockSet_consistent_cancelIpcBlocking (victimTid : SeLe4n.ThreadId)
    (blEp blN : Option SeLe4n.ObjId) (consumedReplyId : Option SeLe4n.ReplyId)
    (returnedDonationSc : Option SeLe4n.SchedContextId)
    (donationHolderTid : Option SeLe4n.ThreadId)
    (holderEndpointObjId : Option SeLe4n.ObjId)
    (holderSpliceNeighbors : Option SeLe4n.ThreadId × Option SeLe4n.ThreadId)
    -- WS-OD OD3.7: the two below-head objects the reclaim reaches at depth ≥ 2.
    (belowHeadReplyId : Option SeLe4n.ReplyId)
    (outerCallerTid : Option SeLe4n.ThreadId)
    -- WS-OD (`v0.35.4`): the head the reclaim clears and the frame the splice
    -- rewrites.
    (reclaimHeadReplyId splicedFrameAboveReplyId : Option SeLe4n.ReplyId)
    -- **WS-HP HP3.1**: and the frame below the cut, which the splice re-links.
    (splicedFrameBelowReplyId : Option SeLe4n.ReplyId) :
    ∀ p ∈ (lockSet_cancelIpcBlocking victimTid blEp blN consumedReplyId
        returnedDonationSc donationHolderTid holderEndpointObjId holderSpliceNeighbors
        belowHeadReplyId outerCallerTid reclaimHeadReplyId splicedFrameAboveReplyId
        splicedFrameBelowReplyId).pairs,
      p.fst.kind ∈ permittedKinds .tcbSuspend :=
  lockSet_consistent_base_plus_fourteen_opts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
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
    (by intro pp hpp
        cases returnedDonationSc with
        | none => simp at hpp
        | some sc => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases donationHolderTid with
        | none => simp at hpp
        | some h => simp at hpp; rw [← hpp]; simp; decide)
    -- WS-OD OD1.5: the abort prefix's three members are an endpoint and two
    -- TCBs, all three already permitted kinds for the enclosing `.tcbSuspend`.
    (by intro pp hpp
        cases holderEndpointObjId with
        | none => simp at hpp
        | some ep => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases hN1 : holderSpliceNeighbors.1 with
        | none => rw [hN1] at hpp; simp at hpp
        | some p => rw [hN1] at hpp; simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases hN2 : holderSpliceNeighbors.2 with
        | none => rw [hN2] at hpp; simp at hpp
        | some n => rw [hN2] at hpp; simp at hpp; rw [← hpp]; simp; decide)
    -- WS-OD OD3.7: the Reply one frame below the stack head, and that frame's
    -- caller's TCB — both kinds `.tcbSuspend` already admits, so the ladder is
    -- unchanged (the mode is not the ladder's business).
    (by intro pp hpp
        cases belowHeadReplyId with
        | none => simp at hpp
        | some r => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases outerCallerTid with
        | none => simp at hpp
        | some ot => simp at hpp; rw [← hpp]; simp; decide)
    -- WS-OD (`v0.35.4`): two more Reply-kind members — the head the reclaim
    -- clears and the frame the splice rewrites.
    (by intro pp hpp
        cases reclaimHeadReplyId with
        | none => simp at hpp
        | some r => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases splicedFrameAboveReplyId with
        | none => simp at hpp
        | some r => simp at hpp; rw [← hpp]; simp; decide)
    -- **WS-HP HP3.1**: and one more Reply-kind member — the frame below the cut.
    (by intro pp hpp
        cases splicedFrameBelowReplyId with
        | none => simp at hpp
        | some r => simp at hpp; rw [← hpp]; simp; decide)
    -- WS-OD OD3.5: the state-level lock, taken when the reply arm hands a
    -- donation back and maintains `scThreadIndex` with it.
    (by intro pp hpp
        cases returnedDonationSc with
        | none => simp at hpp
        | some _ => simp at hpp; rw [← hpp]; simp [stateLevelLock]; decide)

/-- WS-SM SM6.E.3: every lock the `cancelDonation` footprint declares has a
kind permitted for the enclosing `.tcbSuspend` syscall. -/
theorem lockSet_consistent_cancelDonation (victimTid : SeLe4n.ThreadId)
    (bindingScId : Option SeLe4n.SchedContextId)
    (donatedOriginalOwnerTid : Option SeLe4n.ThreadId)
    -- WS-OD (`v0.35.4`): at the pop's arity.
    (headReplyId belowHeadReplyId : Option SeLe4n.ReplyId)
    (outerCallerTid : Option SeLe4n.ThreadId) :
    ∀ p ∈ (lockSet_cancelDonation victimTid bindingScId donatedOriginalOwnerTid
        headReplyId belowHeadReplyId outerCallerTid).pairs,
      p.fst.kind ∈ permittedKinds .tcbSuspend :=
  lockSet_consistent_base_plus_six_opts _ _ _ _ _ _ _ _
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
    -- WS-OD (`v0.35.4`): the pop's two Reply writes and its TCB read — kinds
    -- `.tcbSuspend` already admits.
    (by intro pp hpp
        cases headReplyId with
        | none => simp at hpp
        | some r => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases belowHeadReplyId with
        | none => simp at hpp
        | some r => simp at hpp; rw [← hpp]; simp; decide)
    (by intro pp hpp
        cases outerCallerTid with
        | none => simp at hpp
        | some ot => simp at hpp; rw [← hpp]; simp; decide)
    -- WS-OD OD3.5: the donation cancellation's `scThreadIndex` write.
    (by intro pp hpp
        cases bindingScId with
        | none => simp at hpp
        | some _ => simp at hpp; rw [← hpp]; simp [stateLevelLock]; decide)

/-- WS-SM SM6.E.2: the `cancelIpcBlocking` lock-set is **hierarchically
correct** — every declared lock has a permitted kind and the keys are
duplicate-free (the SM3.B well-formedness `LockSet` carries by construction).
Together these are the structural soundness conditions the deadlock-freedom
theorem (2.1.9) and the 2PL serializability corollary (2.1.11) consume. -/
theorem cancelIpcBlockingOnCore_lockSet_correct (victimTid : SeLe4n.ThreadId)
    (blEp blN : Option SeLe4n.ObjId) (consumedReplyId : Option SeLe4n.ReplyId)
    (rdSc : Option SeLe4n.SchedContextId) (dhTid : Option SeLe4n.ThreadId)
    (holderEp : Option SeLe4n.ObjId)
    (holderNb : Option SeLe4n.ThreadId × Option SeLe4n.ThreadId)
    -- WS-OD OD3.7: the two below-head objects the reclaim reaches at depth ≥ 2.
    (belowHeadReply? : Option SeLe4n.ReplyId) (outerCaller? : Option SeLe4n.ThreadId)
    -- WS-OD (`v0.35.4`): the reclaimed head and the detached frame above.
    (reclaimHead? frameAbove? : Option SeLe4n.ReplyId)
    -- **WS-HP HP3.1**: the frame below the cut, which the splice re-links.
    (splicedBelow? : Option SeLe4n.ReplyId) :
    (∀ p ∈ (lockSet_cancelIpcBlocking victimTid blEp blN consumedReplyId rdSc dhTid holderEp
              holderNb belowHeadReply? outerCaller? reclaimHead? frameAbove? splicedBelow?).pairs,
        p.fst.kind ∈ permittedKinds .tcbSuspend) ∧
    ((lockSet_cancelIpcBlocking victimTid blEp blN consumedReplyId rdSc dhTid holderEp
        holderNb belowHeadReply? outerCaller? reclaimHead? frameAbove? splicedBelow?).pairs.map
        (·.fst)).Nodup :=
  ⟨lockSet_consistent_cancelIpcBlocking victimTid blEp blN consumedReplyId rdSc dhTid
      holderEp holderNb belowHeadReply? outerCaller? reclaimHead? frameAbove? splicedBelow?,
   (lockSet_cancelIpcBlocking victimTid blEp blN consumedReplyId rdSc dhTid holderEp
      holderNb belowHeadReply? outerCaller? reclaimHead? frameAbove? splicedBelow?).hUniqueKeys⟩

/-- WS-SM SM6.E.4: the `cancelDonation` lock-set is hierarchically correct. -/
theorem cancelDonationOnCore_lockSet_correct (victimTid : SeLe4n.ThreadId)
    (bindingScId : Option SeLe4n.SchedContextId)
    (donatedOriginalOwnerTid : Option SeLe4n.ThreadId)
    -- WS-OD (`v0.35.4`): at the pop's arity.
    (headReplyId belowHeadReplyId : Option SeLe4n.ReplyId)
    (outerCallerTid : Option SeLe4n.ThreadId) :
    (∀ p ∈ (lockSet_cancelDonation victimTid bindingScId donatedOriginalOwnerTid
              headReplyId belowHeadReplyId outerCallerTid).pairs,
        p.fst.kind ∈ permittedKinds .tcbSuspend) ∧
    ((lockSet_cancelDonation victimTid bindingScId donatedOriginalOwnerTid
        headReplyId belowHeadReplyId outerCallerTid).pairs.map
        (·.fst)).Nodup :=
  ⟨lockSet_consistent_cancelDonation victimTid bindingScId donatedOriginalOwnerTid
      headReplyId belowHeadReplyId outerCallerTid,
   (lockSet_cancelDonation victimTid bindingScId donatedOriginalOwnerTid
      headReplyId belowHeadReplyId outerCallerTid).hUniqueKeys⟩

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
      -- PR #831 review 4: the two neighbour-TCB extensions are `.tcb`-kind
      -- writes, already permitted for `.tcbSuspend`.
      refine lockSet_consistent_extendOpt _ _ _
        (lockSet_consistent_extendOpt _ _ _
          (lockSet_consistent_cancelIpcBlocking victimTid _ _ _ _ _ _ _ _ _ _ _ _) ?_) ?_
      · intro pp hEq
        cases h1 : (cancelArmSpliceNeighbors? tcb).1 with
        | none => rw [h1] at hEq; cases hEq
        | some n =>
          rw [h1] at hEq
          injection hEq with h
          rw [← h]
          show (tcbLock n).kind ∈ permittedKinds .tcbSuspend
          rw [tcbLock_kind]; decide
      · intro pp hEq
        cases h2 : (cancelArmSpliceNeighbors? tcb).2 with
        | none => rw [h2] at hEq; cases hEq
        | some n =>
          rw [h2] at hEq
          injection hEq with h
          rw [← h]
          show (tcbLock n).kind ∈ permittedKinds .tcbSuspend
          rw [tcbLock_kind]; decide
  | none =>
      exact lockSet_consistent_cancelIpcBlocking victimTid none none none none none none
        (none, none) none none none none none

/-- WS-SM SM6.E.3: the state-resolved donation-cancellation lock-set is
hierarchically correct. -/
theorem lockSet_cancelDonationOnCore_correct (st : SystemState)
    (victimTid : SeLe4n.ThreadId) :
    ∀ p ∈ (lockSet_cancelDonationOnCore st victimTid).pairs,
      p.fst.kind ∈ permittedKinds .tcbSuspend := by
  unfold lockSet_cancelDonationOnCore
  cases st.getTcb? victimTid with
  | some tcb => exact lockSet_consistent_cancelDonation victimTid _ _ _ _ _
  | none => exact lockSet_consistent_cancelDonation victimTid none none none none none

-- ============================================================================
-- §7  Write coverage — every cancellation write is under a declared write lock
-- ============================================================================

-- The mode-aware membership helpers `mem_insertOrMerge_write_of_mem_write`
-- (`Concurrency/Locks/LockSet.lean`, next to `mem_insertOrMerge_of_mem_of_ne`)
-- and `mem_write_lockSetExtendOpt` (`Concurrency/Locks/LockSetTransitions.lean`,
-- next to `lockSetExtendOpt`) live with the generic `LockSet` algebra they
-- belong to; the coverage families below consume them.

-- The member is introduced by an extension, so the layer count is EXACT rather
-- than `repeat`: peeling one layer too many discards the very lock being proved
-- present.  Tower, innermost first: the victim's TCB; the blocked endpoint; the
-- blocked notification; the consumed Reply; the returned SchedContext; the
-- donation holder; the holder's endpoint and its two splice neighbours (WS-OD
-- OD1.5); the frame below the reply-stack head and the outer caller (WS-OD
-- OD3.7); the reclaimed head and the detached frame above (WS-OD `v0.35.4`);
-- and the state-level lock (WS-OD OD3.5) outermost -- thirteen extensions.

/-- WS-SM SM6.E.1 (coverage): the **victim TCB write lock** — under which the
cancellation clears the victim's IPC fields — is a declared member of the
`cancelIpcBlocking` footprint, unconditionally. -/
theorem lockSet_cancelIpcBlocking_victim_tcb_write_mem
    (victimTid : SeLe4n.ThreadId)
    (blEp : Option SeLe4n.ObjId)
    (blN : Option SeLe4n.ObjId)
    (consumedReplyId : Option SeLe4n.ReplyId)
    (rdSc : Option SeLe4n.SchedContextId)
    (dhTid : Option SeLe4n.ThreadId)
    (holderEp : Option SeLe4n.ObjId)
    (holderNb : Option SeLe4n.ThreadId × Option SeLe4n.ThreadId)
    (belowHeadReply? : Option SeLe4n.ReplyId)
    (outerCaller? : Option SeLe4n.ThreadId)
    (reclaimHead? : Option SeLe4n.ReplyId)
    (frameAbove? : Option SeLe4n.ReplyId)
    -- **WS-HP HP3.1**: the frame below the cut, which the splice re-links.
    (splicedBelow? : Option SeLe4n.ReplyId) :
    (tcbLock victimTid, AccessMode.write)
      ∈ (lockSet_cancelIpcBlocking victimTid blEp blN consumedReplyId rdSc dhTid holderEp holderNb belowHeadReply? outerCaller? reclaimHead? frameAbove? splicedBelow?).pairs := by
  unfold lockSet_cancelIpcBlocking
  iterate 14 apply mem_write_lockSetExtendOpt
  show (tcbLock victimTid, AccessMode.write)
    ∈ ((LockSet.empty.insertOrMerge (tcbLock victimTid) AccessMode.write)).pairs
  exact self_write_mem_insertOrMerge _ (tcbLock victimTid)

/-- WS-SM SM6.E.1 (coverage): the **blocked-on endpoint write lock** — under
which the cancellation dequeues the victim and patches its queue neighbours —
is a declared member whenever the endpoint is resolved. -/
theorem lockSet_cancelIpcBlocking_blocked_endpoint_write_mem
    (victimTid : SeLe4n.ThreadId)
    (ep : SeLe4n.ObjId)
    (blN : Option SeLe4n.ObjId)
    (consumedReplyId : Option SeLe4n.ReplyId)
    (rdSc : Option SeLe4n.SchedContextId)
    (dhTid : Option SeLe4n.ThreadId)
    (holderEp : Option SeLe4n.ObjId)
    (holderNb : Option SeLe4n.ThreadId × Option SeLe4n.ThreadId)
    (belowHeadReply? : Option SeLe4n.ReplyId)
    (outerCaller? : Option SeLe4n.ThreadId)
    (reclaimHead? : Option SeLe4n.ReplyId)
    (frameAbove? : Option SeLe4n.ReplyId)
    -- **WS-HP HP3.1**: the frame below the cut, which the splice re-links.
    (splicedBelow? : Option SeLe4n.ReplyId) :
    (endpointLock ep, AccessMode.write)
      ∈ (lockSet_cancelIpcBlocking victimTid (some ep) blN consumedReplyId rdSc dhTid holderEp holderNb belowHeadReply? outerCaller? reclaimHead? frameAbove? splicedBelow?).pairs := by
  unfold lockSet_cancelIpcBlocking
  iterate 13 apply mem_write_lockSetExtendOpt
  simp only [lockSetExtendOpt, Option.map_some]
  exact self_write_mem_insertOrMerge _ (endpointLock ep)

/-- WS-SM SM6.E.1 (coverage): the **blocked-on notification write lock** —
under which the cancellation drops the victim's waiter-list entry — is a
declared member whenever the notification is resolved. -/
theorem lockSet_cancelIpcBlocking_blocked_notification_write_mem
    (victimTid : SeLe4n.ThreadId)
    (blEp : Option SeLe4n.ObjId)
    (n : SeLe4n.ObjId)
    (consumedReplyId : Option SeLe4n.ReplyId)
    (rdSc : Option SeLe4n.SchedContextId)
    (dhTid : Option SeLe4n.ThreadId)
    (holderEp : Option SeLe4n.ObjId)
    (holderNb : Option SeLe4n.ThreadId × Option SeLe4n.ThreadId)
    (belowHeadReply? : Option SeLe4n.ReplyId)
    (outerCaller? : Option SeLe4n.ThreadId)
    (reclaimHead? : Option SeLe4n.ReplyId)
    (frameAbove? : Option SeLe4n.ReplyId)
    -- **WS-HP HP3.1**: the frame below the cut, which the splice re-links.
    (splicedBelow? : Option SeLe4n.ReplyId) :
    (notificationLock n, AccessMode.write)
      ∈ (lockSet_cancelIpcBlocking victimTid blEp (some n) consumedReplyId rdSc dhTid holderEp holderNb belowHeadReply? outerCaller? reclaimHead? frameAbove? splicedBelow?).pairs := by
  unfold lockSet_cancelIpcBlocking
  iterate 12 apply mem_write_lockSetExtendOpt
  simp only [lockSetExtendOpt, Option.map_some]
  exact self_write_mem_insertOrMerge _ (notificationLock n)

/-- WS-SM SM6.E.1 (coverage): the **consumed Reply object write lock** — under
which the cancellation severs the single-use `reply.caller` back-link — is a
declared member whenever the reply is resolved. -/
theorem lockSet_cancelIpcBlocking_consumed_reply_write_mem
    (victimTid : SeLe4n.ThreadId)
    (blEp : Option SeLe4n.ObjId)
    (blN : Option SeLe4n.ObjId)
    (r : SeLe4n.ReplyId)
    (rdSc : Option SeLe4n.SchedContextId)
    (dhTid : Option SeLe4n.ThreadId)
    (holderEp : Option SeLe4n.ObjId)
    (holderNb : Option SeLe4n.ThreadId × Option SeLe4n.ThreadId)
    (belowHeadReply? : Option SeLe4n.ReplyId)
    (outerCaller? : Option SeLe4n.ThreadId)
    (reclaimHead? : Option SeLe4n.ReplyId)
    (frameAbove? : Option SeLe4n.ReplyId)
    -- **WS-HP HP3.1**: the frame below the cut, which the splice re-links.
    (splicedBelow? : Option SeLe4n.ReplyId) :
    (replyLock r, AccessMode.write)
      ∈ (lockSet_cancelIpcBlocking victimTid blEp blN (some r) rdSc dhTid holderEp holderNb belowHeadReply? outerCaller? reclaimHead? frameAbove? splicedBelow?).pairs := by
  unfold lockSet_cancelIpcBlocking
  iterate 11 apply mem_write_lockSetExtendOpt
  simp only [lockSetExtendOpt, Option.map_some]
  exact self_write_mem_insertOrMerge _ (replyLock r)

/-- **WS-RR RR7.22 (residual, remediation)**: the **returned SchedContext write
lock** — under which the reply arm rebinds `boundThread` back to the cancelled
caller — is a declared member whenever a donation is resolved. -/
theorem lockSet_cancelIpcBlocking_returned_donation_sc_write_mem
    (victimTid : SeLe4n.ThreadId)
    (blEp : Option SeLe4n.ObjId)
    (blN : Option SeLe4n.ObjId)
    (consumedReplyId : Option SeLe4n.ReplyId)
    (sc : SeLe4n.SchedContextId)
    (dhTid : Option SeLe4n.ThreadId)
    (holderEp : Option SeLe4n.ObjId)
    (holderNb : Option SeLe4n.ThreadId × Option SeLe4n.ThreadId)
    (belowHeadReply? : Option SeLe4n.ReplyId)
    (outerCaller? : Option SeLe4n.ThreadId)
    (reclaimHead? : Option SeLe4n.ReplyId)
    (frameAbove? : Option SeLe4n.ReplyId)
    -- **WS-HP HP3.1**: the frame below the cut, which the splice re-links.
    (splicedBelow? : Option SeLe4n.ReplyId) :
    (schedContextLock sc, AccessMode.write)
      ∈ (lockSet_cancelIpcBlocking victimTid blEp blN consumedReplyId (some sc) dhTid holderEp holderNb belowHeadReply? outerCaller? reclaimHead? frameAbove? splicedBelow?).pairs := by
  unfold lockSet_cancelIpcBlocking
  iterate 10 apply mem_write_lockSetExtendOpt
  simp only [lockSetExtendOpt, Option.map_some]
  exact self_write_mem_insertOrMerge _ (schedContextLock sc)

/-- **WS-RR RR7.22 (residual, remediation)**: the **donation holder's TCB write
lock** — under which the reply arm clears the server's `.donated` binding — is a
declared member whenever a donation is resolved. -/
theorem lockSet_cancelIpcBlocking_donation_holder_tcb_write_mem
    (victimTid : SeLe4n.ThreadId)
    (blEp : Option SeLe4n.ObjId)
    (blN : Option SeLe4n.ObjId)
    (consumedReplyId : Option SeLe4n.ReplyId)
    (rdSc : Option SeLe4n.SchedContextId)
    (h : SeLe4n.ThreadId)
    (holderEp : Option SeLe4n.ObjId)
    (holderNb : Option SeLe4n.ThreadId × Option SeLe4n.ThreadId)
    (belowHeadReply? : Option SeLe4n.ReplyId)
    (outerCaller? : Option SeLe4n.ThreadId)
    (reclaimHead? : Option SeLe4n.ReplyId)
    (frameAbove? : Option SeLe4n.ReplyId)
    -- **WS-HP HP3.1**: the frame below the cut, which the splice re-links.
    (splicedBelow? : Option SeLe4n.ReplyId) :
    (tcbLock h, AccessMode.write)
      ∈ (lockSet_cancelIpcBlocking victimTid blEp blN consumedReplyId rdSc (some h) holderEp holderNb belowHeadReply? outerCaller? reclaimHead? frameAbove? splicedBelow?).pairs := by
  unfold lockSet_cancelIpcBlocking
  iterate 9 apply mem_write_lockSetExtendOpt
  simp only [lockSetExtendOpt, Option.map_some]
  exact self_write_mem_insertOrMerge _ (tcbLock h)

/-- **WS-OD OD1.5** (coverage): the **holder's endpoint write lock** — under
which the reclaim's abort prefix splices the holder out of its send queue — is a
declared member whenever the abort runs.

The three theorems here are the abort's half of the footprint's coverage
argument.  Before OD1.5 the declared set named the holder's *TCB* and not the
endpoint it is queued on, so the footprint was **false** on the one arm where the
abort runs — worse, by this project's rule, than a wide one. -/
theorem lockSet_cancelIpcBlocking_holder_endpoint_write_mem
    (victimTid : SeLe4n.ThreadId)
    (blEp : Option SeLe4n.ObjId)
    (blN : Option SeLe4n.ObjId)
    (consumedReplyId : Option SeLe4n.ReplyId)
    (rdSc : Option SeLe4n.SchedContextId)
    (dhTid : Option SeLe4n.ThreadId)
    (ep : SeLe4n.ObjId)
    (holderNb : Option SeLe4n.ThreadId × Option SeLe4n.ThreadId)
    (belowHeadReply? : Option SeLe4n.ReplyId)
    (outerCaller? : Option SeLe4n.ThreadId)
    (reclaimHead? : Option SeLe4n.ReplyId)
    (frameAbove? : Option SeLe4n.ReplyId)
    -- **WS-HP HP3.1**: the frame below the cut, which the splice re-links.
    (splicedBelow? : Option SeLe4n.ReplyId) :
    (endpointLock ep, AccessMode.write)
      ∈ (lockSet_cancelIpcBlocking victimTid blEp blN consumedReplyId rdSc dhTid (some ep) holderNb belowHeadReply? outerCaller? reclaimHead? frameAbove? splicedBelow?).pairs := by
  unfold lockSet_cancelIpcBlocking
  iterate 8 apply mem_write_lockSetExtendOpt
  simp only [lockSetExtendOpt, Option.map_some]
  exact self_write_mem_insertOrMerge _ (endpointLock ep)

/-- **WS-OD OD1.5** (coverage): the aborted holder's **predecessor** TCB write
lock, under which the splice patches its `queueNext`. -/
theorem lockSet_cancelIpcBlocking_holder_splice_prev_write_mem
    (victimTid : SeLe4n.ThreadId)
    (blEp : Option SeLe4n.ObjId)
    (blN : Option SeLe4n.ObjId)
    (consumedReplyId : Option SeLe4n.ReplyId)
    (rdSc : Option SeLe4n.SchedContextId)
    (dhTid : Option SeLe4n.ThreadId)
    (holderEp : Option SeLe4n.ObjId)
    (p : SeLe4n.ThreadId) (nb2 : Option SeLe4n.ThreadId)
    (belowHeadReply? : Option SeLe4n.ReplyId)
    (outerCaller? : Option SeLe4n.ThreadId)
    (reclaimHead? : Option SeLe4n.ReplyId)
    (frameAbove? : Option SeLe4n.ReplyId)
    -- **WS-HP HP3.1**: the frame below the cut, which the splice re-links.
    (splicedBelow? : Option SeLe4n.ReplyId) :
    (tcbLock p, AccessMode.write)
      ∈ (lockSet_cancelIpcBlocking victimTid blEp blN consumedReplyId rdSc dhTid holderEp (some p, nb2) belowHeadReply? outerCaller? reclaimHead? frameAbove? splicedBelow?).pairs := by
  unfold lockSet_cancelIpcBlocking
  iterate 7 apply mem_write_lockSetExtendOpt
  simp only [lockSetExtendOpt, Option.map_some]
  exact self_write_mem_insertOrMerge _ (tcbLock p)

/-- **WS-OD OD1.5** (coverage): the aborted holder's **successor** TCB write
lock, under which the splice patches its `queuePrev` and `queuePPrev`. -/
theorem lockSet_cancelIpcBlocking_holder_splice_next_write_mem
    (victimTid : SeLe4n.ThreadId)
    (blEp : Option SeLe4n.ObjId)
    (blN : Option SeLe4n.ObjId)
    (consumedReplyId : Option SeLe4n.ReplyId)
    (rdSc : Option SeLe4n.SchedContextId)
    (dhTid : Option SeLe4n.ThreadId)
    (holderEp : Option SeLe4n.ObjId)
    (nb1 : Option SeLe4n.ThreadId) (n : SeLe4n.ThreadId)
    (belowHeadReply? : Option SeLe4n.ReplyId)
    (outerCaller? : Option SeLe4n.ThreadId)
    (reclaimHead? : Option SeLe4n.ReplyId)
    (frameAbove? : Option SeLe4n.ReplyId)
    -- **WS-HP HP3.1**: the frame below the cut, which the splice re-links.
    (splicedBelow? : Option SeLe4n.ReplyId) :
    (tcbLock n, AccessMode.write)
      ∈ (lockSet_cancelIpcBlocking victimTid blEp blN consumedReplyId rdSc dhTid holderEp (nb1, some n) belowHeadReply? outerCaller? reclaimHead? frameAbove? splicedBelow?).pairs := by
  unfold lockSet_cancelIpcBlocking
  iterate 6 apply mem_write_lockSetExtendOpt
  simp only [lockSetExtendOpt, Option.map_some]
  exact self_write_mem_insertOrMerge _ (tcbLock n)

/-- **WS-OD (`v0.35.4`)** (coverage): the **frame below the reply-stack head**
is a declared **write** — the reclaim's pop re-heads it (`storeReplyReHead`).
OD3.7 declared this object read; the doubly-linked stack writes it. -/
theorem lockSet_cancelIpcBlocking_below_head_write_mem
    (victimTid : SeLe4n.ThreadId)
    (blEp : Option SeLe4n.ObjId)
    (blN : Option SeLe4n.ObjId)
    (consumedReplyId : Option SeLe4n.ReplyId)
    (rdSc : Option SeLe4n.SchedContextId)
    (dhTid : Option SeLe4n.ThreadId)
    (holderEp : Option SeLe4n.ObjId)
    (holderNb : Option SeLe4n.ThreadId × Option SeLe4n.ThreadId)
    (r : SeLe4n.ReplyId)
    (outerCaller? : Option SeLe4n.ThreadId)
    (reclaimHead? : Option SeLe4n.ReplyId)
    (frameAbove? : Option SeLe4n.ReplyId)
    -- **WS-HP HP3.1**: the frame below the cut, which the splice re-links.
    (splicedBelow? : Option SeLe4n.ReplyId) :
    (replyLock r, AccessMode.write)
      ∈ (lockSet_cancelIpcBlocking victimTid blEp blN consumedReplyId rdSc dhTid holderEp holderNb (some r) outerCaller? reclaimHead? frameAbove? splicedBelow?).pairs := by
  unfold lockSet_cancelIpcBlocking
  iterate 5 apply mem_write_lockSetExtendOpt
  simp only [lockSetExtendOpt, Option.map_some]
  exact self_write_mem_insertOrMerge _ (replyLock r)

/-- **WS-OD (`v0.35.4`)** (coverage): the **outer caller's TCB** is a declared
key — the pop reads it (`outerCallerAcceptable`) and the suspend pipeline's
second pop, one step later, rebinds it.  Stated as `containsKey` rather than as a
mode membership, because the fact the suspend footprint's size argument consumes
is that the key is already present: the pipeline's write-mode member for the
same thread then merges instead of counting
(`LockSet.size_insertOrMerge_of_containsKey`). -/
theorem lockSet_cancelIpcBlocking_outer_caller_containsKey
    (victimTid : SeLe4n.ThreadId)
    (blEp : Option SeLe4n.ObjId)
    (blN : Option SeLe4n.ObjId)
    (consumedReplyId : Option SeLe4n.ReplyId)
    (rdSc : Option SeLe4n.SchedContextId)
    (dhTid : Option SeLe4n.ThreadId)
    (holderEp : Option SeLe4n.ObjId)
    (holderNb : Option SeLe4n.ThreadId × Option SeLe4n.ThreadId)
    (belowHeadReply? : Option SeLe4n.ReplyId)
    (ot : SeLe4n.ThreadId)
    (reclaimHead? : Option SeLe4n.ReplyId)
    (frameAbove? : Option SeLe4n.ReplyId)
    -- **WS-HP HP3.1**: the frame below the cut, which the splice re-links.
    (splicedBelow? : Option SeLe4n.ReplyId) :
    (lockSet_cancelIpcBlocking victimTid blEp blN consumedReplyId rdSc dhTid holderEp holderNb belowHeadReply? (some ot) reclaimHead? frameAbove? splicedBelow?).containsKey (tcbLock ot) = true := by
  unfold lockSet_cancelIpcBlocking
  iterate 4 apply containsKey_lockSetExtendOpt_of_containsKey
  simp only [lockSetExtendOpt, Option.map_some]
  exact containsKey_insertOrMerge_self _ (tcbLock ot) _

/-- **WS-OD (`v0.35.4`)** (coverage): the **head the reclaim clears** is a
declared write, on its own key rather than through the consumed reply's. -/
theorem lockSet_cancelIpcBlocking_reclaim_head_write_mem
    (victimTid : SeLe4n.ThreadId)
    (blEp : Option SeLe4n.ObjId)
    (blN : Option SeLe4n.ObjId)
    (consumedReplyId : Option SeLe4n.ReplyId)
    (rdSc : Option SeLe4n.SchedContextId)
    (dhTid : Option SeLe4n.ThreadId)
    (holderEp : Option SeLe4n.ObjId)
    (holderNb : Option SeLe4n.ThreadId × Option SeLe4n.ThreadId)
    (belowHeadReply? : Option SeLe4n.ReplyId)
    (outerCaller? : Option SeLe4n.ThreadId)
    (r : SeLe4n.ReplyId)
    (frameAbove? : Option SeLe4n.ReplyId)
    (splicedBelow? : Option SeLe4n.ReplyId) :
    (replyLock r, AccessMode.write)
      ∈ (lockSet_cancelIpcBlocking victimTid blEp blN consumedReplyId rdSc dhTid holderEp holderNb belowHeadReply? outerCaller? (some r) frameAbove? splicedBelow?).pairs := by
  unfold lockSet_cancelIpcBlocking
  iterate 3 apply mem_write_lockSetExtendOpt
  simp only [lockSetExtendOpt, Option.map_some]
  exact self_write_mem_insertOrMerge _ (replyLock r)

/-- **WS-OD (`v0.35.4`)** (coverage): the **frame above the cancelled caller's
own** — the one `spliceThreadReplyFrameOut` unlinks — is a declared write. -/
theorem lockSet_cancelIpcBlocking_spliced_frame_above_write_mem
    (victimTid : SeLe4n.ThreadId)
    (blEp : Option SeLe4n.ObjId)
    (blN : Option SeLe4n.ObjId)
    (consumedReplyId : Option SeLe4n.ReplyId)
    (rdSc : Option SeLe4n.SchedContextId)
    (dhTid : Option SeLe4n.ThreadId)
    (holderEp : Option SeLe4n.ObjId)
    (holderNb : Option SeLe4n.ThreadId × Option SeLe4n.ThreadId)
    (belowHeadReply? : Option SeLe4n.ReplyId)
    (outerCaller? : Option SeLe4n.ThreadId)
    (reclaimHead? : Option SeLe4n.ReplyId)
    (r : SeLe4n.ReplyId)
    (splicedBelow? : Option SeLe4n.ReplyId) :
    (replyLock r, AccessMode.write)
      ∈ (lockSet_cancelIpcBlocking victimTid blEp blN consumedReplyId rdSc dhTid holderEp holderNb belowHeadReply? outerCaller? reclaimHead? (some r) splicedBelow?).pairs := by
  unfold lockSet_cancelIpcBlocking
  iterate 2 apply mem_write_lockSetExtendOpt
  simp only [lockSetExtendOpt, Option.map_some]
  exact self_write_mem_insertOrMerge _ (replyLock r)

/-- **WS-HP HP3.1** (coverage): the **frame below the cut** — the one the splice
re-links upward, in the same step as the frame above's rewrite — is a declared write.  The
second half of the removal's write set; the first is the lemma above. -/
theorem lockSet_cancelIpcBlocking_spliced_frame_below_write_mem
    (victimTid : SeLe4n.ThreadId)
    (blEp : Option SeLe4n.ObjId)
    (blN : Option SeLe4n.ObjId)
    (consumedReplyId : Option SeLe4n.ReplyId)
    (rdSc : Option SeLe4n.SchedContextId)
    (dhTid : Option SeLe4n.ThreadId)
    (holderEp : Option SeLe4n.ObjId)
    (holderNb : Option SeLe4n.ThreadId × Option SeLe4n.ThreadId)
    (belowHeadReply? : Option SeLe4n.ReplyId)
    (outerCaller? : Option SeLe4n.ThreadId)
    (reclaimHead? : Option SeLe4n.ReplyId)
    (frameAbove? : Option SeLe4n.ReplyId)
    (r : SeLe4n.ReplyId) :
    (replyLock r, AccessMode.write)
      ∈ (lockSet_cancelIpcBlocking victimTid blEp blN consumedReplyId rdSc dhTid holderEp holderNb belowHeadReply? outerCaller? reclaimHead? frameAbove? (some r)).pairs := by
  unfold lockSet_cancelIpcBlocking
  iterate 1 apply mem_write_lockSetExtendOpt
  simp only [lockSetExtendOpt, Option.map_some]
  exact self_write_mem_insertOrMerge _ (replyLock r)

-- The donation-cancellation tower, innermost first: the victim's TCB; the
-- SchedContext; the donated arm's original owner; (WS-OD `v0.35.4`) the head
-- the pop clears, the frame below it re-heads and the outer caller it reads;
-- and the state-level lock outermost -- six extensions.

/-- WS-SM SM6.E.3 (coverage): the **victim (donor) TCB write lock** is a
declared member of the `cancelDonation` footprint, unconditionally. -/
theorem lockSet_cancelDonation_victim_tcb_write_mem
    (victimTid : SeLe4n.ThreadId)
    (bindingScId : Option SeLe4n.SchedContextId)
    (donatedOriginalOwnerTid : Option SeLe4n.ThreadId)
    (headReplyId : Option SeLe4n.ReplyId)
    (belowHeadReplyId : Option SeLe4n.ReplyId)
    (outerCallerTid : Option SeLe4n.ThreadId) :
    (tcbLock victimTid, AccessMode.write)
      ∈ (lockSet_cancelDonation victimTid bindingScId donatedOriginalOwnerTid headReplyId belowHeadReplyId outerCallerTid).pairs := by
  unfold lockSet_cancelDonation
  iterate 6 apply mem_write_lockSetExtendOpt
  show (tcbLock victimTid, AccessMode.write)
    ∈ ((LockSet.empty.insertOrMerge (tcbLock victimTid) AccessMode.write)).pairs
  exact self_write_mem_insertOrMerge _ (tcbLock victimTid)

/-- WS-SM SM6.E.3 (coverage): the **SchedContext write lock** — under which
the bound arm deactivates the SC and the donated arm re-binds it — is a
declared member whenever the SC is resolved. -/
theorem lockSet_cancelDonation_binding_sc_write_mem
    (victimTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId)
    (donatedOriginalOwnerTid : Option SeLe4n.ThreadId)
    (headReplyId : Option SeLe4n.ReplyId)
    (belowHeadReplyId : Option SeLe4n.ReplyId)
    (outerCallerTid : Option SeLe4n.ThreadId) :
    (schedContextLock scId, AccessMode.write)
      ∈ (lockSet_cancelDonation victimTid (some scId) donatedOriginalOwnerTid headReplyId belowHeadReplyId outerCallerTid).pairs := by
  unfold lockSet_cancelDonation
  iterate 5 apply mem_write_lockSetExtendOpt
  simp only [lockSetExtendOpt, Option.map_some]
  exact self_write_mem_insertOrMerge _ (schedContextLock scId)

/-- WS-SM SM6.E.3 (coverage): the **original-owner TCB write lock** — under
which the donated arm re-establishes the owner's binding — is a declared member
whenever the owner is resolved. -/
theorem lockSet_cancelDonation_donated_owner_tcb_write_mem
    (victimTid : SeLe4n.ThreadId)
    (bindingScId : Option SeLe4n.SchedContextId)
    (ot : SeLe4n.ThreadId)
    (headReplyId : Option SeLe4n.ReplyId)
    (belowHeadReplyId : Option SeLe4n.ReplyId)
    (outerCallerTid : Option SeLe4n.ThreadId) :
    (tcbLock ot, AccessMode.write)
      ∈ (lockSet_cancelDonation victimTid bindingScId (some ot) headReplyId belowHeadReplyId outerCallerTid).pairs := by
  unfold lockSet_cancelDonation
  iterate 4 apply mem_write_lockSetExtendOpt
  simp only [lockSetExtendOpt, Option.map_some]
  exact self_write_mem_insertOrMerge _ (tcbLock ot)

/-- **WS-OD (`v0.35.4`)** (coverage): the **head the donated arm's pop clears**
is a declared write whenever it is resolved. -/
theorem lockSet_cancelDonation_head_write_mem
    (victimTid : SeLe4n.ThreadId)
    (bindingScId : Option SeLe4n.SchedContextId)
    (donatedOriginalOwnerTid : Option SeLe4n.ThreadId)
    (r : SeLe4n.ReplyId)
    (belowHeadReplyId : Option SeLe4n.ReplyId)
    (outerCallerTid : Option SeLe4n.ThreadId) :
    (replyLock r, AccessMode.write)
      ∈ (lockSet_cancelDonation victimTid bindingScId donatedOriginalOwnerTid (some r) belowHeadReplyId outerCallerTid).pairs := by
  unfold lockSet_cancelDonation
  iterate 3 apply mem_write_lockSetExtendOpt
  simp only [lockSetExtendOpt, Option.map_some]
  exact self_write_mem_insertOrMerge _ (replyLock r)

/-- **WS-OD (`v0.35.4`)** (coverage): and the **frame below it**, which the pop
re-heads. -/
theorem lockSet_cancelDonation_below_head_write_mem
    (victimTid : SeLe4n.ThreadId)
    (bindingScId : Option SeLe4n.SchedContextId)
    (donatedOriginalOwnerTid : Option SeLe4n.ThreadId)
    (headReplyId : Option SeLe4n.ReplyId)
    (r : SeLe4n.ReplyId)
    (outerCallerTid : Option SeLe4n.ThreadId) :
    (replyLock r, AccessMode.write)
      ∈ (lockSet_cancelDonation victimTid bindingScId donatedOriginalOwnerTid headReplyId (some r) outerCallerTid).pairs := by
  unfold lockSet_cancelDonation
  iterate 2 apply mem_write_lockSetExtendOpt
  simp only [lockSetExtendOpt, Option.map_some]
  exact self_write_mem_insertOrMerge _ (replyLock r)

/-- **WS-OD (`v0.35.4`)** (coverage): the **outer caller** the pop validates is
a declared key. -/
theorem lockSet_cancelDonation_outer_caller_containsKey
    (victimTid : SeLe4n.ThreadId)
    (bindingScId : Option SeLe4n.SchedContextId)
    (donatedOriginalOwnerTid : Option SeLe4n.ThreadId)
    (headReplyId : Option SeLe4n.ReplyId)
    (belowHeadReplyId : Option SeLe4n.ReplyId)
    (ot : SeLe4n.ThreadId) :
    (lockSet_cancelDonation victimTid bindingScId donatedOriginalOwnerTid headReplyId belowHeadReplyId (some ot)).containsKey (tcbLock ot) = true := by
  unfold lockSet_cancelDonation
  iterate 1 apply containsKey_lockSetExtendOpt_of_containsKey
  simp only [lockSetExtendOpt, Option.map_some]
  exact containsKey_insertOrMerge_self _ (tcbLock ot) _

/-- **WS-OD OD3.5 / `v0.35.4`** (coverage): the **state-level lock** the reclaim's
`scThreadIndex` maintenance takes is a declared write whenever a donation is
resolved — the member OD3.5 declared and never gave a coverage theorem. -/
theorem lockSet_cancelIpcBlocking_stateLevel_write_mem
    (victimTid : SeLe4n.ThreadId) (blEp blN : Option SeLe4n.ObjId)
    (consumedReplyId : Option SeLe4n.ReplyId) (sc : SeLe4n.SchedContextId)
    (dhTid : Option SeLe4n.ThreadId) (holderEp : Option SeLe4n.ObjId)
    (holderNb : Option SeLe4n.ThreadId × Option SeLe4n.ThreadId)
    (belowHeadReply? : Option SeLe4n.ReplyId) (outerCaller? : Option SeLe4n.ThreadId)
    (reclaimHead? frameAbove? : Option SeLe4n.ReplyId)
    -- **WS-HP HP3.1**: the frame below the cut, which the splice re-links.
    (splicedBelow? : Option SeLe4n.ReplyId) :
    (stateLevelLock, AccessMode.write)
      ∈ (lockSet_cancelIpcBlocking victimTid blEp blN consumedReplyId (some sc) dhTid holderEp
          holderNb belowHeadReply? outerCaller? reclaimHead? frameAbove? splicedBelow?).pairs := by
  unfold lockSet_cancelIpcBlocking
  simp only [Option.isSome_some, if_true]
  exact LockSet.mem_insertOrMerge_write_self _ _

/-- **WS-OD OD3.5 / `v0.35.4`** (coverage): and the donation cancellation's. -/
theorem lockSet_cancelDonation_stateLevel_write_mem
    (victimTid : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (donatedOriginalOwnerTid : Option SeLe4n.ThreadId)
    (headReplyId belowHeadReplyId : Option SeLe4n.ReplyId)
    (outerCallerTid : Option SeLe4n.ThreadId) :
    (stateLevelLock, AccessMode.write)
      ∈ (lockSet_cancelDonation victimTid (some scId) donatedOriginalOwnerTid
          headReplyId belowHeadReplyId outerCallerTid).pairs := by
  unfold lockSet_cancelDonation
  simp only [Option.isSome_some, if_true]
  exact LockSet.mem_insertOrMerge_write_self _ _

-- ============================================================================
-- §7b  Coverage of the state-resolved cancellation footprint
-- ============================================================================
-- The `OnCore` form is what the suspend footprint below is rooted at, so its
-- coverage is stated once here, member by member, and the suspend footprint
-- inherits it through one lift.

/-- WS-OD (`v0.35.4`): the victim's TCB write lock, on every arm. -/
theorem lockSet_cancelIpcBlockingOnCore_covers_victim (st : SystemState)
    (victimTid : SeLe4n.ThreadId) :
    (tcbLock victimTid, AccessMode.write)
      ∈ (lockSet_cancelIpcBlockingOnCore st victimTid).pairs := by
  unfold lockSet_cancelIpcBlockingOnCore
  split
  · iterate 2 apply mem_write_lockSetExtendOpt
    exact lockSet_cancelIpcBlocking_victim_tcb_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _
  · exact lockSet_cancelIpcBlocking_victim_tcb_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _

/-- WS-OD (`v0.35.4`): the blocked endpoint's write lock, on the endpoint arm. -/
theorem lockSet_cancelIpcBlockingOnCore_covers_blockedEndpoint (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB) (ep : SeLe4n.ObjId)
    (hT : st.getTcb? victimTid = some tcb) (hE : cancelBlockedEndpoint? tcb = some ep) :
    (endpointLock ep, AccessMode.write)
      ∈ (lockSet_cancelIpcBlockingOnCore st victimTid).pairs := by
  unfold lockSet_cancelIpcBlockingOnCore
  rw [hT]
  simp only [hE]
  iterate 2 apply mem_write_lockSetExtendOpt
  exact lockSet_cancelIpcBlocking_blocked_endpoint_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _

/-- WS-OD (`v0.35.4`): the blocked notification's, on the notification arm. -/
theorem lockSet_cancelIpcBlockingOnCore_covers_blockedNotification (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB) (n : SeLe4n.ObjId)
    (hT : st.getTcb? victimTid = some tcb) (hN : cancelBlockedNotification? tcb = some n) :
    (notificationLock n, AccessMode.write)
      ∈ (lockSet_cancelIpcBlockingOnCore st victimTid).pairs := by
  unfold lockSet_cancelIpcBlockingOnCore
  rw [hT]
  simp only [hN]
  iterate 2 apply mem_write_lockSetExtendOpt
  exact lockSet_cancelIpcBlocking_blocked_notification_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _

/-- WS-OD (`v0.35.4`): the consumed Reply's, on the reply arm. -/
theorem lockSet_cancelIpcBlockingOnCore_covers_consumedReply (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB) (r : SeLe4n.ReplyId)
    (hT : st.getTcb? victimTid = some tcb) (hR : cancelConsumedReply? tcb = some r) :
    (replyLock r, AccessMode.write)
      ∈ (lockSet_cancelIpcBlockingOnCore st victimTid).pairs := by
  unfold lockSet_cancelIpcBlockingOnCore
  rw [hT]
  simp only [hR]
  iterate 2 apply mem_write_lockSetExtendOpt
  exact lockSet_cancelIpcBlocking_consumed_reply_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **WS-OD (`v0.35.4`)**: **the reclaim's writes are declared** — the context
handed back, the holder it is taken from, the state-level lock the index
maintenance takes, the head the pop clears and the frame below it re-heads.
Each of the last two is conditioned on the resolver that names it, so the
footprint carries the member exactly when the stack has one. -/
theorem lockSet_cancelIpcBlockingOnCore_covers_reclaim (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (holder : SeLe4n.ThreadId)
    (hT : st.getTcb? victimTid = some tcb)
    (hRes : Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb = some (scId, holder)) :
    (schedContextLock scId, AccessMode.write)
        ∈ (lockSet_cancelIpcBlockingOnCore st victimTid).pairs ∧
    (tcbLock holder, AccessMode.write)
        ∈ (lockSet_cancelIpcBlockingOnCore st victimTid).pairs ∧
    (stateLevelLock, AccessMode.write)
        ∈ (lockSet_cancelIpcBlockingOnCore st victimTid).pairs ∧
    (∀ head, replyStackHead? st scId = some head →
      (replyLock head, AccessMode.write)
        ∈ (lockSet_cancelIpcBlockingOnCore st victimTid).pairs) ∧
    (∀ below, (replyStackBelowHead? st scId).1 = some below →
      (replyLock below, AccessMode.write)
        ∈ (lockSet_cancelIpcBlockingOnCore st victimTid).pairs) := by
  unfold lockSet_cancelIpcBlockingOnCore
  rw [hT]
  simp only [hRes, Option.map_some, cancelBelowHeadReads?_of_donation st victimTid tcb scId holder hRes,
    cancelReclaimHead?_of_donation st victimTid tcb scId holder hRes]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · iterate 2 apply mem_write_lockSetExtendOpt
    exact lockSet_cancelIpcBlocking_returned_donation_sc_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _
  · iterate 2 apply mem_write_lockSetExtendOpt
    exact lockSet_cancelIpcBlocking_donation_holder_tcb_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _
  · iterate 2 apply mem_write_lockSetExtendOpt
    exact lockSet_cancelIpcBlocking_stateLevel_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _
  · intro head hHead
    rw [hHead]
    iterate 2 apply mem_write_lockSetExtendOpt
    exact lockSet_cancelIpcBlocking_reclaim_head_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _
  · intro below hBelow
    rw [hBelow]
    iterate 2 apply mem_write_lockSetExtendOpt
    exact lockSet_cancelIpcBlocking_below_head_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _

/-- WS-OD (`v0.35.4`): the outer caller the reclaim validates is a declared key. -/
theorem lockSet_cancelIpcBlockingOnCore_covers_outerCaller_key (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (holder outer : SeLe4n.ThreadId)
    (hT : st.getTcb? victimTid = some tcb)
    (hRes : Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb = some (scId, holder))
    (hOuter : (replyStackBelowHead? st scId).2 = some outer) :
    (lockSet_cancelIpcBlockingOnCore st victimTid).containsKey (tcbLock outer) = true := by
  unfold lockSet_cancelIpcBlockingOnCore
  rw [hT]
  simp only [hRes, Option.map_some, cancelBelowHeadReads?_of_donation st victimTid tcb scId holder hRes,
    cancelReclaimHead?_of_donation st victimTid tcb scId holder hRes, hOuter]
  iterate 2 apply containsKey_lockSetExtendOpt_of_containsKey
  exact lockSet_cancelIpcBlocking_outer_caller_containsKey _ _ _ _ _ _ _ _ _ _ _ _ _

/-- WS-OD (`v0.35.4`): the frame above the cut, which the splice rewrites, is a
declared write. -/
theorem lockSet_cancelIpcBlockingOnCore_covers_splicedFrameAbove (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB) (above : SeLe4n.ReplyId)
    (hT : st.getTcb? victimTid = some tcb)
    (hA : cancelSplicedFrameAbove? st tcb = some above) :
    (replyLock above, AccessMode.write)
      ∈ (lockSet_cancelIpcBlockingOnCore st victimTid).pairs := by
  unfold lockSet_cancelIpcBlockingOnCore
  rw [hT]
  simp only [hA]
  iterate 2 apply mem_write_lockSetExtendOpt
  exact lockSet_cancelIpcBlocking_spliced_frame_above_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **WS-HP HP3.4**: and the frame the splice re-links *below* the cut is one too
— the resolved coverage theorem this family carries for every member, tying the
declared lock to the **resolver** the footprint reads it from rather than to a
name.  `_correct` and `_size_le` do not stand in for it: one is about the kinds
of the members present and the other about how many there are, and neither says
that the object a resolver names is among them. -/
theorem lockSet_cancelIpcBlockingOnCore_covers_splicedFrameBelow (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB) (below : SeLe4n.ReplyId)
    (hT : st.getTcb? victimTid = some tcb)
    (hB : cancelSplicedFrameBelow? st tcb = some below) :
    (replyLock below, AccessMode.write)
      ∈ (lockSet_cancelIpcBlockingOnCore st victimTid).pairs := by
  unfold lockSet_cancelIpcBlockingOnCore
  rw [hT]
  simp only [hB]
  iterate 2 apply mem_write_lockSetExtendOpt
  exact lockSet_cancelIpcBlocking_spliced_frame_below_write_mem _ _ _ _ _ _ _ _ _ _ _ _ _

-- ============================================================================
-- §7c  Coverage of the state-resolved donation-cancellation footprint
-- ============================================================================
-- Swept here at the WS-RM post-landing audit.  Every parametric member of
-- `lockSet_cancelDonation` had its write-membership lemma and the `OnCore` form
-- had none, so nothing tied a member to the **resolver** the footprint reads it
-- from -- which is the whole content of a resolved coverage theorem, and the
-- shape `lockSet_cancelIpcBlockingOnCore` above and both reply footprints carry.
-- `_correct` and `_size_le` do not stand in for it: one is about the *kinds* of
-- the members present and the other about how many there are, and neither says
-- that the object a resolver names is among them.

/-- The victim's own TCB write lock, on **both** arms of the resolution — the
donor's binding is rewritten whether or not its TCB resolves. -/
theorem lockSet_cancelDonationOnCore_covers_victim (st : SystemState)
    (victimTid : SeLe4n.ThreadId) :
    (tcbLock victimTid, AccessMode.write)
      ∈ (lockSet_cancelDonationOnCore st victimTid).pairs := by
  unfold lockSet_cancelDonationOnCore
  split
  · exact lockSet_cancelDonation_victim_tcb_write_mem _ _ _ _ _ _
  · exact lockSet_cancelDonation_victim_tcb_write_mem _ _ _ _ _ _

/-- The SchedContext the cancellation rewrites — deactivated on the bound arm,
re-bound on the donated one — resolved through `cancelBindingSc?`. -/
theorem lockSet_cancelDonationOnCore_covers_bindingSchedContext (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (hT : st.getTcb? victimTid = some tcb)
    (hSc : cancelBindingSc? tcb = some scId) :
    (schedContextLock scId, AccessMode.write)
      ∈ (lockSet_cancelDonationOnCore st victimTid).pairs := by
  unfold lockSet_cancelDonationOnCore
  rw [hT]
  simp only [hSc]
  exact lockSet_cancelDonation_binding_sc_write_mem _ _ _ _ _ _

/-- ...and the `scThreadIndex` maintenance that rebinding takes, on the same
resolver: the index is an `RHTable` whose insert may rehash, so no per-object
member can cover it. -/
theorem lockSet_cancelDonationOnCore_covers_stateLevel (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (hT : st.getTcb? victimTid = some tcb)
    (hSc : cancelBindingSc? tcb = some scId) :
    (stateLevelLock, AccessMode.write)
      ∈ (lockSet_cancelDonationOnCore st victimTid).pairs := by
  unfold lockSet_cancelDonationOnCore
  rw [hT]
  simp only [hSc]
  exact lockSet_cancelDonation_stateLevel_write_mem _ _ _ _ _ _

/-- The original owner the donated arm hands the context back to, resolved
through `cancelDonatedOwner?` — `none` on the bound arm, which re-binds nobody. -/
theorem lockSet_cancelDonationOnCore_covers_donatedOwner (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB) (owner : SeLe4n.ThreadId)
    (hT : st.getTcb? victimTid = some tcb)
    (hOwner : cancelDonatedOwner? tcb = some owner) :
    (tcbLock owner, AccessMode.write)
      ∈ (lockSet_cancelDonationOnCore st victimTid).pairs := by
  unfold lockSet_cancelDonationOnCore
  rw [hT]
  simp only [hOwner]
  exact lockSet_cancelDonation_donated_owner_tcb_write_mem _ _ _ _ _ _

/-- The donated arm's reply-stack pop: the head it clears and the frame below it
re-heads, both resolved through `cancelDonationPopMembers?`. -/
theorem lockSet_cancelDonationOnCore_covers_pop (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB)
    (hT : st.getTcb? victimTid = some tcb) :
    (∀ head, (cancelDonationPopMembers? st tcb).1 = some head →
      (replyLock head, AccessMode.write)
        ∈ (lockSet_cancelDonationOnCore st victimTid).pairs) ∧
    (∀ below, (cancelDonationPopMembers? st tcb).2.1 = some below →
      (replyLock below, AccessMode.write)
        ∈ (lockSet_cancelDonationOnCore st victimTid).pairs) := by
  unfold lockSet_cancelDonationOnCore
  rw [hT]
  refine ⟨?_, ?_⟩
  · intro head hHead
    simp only [hHead]
    exact lockSet_cancelDonation_head_write_mem _ _ _ _ _ _
  · intro below hBelow
    simp only [hBelow]
    exact lockSet_cancelDonation_below_head_write_mem _ _ _ _ _ _

/-- ...and the outer caller the pop validates before it hands the context over,
a declared **key** rather than a write: the pop reads that TCB to check it is a
waiting donor, and rewrites the answered caller's binding, not its. -/
theorem lockSet_cancelDonationOnCore_covers_outerCaller_key (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB) (outer : SeLe4n.ThreadId)
    (hT : st.getTcb? victimTid = some tcb)
    (hOuter : (cancelDonationPopMembers? st tcb).2.2 = some outer) :
    (lockSet_cancelDonationOnCore st victimTid).containsKey (tcbLock outer) = true := by
  unfold lockSet_cancelDonationOnCore
  rw [hT]
  simp only [hOuter]
  exact lockSet_cancelDonation_outer_caller_containsKey _ _ _ _ _ _

-- ============================================================================
-- §8  The `.tcbSuspend` footprint — rooted at the cancellation footprint
-- ============================================================================
-- Until WS-OD (`v0.35.4`) the syscall-level footprint was a separate parametric
-- `lockSet_tcbSuspend` whose five optionals were resolved from the victim's
-- **pre-state** fields, and this section proved it covered the two
-- sub-operation footprints member by member.  That construction had two
-- defects the doubly-linked reply stack made impossible to keep.  It resolved
-- the donation cancellation's context from the victim's pre-state binding,
-- while `suspendThreadOnCore` runs that cancellation on the **post-teardown**
-- binding — the reclaim (v0.34.97) rebinds a cancelled caller *during* the
-- teardown, so on the live seams the reclaim itself, and at depth ≥ 2 the second
-- pop the rebinding provokes, wrote objects the footprint never named.  And it
-- was a second answer to a question the sub-operation footprint already
-- answered, so every member the cancellation gained had to be added twice.
--
-- The footprint is now *defined over* `lockSet_cancelIpcBlockingOnCore`: the
-- teardown's writes are covered by construction and the coverage theorem is a
-- one-line lift, and what this section declares is only what the pipeline adds
-- — the caller's two read locks and the donation cancellation's members,
-- resolved on the binding the pipeline will actually find.

/-- **WS-OD (`v0.35.4`)**: the members the suspend pipeline's **donation
cancellation** (`suspendThreadOnCore`'s G3 arm) adds beyond the teardown.

The arm dispatches on the victim's binding **after** `cancelIpcBlocking` has run,
and the teardown can change it: a cancelled caller owed a donation is rebound by
the reclaim — `.bound scId` at the bottom of the stack, `.donated scId outer`
above it — so the members are resolved on the binding the arm will find, not on
the one the victim entered with.  Two exclusive cases:

* **A reclaim is resolved** (`cancelledCallerDonation? = some (scId, _)`).  The
  victim leaves the teardown holding `scId`.  At the bottom of the stack it is
  `.bound scId` and the bound arm writes the context, the victim and the index —
  every one of them a member of the cancellation footprint already, so nothing
  is added.  Above the bottom it is `.donated scId outer`, and the donated arm
  **pops again**: the frame below the original head is cleared (the
  cancellation footprint's below-head write), the frame below *that* is
  re-headed (`belowHead?`), `outer` is rebound (`owner?`, write — the
  cancellation footprint holds that key in read mode, so this member merges
  rather than counts) and the second frame's caller is validated (`outer?`,
  read).  The context and the index are members already.
* **No reclaim is resolved.**  The binding is the one the victim entered with,
  and the arm is the plain donation cancellation: the bound arm writes the
  context and the index; the donated arm is the pop on the victim's own context,
  writing the context, the owner, the head and the frame below it, and reading
  the outer caller.

The one shape neither case describes — a reclaim resolved for a victim that
*already* holds a binding, which `donationOwnerValid` excludes and on which the
reclaim would overwrite that binding — is refused at the entry
(`cancelledCallerAlreadyBound`, consumed by `suspendFootprintOf`), because a
footprint that declared both cases at once could not stay inside the ceiling
and one that declared either alone would be false. -/
structure SuspendDonationCancelMembers where
  scId? : Option SeLe4n.SchedContextId := none
  owner? : Option SeLe4n.ThreadId := none
  head? : Option SeLe4n.ReplyId := none
  belowHead? : Option SeLe4n.ReplyId := none
  outer? : Option SeLe4n.ThreadId := none
  deriving Repr, DecidableEq

/-- WS-OD (`v0.35.4`): the donation-cancellation members, resolved as the
docstring of `SuspendDonationCancelMembers` describes. -/
def suspendDonationCancelTail? (st : SystemState) (victimTid : SeLe4n.ThreadId)
    (tcb : TCB) : SuspendDonationCancelMembers :=
  match Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb with
  | some (scId, _) =>
    match (replyStackBelowHead? st scId).2 with
    | none => {}
    | some outer =>
      { owner? := some outer,
        belowHead? := (replyStackSecondBelowHead? st scId).1,
        outer? := (replyStackSecondBelowHead? st scId).2 }
  | none =>
    match tcb.schedContextBinding with
    | .unbound => {}
    | .bound scId => { scId? := some scId }
    | .donated scId owner =>
      { scId? := some scId, owner? := some owner, head? := replyStackHead? st scId,
        belowHead? := (replyStackBelowHead? st scId).1,
        outer? := (replyStackBelowHead? st scId).2 }

/-- WS-OD (`v0.35.4`): the tail on the victim the state resolves; empty when the
target is no TCB, where the pipeline refuses before it cancels anything. -/
def suspendDonationCancelTailOf? (st : SystemState) (victimTid : SeLe4n.ThreadId) :
    SuspendDonationCancelMembers :=
  match st.getTcb? victimTid with
  | some tcb => suspendDonationCancelTail? st victimTid tcb
  | none => {}

/-- WS-OD (`v0.35.4`): **the shape the suspend footprint refuses** — a reclaim
resolved for a victim that already holds a binding.  `donationOwnerValid` says a
donation's owner is `.unbound`, so no reachable state has it; on one that did,
the reclaim would overwrite the binding the tail was resolved from, and no single
footprint inside the ceiling describes both what the tail declares and what the
arm would then touch.  `suspendFootprintOf` answers `none` on it, which falls
back to the coarse serialisation — always sound. -/
def cancelledCallerAlreadyBound (st : SystemState) (victimTid : SeLe4n.ThreadId)
    (tcb : TCB) : Bool :=
  (Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb).isSome &&
    tcb.schedContextBinding.scId?.isSome

/-- **WS-OD (`v0.35.4`): the concrete lock-set the `.tcbSuspend` syscall
acquires** — the state-resolved cancellation footprint, the caller's two read
locks (its TCB and the CSpace root the capability was resolved through), and the
donation cancellation's members resolved on the post-teardown binding, with the
state-level lock the plain donation cancellation's index maintenance takes.

Rooted at `lockSet_cancelIpcBlockingOnCore` rather than restating its members:
`lockSet_tcbSuspendOnCore_covers_cancelIpcBlockingOnCore` is the whole coverage
argument for the teardown, and a member the cancellation gains reaches this
footprint without being added a second time.

The CNode member is the **caller's** CSpace root, not the victim's — the
cap-resolution root `syscallLookupCap` reads to turn the caller's capability
pointer into the target capability.

`lockSet_tcbSuspendOnCore_size_le_seventeen` is its bound
(`Concurrency/Locks/ResolvedFootprintBounds.lean`): sixteen on the widest shape
— a reply-arm victim owed a donation at depth ≥ 3 — which is why
`maxLockSetSize` is sixteen. -/
def lockSet_tcbSuspendOnCore (st : SystemState) (callerTid : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (targetTid : SeLe4n.ThreadId) : LockSet :=
  lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt
    (lockSetExtendOpt (lockSetExtendOpt (lockSetExtendOpt
      (lockSet_cancelIpcBlockingOnCore st targetTid)
      (some (tcbLock callerTid, AccessMode.read)))
      (some (cnodeLock cnodeRootObjId, AccessMode.read)))
      ((suspendDonationCancelTailOf? st targetTid).scId?.map
        (fun sc => (schedContextLock sc, AccessMode.write))))
      ((suspendDonationCancelTailOf? st targetTid).owner?.map
        (fun ot => (tcbLock ot, AccessMode.write))))
      ((suspendDonationCancelTailOf? st targetTid).head?.map
        (fun r => (replyLock r, AccessMode.write))))
      ((suspendDonationCancelTailOf? st targetTid).belowHead?.map
        (fun r => (replyLock r, AccessMode.write))))
      ((suspendDonationCancelTailOf? st targetTid).outer?.map
        (fun ot => (tcbLock ot, AccessMode.read))))
    (if (suspendDonationCancelTailOf? st targetTid).scId?.isSome then
       some (stateLevelLock, AccessMode.write) else none)

/-- WS-OD (`v0.35.4`): the suspend footprint's kinds are all permitted for
`.tcbSuspend` — the cancellation root's by `lockSet_cancelIpcBlockingOnCore_correct`,
and the eight extensions are a TCB, a CNode, a SchedContext, two TCBs, two Replies
and the state-level lock. -/
theorem lockSet_tcbSuspendOnCore_correct (st : SystemState) (callerTid : SeLe4n.ThreadId)
    (cnodeRootObjId : SeLe4n.ObjId) (targetTid : SeLe4n.ThreadId) :
    ∀ p ∈ (lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid).pairs,
      p.fst.kind ∈ permittedKinds .tcbSuspend := by
  unfold lockSet_tcbSuspendOnCore
  refine lockSet_consistent_extendOpt _ _ _ (lockSet_consistent_extendOpt _ _ _
    (lockSet_consistent_extendOpt _ _ _ (lockSet_consistent_extendOpt _ _ _
    (lockSet_consistent_extendOpt _ _ _ (lockSet_consistent_extendOpt _ _ _
    (lockSet_consistent_extendOpt _ _ _ (lockSet_consistent_extendOpt _ _ _
      (lockSet_cancelIpcBlockingOnCore_correct st targetTid) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · intro pp hEq; injection hEq with h; rw [← h]
    show (tcbLock callerTid).kind ∈ permittedKinds .tcbSuspend
    rw [tcbLock_kind]; decide
  · intro pp hEq; injection hEq with h; rw [← h]
    show (cnodeLock cnodeRootObjId).kind ∈ permittedKinds .tcbSuspend
    rw [cnodeLock_kind]; decide
  · intro pp hEq
    cases h : (suspendDonationCancelTailOf? st targetTid).scId? with
    | none => rw [h] at hEq; cases hEq
    | some sc => rw [h] at hEq; injection hEq with h'; rw [← h']; simp; decide
  · intro pp hEq
    cases h : (suspendDonationCancelTailOf? st targetTid).owner? with
    | none => rw [h] at hEq; cases hEq
    | some ot => rw [h] at hEq; injection hEq with h'; rw [← h']; simp; decide
  · intro pp hEq
    cases h : (suspendDonationCancelTailOf? st targetTid).head? with
    | none => rw [h] at hEq; cases hEq
    | some r => rw [h] at hEq; injection hEq with h'; rw [← h']; simp; decide
  · intro pp hEq
    cases h : (suspendDonationCancelTailOf? st targetTid).belowHead? with
    | none => rw [h] at hEq; cases hEq
    | some r => rw [h] at hEq; injection hEq with h'; rw [← h']; simp; decide
  · intro pp hEq
    cases h : (suspendDonationCancelTailOf? st targetTid).outer? with
    | none => rw [h] at hEq; cases hEq
    | some ot => rw [h] at hEq; injection hEq with h'; rw [← h']; simp; decide
  · intro pp hEq
    cases h : (suspendDonationCancelTailOf? st targetTid).scId?.isSome with
    | false => rw [h] at hEq; cases hEq
    | true => rw [h] at hEq; injection hEq with h'; rw [← h']; simp [stateLevelLock]; decide

/-- **WS-OD (`v0.35.4`): every write the cancellation footprint declares is a
write the suspend footprint declares.**  The whole of what §8 used to prove
member by member, as one lift — the suspend footprint is *built over* the
cancellation footprint, so nothing has to be re-derived when that one gains a
member. -/
theorem lockSet_tcbSuspendOnCore_covers_cancelIpcBlockingOnCore (st : SystemState)
    (callerTid : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (targetTid : SeLe4n.ThreadId) (l : LockId)
    (hMem : (l, AccessMode.write) ∈ (lockSet_cancelIpcBlockingOnCore st targetTid).pairs) :
    (l, AccessMode.write)
      ∈ (lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid).pairs := by
  unfold lockSet_tcbSuspendOnCore
  iterate 8 apply mem_write_lockSetExtendOpt
  exact hMem

/-- WS-OD (`v0.35.4`): and a key the cancellation footprint holds, in any mode,
is a key the suspend footprint holds. -/
theorem lockSet_tcbSuspendOnCore_containsKey_of_cancelIpcBlockingOnCore (st : SystemState)
    (callerTid : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (targetTid : SeLe4n.ThreadId) (l : LockId)
    (hKey : (lockSet_cancelIpcBlockingOnCore st targetTid).containsKey l = true) :
    (lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid).containsKey l = true := by
  unfold lockSet_tcbSuspendOnCore
  iterate 8 apply containsKey_lockSetExtendOpt_of_containsKey
  exact hKey

/-- WS-OD (`v0.35.4`): the victim's TCB write lock — the one member every
`.tcbSuspend` needs — is declared, on every arm. -/
theorem lockSet_tcbSuspendOnCore_covers_victim (st : SystemState)
    (callerTid : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (targetTid : SeLe4n.ThreadId) :
    (tcbLock targetTid, AccessMode.write)
      ∈ (lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid).pairs :=
  lockSet_tcbSuspendOnCore_covers_cancelIpcBlockingOnCore st callerTid cnodeRootObjId
    targetTid _ (lockSet_cancelIpcBlockingOnCore_covers_victim st targetTid)

/-- **WS-OD (`v0.35.4`): the tail's members are declared in the modes it names
them** — the six facts the interpretation theorems below assemble. -/
theorem lockSet_tcbSuspendOnCore_covers_tail (st : SystemState)
    (callerTid : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (targetTid : SeLe4n.ThreadId) :
    (∀ sc, (suspendDonationCancelTailOf? st targetTid).scId? = some sc →
      (schedContextLock sc, AccessMode.write)
        ∈ (lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid).pairs) ∧
    (∀ ot, (suspendDonationCancelTailOf? st targetTid).owner? = some ot →
      (tcbLock ot, AccessMode.write)
        ∈ (lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid).pairs) ∧
    (∀ r, (suspendDonationCancelTailOf? st targetTid).head? = some r →
      (replyLock r, AccessMode.write)
        ∈ (lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid).pairs) ∧
    (∀ r, (suspendDonationCancelTailOf? st targetTid).belowHead? = some r →
      (replyLock r, AccessMode.write)
        ∈ (lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid).pairs) ∧
    (∀ ot, (suspendDonationCancelTailOf? st targetTid).outer? = some ot →
      (lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid).containsKey
        (tcbLock ot) = true) ∧
    (∀ sc, (suspendDonationCancelTailOf? st targetTid).scId? = some sc →
      (stateLevelLock, AccessMode.write)
        ∈ (lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid).pairs) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro sc h
    unfold lockSet_tcbSuspendOnCore
    rw [h]
    iterate 5 apply mem_write_lockSetExtendOpt
    simp only [lockSetExtendOpt, Option.map_some]
    exact self_write_mem_insertOrMerge _ (schedContextLock sc)
  · intro ot h
    unfold lockSet_tcbSuspendOnCore
    rw [h]
    iterate 4 apply mem_write_lockSetExtendOpt
    simp only [lockSetExtendOpt, Option.map_some]
    exact self_write_mem_insertOrMerge _ (tcbLock ot)
  · intro r h
    unfold lockSet_tcbSuspendOnCore
    rw [h]
    iterate 3 apply mem_write_lockSetExtendOpt
    simp only [lockSetExtendOpt, Option.map_some]
    exact self_write_mem_insertOrMerge _ (replyLock r)
  · intro r h
    unfold lockSet_tcbSuspendOnCore
    rw [h]
    iterate 2 apply mem_write_lockSetExtendOpt
    simp only [lockSetExtendOpt, Option.map_some]
    exact self_write_mem_insertOrMerge _ (replyLock r)
  · intro ot h
    unfold lockSet_tcbSuspendOnCore
    rw [h]
    apply containsKey_lockSetExtendOpt_of_containsKey
    simp only [lockSetExtendOpt, Option.map_some]
    exact containsKey_insertOrMerge_self _ (tcbLock ot) _
  · intro sc h
    unfold lockSet_tcbSuspendOnCore
    rw [h]
    simp only [Option.isSome_some, if_true]
    exact LockSet.mem_insertOrMerge_write_self _ _

/-- WS-OD (`v0.35.4`): the tail on a victim owed no donation is read off its own
binding — the bound arm. -/
theorem suspendDonationCancelTailOf?_of_bound (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (hT : st.getTcb? victimTid = some tcb)
    (hNoRes : Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb = none)
    (hB : tcb.schedContextBinding = .bound scId) :
    suspendDonationCancelTailOf? st victimTid = { scId? := some scId } := by
  unfold suspendDonationCancelTailOf? suspendDonationCancelTail?
  rw [hT]
  simp only [hNoRes, hB]

/-- WS-OD (`v0.35.4`): …and the donated arm. -/
theorem suspendDonationCancelTailOf?_of_donated (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (owner : SeLe4n.ThreadId)
    (hT : st.getTcb? victimTid = some tcb)
    (hNoRes : Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb = none)
    (hD : tcb.schedContextBinding = .donated scId owner) :
    suspendDonationCancelTailOf? st victimTid
      = { scId? := some scId, owner? := some owner, head? := replyStackHead? st scId,
          belowHead? := (replyStackBelowHead? st scId).1,
          outer? := (replyStackBelowHead? st scId).2 } := by
  unfold suspendDonationCancelTailOf? suspendDonationCancelTail?
  rw [hT]
  simp only [hNoRes, hD]

/-- WS-OD (`v0.35.4`): …and an unbound victim owed no donation adds nothing. -/
theorem suspendDonationCancelTailOf?_of_unbound (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB)
    (hT : st.getTcb? victimTid = some tcb)
    (hNoRes : Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb = none)
    (hU : tcb.schedContextBinding = .unbound) :
    suspendDonationCancelTailOf? st victimTid = {} := by
  unfold suspendDonationCancelTailOf? suspendDonationCancelTail?
  rw [hT]
  simp only [hNoRes, hU]

/-- WS-OD (`v0.35.4`): the tail on a victim owed a donation at the bottom of its
stack — the reclaim rebinds it `.bound`, and the bound arm's writes are the
cancellation footprint's members already. -/
theorem suspendDonationCancelTailOf?_of_reclaim_bottom (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (holder : SeLe4n.ThreadId)
    (hT : st.getTcb? victimTid = some tcb)
    (hRes : Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb = some (scId, holder))
    (hBottom : (replyStackBelowHead? st scId).2 = none) :
    suspendDonationCancelTailOf? st victimTid = {} := by
  unfold suspendDonationCancelTailOf? suspendDonationCancelTail?
  rw [hT]
  simp only [hRes, hBottom]

/-- WS-OD (`v0.35.4`): …and above the bottom, where the second pop's members are
the frame below the frame below the head and the outer caller the reclaim binds. -/
theorem suspendDonationCancelTailOf?_of_reclaim_outer (st : SystemState)
    (victimTid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (holder outer : SeLe4n.ThreadId)
    (hT : st.getTcb? victimTid = some tcb)
    (hRes : Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb = some (scId, holder))
    (hOuter : (replyStackBelowHead? st scId).2 = some outer) :
    suspendDonationCancelTailOf? st victimTid
      = { owner? := some outer,
          belowHead? := (replyStackSecondBelowHead? st scId).1,
          outer? := (replyStackSecondBelowHead? st scId).2 } := by
  unfold suspendDonationCancelTailOf? suspendDonationCancelTail?
  rw [hT]
  simp only [hRes, hOuter]

/-- **WS-OD (`v0.35.4`): the bound arm's writes are declared** — a victim owed no
donation and bound to `scId` has the context and the index under declared write
locks (its own TCB is `lockSet_tcbSuspendOnCore_covers_victim`). -/
theorem lockSet_tcbSuspendOnCore_covers_boundCancel (st : SystemState)
    (callerTid : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (targetTid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (hT : st.getTcb? targetTid = some tcb)
    (hNoRes : Lifecycle.Suspend.cancelledCallerDonation? st targetTid tcb = none)
    (hB : tcb.schedContextBinding = .bound scId) :
    (schedContextLock scId, AccessMode.write)
        ∈ (lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid).pairs ∧
    (stateLevelLock, AccessMode.write)
        ∈ (lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid).pairs := by
  have hTail := suspendDonationCancelTailOf?_of_bound st targetTid tcb scId hT hNoRes hB
  obtain ⟨hSc, -, -, -, -, hState⟩ :=
    lockSet_tcbSuspendOnCore_covers_tail st callerTid cnodeRootObjId targetTid
  exact ⟨hSc scId (by rw [hTail]), hState scId (by rw [hTail])⟩

/-- **WS-OD (`v0.35.4`): the donated arm's pop is declared** — a victim owed no
donation and holding `scId` donated by `owner` has the context, the owner, the
index, the head it clears and the frame below it re-heads under declared write
locks, and the outer caller it validates as a declared key. -/
theorem lockSet_tcbSuspendOnCore_covers_donatedCancel (st : SystemState)
    (callerTid : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (targetTid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (owner : SeLe4n.ThreadId)
    (hT : st.getTcb? targetTid = some tcb)
    (hNoRes : Lifecycle.Suspend.cancelledCallerDonation? st targetTid tcb = none)
    (hD : tcb.schedContextBinding = .donated scId owner) :
    (schedContextLock scId, AccessMode.write)
        ∈ (lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid).pairs ∧
    (tcbLock owner, AccessMode.write)
        ∈ (lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid).pairs ∧
    (stateLevelLock, AccessMode.write)
        ∈ (lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid).pairs ∧
    (∀ head, replyStackHead? st scId = some head →
      (replyLock head, AccessMode.write)
        ∈ (lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid).pairs) ∧
    (∀ below, (replyStackBelowHead? st scId).1 = some below →
      (replyLock below, AccessMode.write)
        ∈ (lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid).pairs) ∧
    (∀ outer, (replyStackBelowHead? st scId).2 = some outer →
      (lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid).containsKey
        (tcbLock outer) = true) := by
  have hTail := suspendDonationCancelTailOf?_of_donated st targetTid tcb scId owner hT hNoRes hD
  obtain ⟨hSc, hOwner, hHead, hBelow, hOuter, hState⟩ :=
    lockSet_tcbSuspendOnCore_covers_tail st callerTid cnodeRootObjId targetTid
  refine ⟨hSc scId (by rw [hTail]), hOwner owner (by rw [hTail]), hState scId (by rw [hTail]),
    ?_, ?_, ?_⟩
  · intro head h; exact hHead head (by rw [hTail]; exact h)
  · intro below h; exact hBelow below (by rw [hTail]; exact h)
  · intro outer h; exact hOuter outer (by rw [hTail]; exact h)

/-- **WS-OD (`v0.35.4`): the second pop is declared.**  A reply-arm victim owed a
donation whose stack has a frame below its head leaves the teardown
`.donated scId outer`, and the donated arm pops once more.  Its writes: the
context (the cancellation footprint's returned-donation member, lifted), the
frame below the original head — now the head — cleared (the cancellation
footprint's below-head write, lifted), the frame below *that* re-headed (the
tail's `belowHead?`), `outer` rebound (the tail's `owner?`), the index (the
cancellation footprint's state-level member, lifted); and it reads the second
frame's caller (the tail's `outer?`). -/
theorem lockSet_tcbSuspendOnCore_covers_reclaimSecondPop (st : SystemState)
    (callerTid : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (targetTid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (holder outer : SeLe4n.ThreadId)
    (hT : st.getTcb? targetTid = some tcb)
    (hRes : Lifecycle.Suspend.cancelledCallerDonation? st targetTid tcb = some (scId, holder))
    (hOuter : (replyStackBelowHead? st scId).2 = some outer) :
    (schedContextLock scId, AccessMode.write)
        ∈ (lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid).pairs ∧
    (tcbLock outer, AccessMode.write)
        ∈ (lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid).pairs ∧
    (stateLevelLock, AccessMode.write)
        ∈ (lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid).pairs ∧
    (∀ below, (replyStackBelowHead? st scId).1 = some below →
      (replyLock below, AccessMode.write)
        ∈ (lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid).pairs) ∧
    (∀ second, (replyStackSecondBelowHead? st scId).1 = some second →
      (replyLock second, AccessMode.write)
        ∈ (lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid).pairs) ∧
    (∀ so, (replyStackSecondBelowHead? st scId).2 = some so →
      (lockSet_tcbSuspendOnCore st callerTid cnodeRootObjId targetTid).containsKey
        (tcbLock so) = true) := by
  have hTail := suspendDonationCancelTailOf?_of_reclaim_outer st targetTid tcb scId holder outer
    hT hRes hOuter
  obtain ⟨hScC, -, hStateC, -, hBelowC⟩ :=
    lockSet_cancelIpcBlockingOnCore_covers_reclaim st targetTid tcb scId holder hT hRes
  obtain ⟨-, hOwner, -, hBelow, hOuterKey, -⟩ :=
    lockSet_tcbSuspendOnCore_covers_tail st callerTid cnodeRootObjId targetTid
  refine ⟨lockSet_tcbSuspendOnCore_covers_cancelIpcBlockingOnCore _ _ _ _ _ hScC,
    hOwner outer (by rw [hTail]),
    lockSet_tcbSuspendOnCore_covers_cancelIpcBlockingOnCore _ _ _ _ _ hStateC, ?_, ?_, ?_⟩
  · intro below h
    exact lockSet_tcbSuspendOnCore_covers_cancelIpcBlockingOnCore _ _ _ _ _ (hBelowC below h)
  · intro second h; exact hBelow second (by rw [hTail]; exact h)
  · intro so h; exact hOuterKey so (by rw [hTail]; exact h)

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
    (rdSc : Option SeLe4n.SchedContextId) (dhTid : Option SeLe4n.ThreadId)
    (holderEp : Option SeLe4n.ObjId)
    (holderNb : Option SeLe4n.ThreadId × Option SeLe4n.ThreadId)
    -- WS-OD OD3.7: declared **explicitly**.  Left off the binder list these two
    -- are auto-bound as implicits, so the arity the statement carries would be
    -- accidental rather than chosen — the same defect OD3.5 fixed one file over.
    (belowHeadReply? : Option SeLe4n.ReplyId) (outerCaller? : Option SeLe4n.ThreadId)
    -- WS-OD (`v0.35.4`): and the reclaimed head and the detached frame above.
    (reclaimHead? frameAbove? : Option SeLe4n.ReplyId)
    -- **WS-HP HP3.1**: the frame below the cut, which the splice re-links.
    (splicedBelow? : Option SeLe4n.ReplyId)
    (s : SystemState) :
    withLockSet (lockSet_cancelIpcBlocking victim blEp blN consumedReplyId rdSc dhTid holderEp holderNb belowHeadReply? outerCaller? reclaimHead? frameAbove? splicedBelow?)
        executingCore (fun st => (cancelIpcBlocking st victim tcb, ())) s
      = (unwindAll executingCore
          (lockSet_cancelIpcBlocking victim blEp blN consumedReplyId rdSc dhTid holderEp holderNb belowHeadReply? outerCaller? reclaimHead? frameAbove? splicedBelow?).lockAcquireSequence.reverse
          (cancelIpcBlocking
            (acquireAll executingCore
              (lockSet_cancelIpcBlocking victim blEp blN consumedReplyId rdSc dhTid holderEp holderNb belowHeadReply? outerCaller? reclaimHead? frameAbove? splicedBelow?).lockAcquireSequence s)
            victim tcb),
         ()) :=
  lockSet_atomic_under_2pl _ executingCore _ s

/-- WS-SM SM6.E.2 (companion): the cross-core cancellation composite is
likewise a single 2PL-atomic step under the same lock-set — the surfaced SGI
is computed inside the bracket and fired by the runtime after the commit. -/
theorem cancelIpcBlockingOnCore_atomic_under_lockSet
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (blEp blN : Option SeLe4n.ObjId) (consumedReplyId : Option SeLe4n.ReplyId)
    (rdSc : Option SeLe4n.SchedContextId) (dhTid : Option SeLe4n.ThreadId)
    (holderEp : Option SeLe4n.ObjId)
    (holderNb : Option SeLe4n.ThreadId × Option SeLe4n.ThreadId)
    -- WS-OD OD3.7: declared **explicitly**.  Left off the binder list these two
    -- are auto-bound as implicits, so the arity the statement carries would be
    -- accidental rather than chosen — the same defect OD3.5 fixed one file over.
    (belowHeadReply? : Option SeLe4n.ReplyId) (outerCaller? : Option SeLe4n.ThreadId)
    -- WS-OD (`v0.35.4`): and the reclaimed head and the detached frame above.
    (reclaimHead? frameAbove? : Option SeLe4n.ReplyId)
    -- **WS-HP HP3.1**: the frame below the cut, which the splice re-links.
    (splicedBelow? : Option SeLe4n.ReplyId)
    (s : SystemState) :
    withLockSet (lockSet_cancelIpcBlocking victim blEp blN consumedReplyId rdSc dhTid holderEp holderNb belowHeadReply? outerCaller? reclaimHead? frameAbove? splicedBelow?)
        executingCore (cancelIpcBlockingOnCore victim tcb executingCore) s
      = (unwindAll executingCore
          (lockSet_cancelIpcBlocking victim blEp blN consumedReplyId rdSc dhTid holderEp holderNb belowHeadReply? outerCaller? reclaimHead? frameAbove? splicedBelow?).lockAcquireSequence.reverse
          (cancelIpcBlockingOnCore victim tcb executingCore
            (acquireAll executingCore
              (lockSet_cancelIpcBlocking victim blEp blN consumedReplyId rdSc dhTid holderEp holderNb belowHeadReply? outerCaller? reclaimHead? frameAbove? splicedBelow?).lockAcquireSequence s)).1,
         (cancelIpcBlockingOnCore victim tcb executingCore
            (acquireAll executingCore
              (lockSet_cancelIpcBlocking victim blEp blN consumedReplyId rdSc dhTid holderEp holderNb belowHeadReply? outerCaller? reclaimHead? frameAbove? splicedBelow?).lockAcquireSequence s)).2) :=
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
    -- WS-OD (`v0.35.4`): at the pop's arity.
    (headReplyId belowHeadReplyId : Option SeLe4n.ReplyId)
    (outerCallerTid : Option SeLe4n.ThreadId)
    (s : SystemState) :
    withLockSet (lockSet_cancelDonation victim bindingScId donatedOriginalOwnerTid
            headReplyId belowHeadReplyId outerCallerTid)
        executingCore
        (fun st => match cancelDonation st victim tcb with
          | .ok st' => (st', Except.ok ())
          | .error e => (st, Except.error e)) s
      = (unwindAll executingCore
          (lockSet_cancelDonation victim bindingScId donatedOriginalOwnerTid
            headReplyId belowHeadReplyId outerCallerTid).lockAcquireSequence.reverse
          ((fun st => match cancelDonation st victim tcb with
            | .ok st' => (st', Except.ok ())
            | .error e => (st, Except.error e))
            (acquireAll executingCore
              (lockSet_cancelDonation victim bindingScId donatedOriginalOwnerTid
            headReplyId belowHeadReplyId outerCallerTid).lockAcquireSequence s)).1,
         ((fun st => match cancelDonation st victim tcb with
            | .ok st' => (st', Except.ok ())
            | .error e => (st, Except.error e))
            (acquireAll executingCore
              (lockSet_cancelDonation victim bindingScId donatedOriginalOwnerTid
            headReplyId belowHeadReplyId outerCallerTid).lockAcquireSequence s)).2) :=
  lockSet_atomic_under_2pl _ executingCore _ s

/-- WS-SM SM6.E.4 (companion): the per-core donation-cancellation dispatcher
is likewise a single 2PL-atomic step under the same lock-set. -/
theorem cancelDonationOnCore_atomic_under_lockSet
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (bindingScId : Option SeLe4n.SchedContextId)
    (donatedOriginalOwnerTid : Option SeLe4n.ThreadId)
    -- WS-OD (`v0.35.4`): at the pop's arity.
    (headReplyId belowHeadReplyId : Option SeLe4n.ReplyId)
    (outerCallerTid : Option SeLe4n.ThreadId)
    (s : SystemState) :
    withLockSet (lockSet_cancelDonation victim bindingScId donatedOriginalOwnerTid
            headReplyId belowHeadReplyId outerCallerTid)
        executingCore (cancelDonationOnCore victim tcb) s
      = (unwindAll executingCore
          (lockSet_cancelDonation victim bindingScId donatedOriginalOwnerTid
            headReplyId belowHeadReplyId outerCallerTid).lockAcquireSequence.reverse
          (cancelDonationOnCore victim tcb
            (acquireAll executingCore
              (lockSet_cancelDonation victim bindingScId donatedOriginalOwnerTid
            headReplyId belowHeadReplyId outerCallerTid).lockAcquireSequence s)).1,
         (cancelDonationOnCore victim tcb
            (acquireAll executingCore
              (lockSet_cancelDonation victim bindingScId donatedOriginalOwnerTid
            headReplyId belowHeadReplyId outerCallerTid).lockAcquireSequence s)).2) :=
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
    exact SystemState.updateTcb_preserves_objects_invExt _ _ _
      (SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hInv)
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
    -- Two in-place rewrites, a SchedContext then a TCB — neither is a
    -- notification, so the notification lookups are the pre-state's.
    have hInv1 : (st.updateSchedContext scId fun sc =>
        { sc with boundThread := none, isActive := false, donationOrigin := none }).objects.invExt :=
      SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hInv
    have hIpc1 : ipcInvariant (st.updateSchedContext scId fun sc =>
        { sc with boundThread := none, isActive := false, donationOrigin := none }) := by
      unfold SystemState.updateSchedContext
      split
      · intro oid ntfn hL
        exact hIpc oid ntfn (notification_lookup_of_insert_no_notification
          _ scId.toObjId _ hInv (fun _ hEq => KernelObject.noConfusion hEq) oid ntfn hL)
      · exact hIpc
    unfold SystemState.updateTcb
    split
    · intro oid ntfn hL
      exact hIpc1 oid ntfn (notification_lookup_of_insert_no_notification
        _ tid.toObjId _ hInv1 (fun _ hEq => KernelObject.noConfusion hEq) oid ntfn hL)
    · exact ipcInvariant_of_objects_eq rfl hIpc1
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
        (migrateSchedContextReplenishment_objects _ _ _ _)
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
    constructor <;>
      (rw [SystemState.updateTcb_scheduler, SystemState.updateSchedContext_scheduler];
       first | rfl | simp)
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
  rw [SystemState.updateTcb_scheduler, SystemState.updateSchedContext_scheduler]
  simp

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
    rw [SystemState.updateTcb_scheduler, SystemState.updateSchedContext_scheduler]
    simp [SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ _ _ _ hOther]
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

/-- WS-SM SM6.E.5 (plan §5 / §10 `cancellation_cross_core_correct`), re-keyed at
WS-RR RR8.6: a cancellation executed on core `executingCore` of a victim the
state **places** on a **different** core — and actively current there — is
fully correct across the core boundary:

1. **Remote poke** — a `.reschedule` SGI targeting the victim's placed core is
   surfaced, so that core stops executing the cancelled thread;
2. **Full deschedule at the placement** — the victim is neither in that core's
   run queue nor its current slot afterwards;
3. **Per-core locality** — every *other* core's current slot is exactly the
   pre-state's, and so is its run queue **unless** the OD1.7 wake targets it
   (a concurrent scheduling decision on a sibling core observes no change to
   its own scheduler state otherwise).  Two deliberate exclusions, both of
   them the reply arm's:

   * WS-RR RR7.22 (residual, remediation): the *replenish* queue is not part
     of this clause at all — the SM5.H migration moves the returned
     SchedContext's replenishments to the caller's home core, which may be
     neither this core nor the victim's.  A run queue and a current slot are
     what a sibling core's scheduling decision reads;
   * WS-OD OD1.7: the run-queue half is conditioned on
     `cancelAbortedHolderWakeCore?`, because the reclaim's abort unblocks the
     donation holder and this composite is what places it — on the *holder's*
     home core, which is likewise neither necessarily this core nor the
     victim's.  Excluding that one core is the honest statement; the previous
     unconditional one was true only because the holder was placed nowhere,
     which is precisely the defect OD1.7 closes.  The current-slot half is
     unconditional, since the wake inserts into a run queue and moves nothing
     onto a core;
4. **Object-level fidelity** — the object store is exactly the single-core
   `cancelIpcBlocking` teardown's (endpoint/notification dequeue, reply-link
   consume, TCB IPC-field clear), so every single-core teardown theorem
   (e.g. `cancelIpcBlocking_preserves_objects_invExt` and the
   `suspendThread_transientWindowInvariant` shape) transports to the
   cross-core composite unchanged.

Until RR8.6 the placed core was the victim's *home* (`determineTargetCore`),
and the hypotheses said so; a victim current on a core its home does not name —
an unpinned thread running on a secondary core — satisfied none of them, so the
flagship was silent on exactly the shape the deschedule got wrong.

Under the `cancelIpcBlocking` lock-set this whole step is 2PL-atomic
(`cancelIpcBlockingOnCore_atomic_under_lockSet`), which is what makes the
plan's "cancellation interleaves with wake" risk row (§7) unreachable: the
victim TCB write lock is held across all four effects. -/
theorem cancellation_cross_core_correct
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore c : CoreId)
    (st : SystemState)
    (hPlaced : placedCoreOf? st victim = some c)
    (hCur : st.scheduler.currentOnCore c = some victim)
    (hRemote : c ≠ executingCore) :
    (cancelIpcBlockingOnCore victim tcb executingCore st).2
      = some (c, SgiKind.reschedule)
    ∧ victim ∉ (cancelIpcBlockingOnCore victim tcb executingCore st).1.scheduler.runQueueOnCore c
    ∧ (cancelIpcBlockingOnCore victim tcb executingCore st).1.scheduler.currentOnCore c
        ≠ some victim
    ∧ (∀ c', c' ≠ c →
        cancelAbortedHolderWakeCore? st (cancelIpcBlockingMigrated victim tcb st) victim tcb
            ≠ some c' →
          (cancelIpcBlockingOnCore victim tcb executingCore st).1.scheduler.runQueueOnCore c'
            = st.scheduler.runQueueOnCore c')
    ∧ (∀ c', c' ≠ c →
        (cancelIpcBlockingOnCore victim tcb executingCore st).1.scheduler.currentOnCore c'
            = st.scheduler.currentOnCore c')
    ∧ (cancelIpcBlockingOnCore victim tcb executingCore st).1.objects
        = (cancelIpcBlocking st victim tcb).objects := by
  have hPost := cancelIpcBlockingOnCore_placedCoreOf?_of_some victim tcb st c hPlaced
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) remote poke
    exact cancelIpcBlockingOnCore_emits_sgi_if_remote_current victim tcb executingCore c st
      hPlaced hCur hRemote
  · -- (2a) not in the placed core's run queue
    rw [cancelIpcBlockingOnCore_state_eq]
    unfold descheduleAtPlacement descheduleAt
    simp only [hPost]
    exact removeRunnableOnCore_not_mem_self _ victim c
  · -- (2b) not the placed core's current
    rw [cancelIpcBlockingOnCore_state_eq]
    unfold descheduleAtPlacement descheduleAt
    simp only [hPost]
    exact removeRunnableOnCore_currentOnCore_ne_self _ victim c
  · -- (3a) per-core run-queue locality: teardown is scheduler-silent, removal is
    --      confined to the placed core, and the OD1.7 wake writes exactly the
    --      aborted holder's home core — which is why that core is excluded
    --      rather than the clause being weakened to say nothing.
    intro c' hc' hWake
    rw [cancelIpcBlockingOnCore_state_eq]
    unfold descheduleAtPlacement descheduleAt
    simp only [hPost]
    have hNe : c ≠ c' := fun h => hc' h.symm
    rw [removeRunnableOnCore_runQueueOnCore_ne _ victim c c' hNe,
        wakeAbortedDonationHolder_runQueueOnCore_ne _ _ victim tcb c' hWake,
        cancelIpcBlockingMigrated_runQueueOnCore, cancelIpcBlocking_scheduler_eq]
  · -- (3b) per-core current-slot locality: unconditional, because the wake
    --      inserts into a run queue and touches no core's current slot.
    intro c' hc'
    rw [cancelIpcBlockingOnCore_state_eq]
    unfold descheduleAtPlacement descheduleAt
    simp only [hPost]
    have hNe : c ≠ c' := fun h => hc' h.symm
    rw [removeRunnableOnCore_currentOnCore_ne _ victim c c' hNe,
        wakeAbortedDonationHolder_currentOnCore,
        cancelIpcBlockingMigrated_currentOnCore, cancelIpcBlocking_scheduler_eq]
  · -- (4) object-level fidelity
    exact cancelIpcBlockingOnCore_objects_eq victim tcb executingCore st

-- ============================================================================
-- §12  SM6.E — Scheduler-domain (`SchedLockId`) lock footprints
-- ============================================================================
-- The SM3.B object-domain `LockSet` footprints (§5) cover the cancellation's
-- kernel-object writes; the scheduler-slot writes — the placed core's run-queue
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

/-- WS-SM SM6.E, re-keyed at WS-RR RR8.6: the scheduler-domain footprint of
`descheduleThread` — the object-store table **write** lock and, when the state
places the thread anywhere, the run-queue **write** lock of the core it places
it on (the dequeue + current-slot clear).  At `some c` it is definitionally the
`wakeThreadLockSet` at `c` (`descheduleThreadLockSet_eq_wakeThreadLockSet`).

The object-store lock is not read by the deschedule itself since RR8.6 (the
placement scan reads scheduler slices only); it is kept because it is what
serialises the deschedule against a concurrent *wake* of the same thread — the
wake's footprint names the thread's home core's run-queue lock and the
deschedule's names its placed core's, which need not coincide, so the table
lock is the one member the dual operations are guaranteed to share.  Wider
than the operation's own reads, and in the direction this project rates safe. -/
def descheduleThreadLockSet (placed : Option CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  (SchedLockId.object schedObjStoreLockId, .write) ::
    (match placed with
     | some c => [(SchedLockId.runQueue ⟨c⟩, .write)]
     | none => [])

/-- WS-SM SM6.E: at a placed thread the deschedule footprint **is** the wake
footprint at that core — the dual operations serialise on exactly the same two
locks whenever the wake targets the placed core, and on the table lock always
(see the docstring above), which is what makes a concurrent wake/cancel race on
the same victim impossible under the `SchedLockId` bracket (the plan §7
"cancellation interleaves with wake" risk row, scheduler-domain half). -/
theorem descheduleThreadLockSet_eq_wakeThreadLockSet (c : CoreId) :
    descheduleThreadLockSet (some c) = wakeThreadLockSet c := rfl

/-- SM6.E: the deschedule footprint is the two-lock set at a placed thread... -/
@[simp] theorem descheduleThreadLockSet_length_some (c : CoreId) :
    (descheduleThreadLockSet (some c)).length = 2 := rfl

/-- ...and the table lock alone at a thread the state places nowhere. -/
@[simp] theorem descheduleThreadLockSet_none :
    descheduleThreadLockSet none
      = [(SchedLockId.object schedObjStoreLockId, Concurrency.AccessMode.write)] := rfl

/-- SM6.E: every lock in the deschedule footprint is acquired in **write**
mode. -/
theorem descheduleThreadLockSet_write_only (placed : Option CoreId) :
    ∀ p ∈ descheduleThreadLockSet placed, p.2 = Concurrency.AccessMode.write := by
  intro p hp
  cases placed with
  | none =>
    rw [descheduleThreadLockSet_none, List.mem_singleton] at hp
    subst hp
    rfl
  | some c => exact wakeThreadLockSet_write_only c p hp

/-- SM6.E: the object-store write lock is in the deschedule footprint. -/
theorem descheduleThreadLockSet_contains_objStore_write (placed : Option CoreId) :
    (SchedLockId.object schedObjStoreLockId, Concurrency.AccessMode.write)
      ∈ descheduleThreadLockSet placed := by
  unfold descheduleThreadLockSet
  exact List.mem_cons.mpr (Or.inl rfl)

/-- SM6.E: the placed core's run-queue write lock is in the deschedule
footprint — it guards the dequeue and the current-slot clear. -/
theorem descheduleThreadLockSet_contains_runQueue_write (c : CoreId) :
    (SchedLockId.runQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∈ descheduleThreadLockSet (some c) :=
  wakeThreadLockSet_contains_runQueue_write c

/-- SM6.E: the deschedule footprint's projected keys are duplicate-free. -/
theorem descheduleThreadLockSet_keys_nodup (placed : Option CoreId) :
    ((descheduleThreadLockSet placed).map (·.1)).Nodup := by
  cases placed with
  | none => simp [descheduleThreadLockSet_none]
  | some c => exact wakeThreadLockSet_keys_nodup c

/-- SM6.E: the deschedule footprint's keys form a `SchedLockId`-ascending
acquisition sequence. -/
theorem descheduleThreadLockSet_pairwise_le (placed : Option CoreId) :
    ((descheduleThreadLockSet placed).map (·.1)).Pairwise (· ≤ ·) := by
  cases placed with
  | none => simp [descheduleThreadLockSet_none]
  | some c => exact wakeThreadLockSet_pairwise_le c

/-- WS-SM SM6.E, re-keyed at WS-RR RR8.6: the scheduler-domain footprint of
`cancelIpcBlockingOnCore` — the deschedule footprint at the core the
**pre-state places the victim on**, **plus** the run-queue write lock of the
core the OD1.7 holder wake places onto, when it fires.

The object teardown's kernel-object writes are the §5 object-domain `LockSet`'s
concern; the composite's scheduler-slot writes are the placement removal and
that one insert.  The removal is resolved on the post-wake state and the
footprint on the pre-state; `cancelIpcBlockingOnCoreSchedLockSet_covers_deschedule`
is the relation between the two, and it is why the wake member covers even the
degenerate insert the wake could perform on the victim itself: that insert lands
on the declared wake core.

**WS-OD OD1.7: `wakeCore` is not optional decoration.**  The reclaim's wake
writes `runQueueOnCore (determineTargetCore st holder)`, and that core is
neither necessarily the victim's placed core nor the executing core — the
holder is a *third* thread with its own affinity.  A footprint that named only
the victim's core would be **false** of the transition, which this project
rates worse than a wide one, so the member is present exactly when the write is
(`cancelAbortedHolderWakeCore?` resolves it, and answers `none` on every arm but
a reply arm whose caller had donated).  A wake onto the victim's own placed core
contributes a duplicate key, which `cancelIpcBlockingOnCoreSchedLockSet_dedup`
removes rather than leaving to a `Nodup` obligation that would then be false. -/
def cancelIpcBlockingOnCoreSchedLockSet (placed wakeCore : Option CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  match wakeCore with
  | none => descheduleThreadLockSet placed
  | some c =>
    if placed = some c then descheduleThreadLockSet placed
    else descheduleThreadLockSet placed ++ [(SchedLockId.runQueue ⟨c⟩, .write)]

/-- WS-OD OD1.7: with no holder woken the footprint is the pre-OD1.7 one, which
is every arm but a reply arm whose caller had donated. -/
@[simp] theorem cancelIpcBlockingOnCoreSchedLockSet_none (placed : Option CoreId) :
    cancelIpcBlockingOnCoreSchedLockSet placed none = descheduleThreadLockSet placed := rfl

/-- WS-OD OD1.7: a wake onto the victim's own placed core adds no member — the
run-queue lock it would name is already held for the deschedule. -/
@[simp] theorem cancelIpcBlockingOnCoreSchedLockSet_dedup (c : CoreId) :
    cancelIpcBlockingOnCoreSchedLockSet (some c) (some c)
      = descheduleThreadLockSet (some c) := by
  unfold cancelIpcBlockingOnCoreSchedLockSet
  simp

/-- WS-OD OD1.7: every lock in the footprint is acquired in **write** mode —
the deschedule's two and the wake's insert are all mutations. -/
theorem cancelIpcBlockingOnCoreSchedLockSet_write_only (placed wakeCore : Option CoreId) :
    ∀ p ∈ cancelIpcBlockingOnCoreSchedLockSet placed wakeCore,
      p.2 = Concurrency.AccessMode.write := by
  intro p hp
  unfold cancelIpcBlockingOnCoreSchedLockSet at hp
  cases wakeCore with
  | none => exact descheduleThreadLockSet_write_only placed p hp
  | some c =>
    simp only [] at hp
    split at hp
    · exact descheduleThreadLockSet_write_only placed p hp
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with h | h
      · exact descheduleThreadLockSet_write_only placed p h
      · subst h; rfl

/-- WS-OD OD1.7: the footprint holds the woken core's run-queue write lock, so
the insert the reclaim performs is covered rather than merely permitted. -/
theorem cancelIpcBlockingOnCoreSchedLockSet_contains_wake_runQueue_write
    (placed : Option CoreId) (c : CoreId) (hc : placed ≠ some c) :
    (SchedLockId.runQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∈ cancelIpcBlockingOnCoreSchedLockSet placed (some c) := by
  unfold cancelIpcBlockingOnCoreSchedLockSet
  simp [hc]

/-- WS-OD OD1.7 / WS-RR RR8.6: ...and still holds the victim's placed core's
run-queue write lock, so widening the footprint costs the deschedule's own
coverage nothing. -/
theorem cancelIpcBlockingOnCoreSchedLockSet_contains_placed_runQueue_write
    (c : CoreId) (wakeCore : Option CoreId) :
    (SchedLockId.runQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∈ cancelIpcBlockingOnCoreSchedLockSet (some c) wakeCore := by
  unfold cancelIpcBlockingOnCoreSchedLockSet
  cases wakeCore with
  | none => exact descheduleThreadLockSet_contains_runQueue_write c
  | some w =>
    simp only []
    split
    · exact descheduleThreadLockSet_contains_runQueue_write c
    · exact List.mem_append.mpr (Or.inl (descheduleThreadLockSet_contains_runQueue_write c))

/-- **WS-RR RR8.6: the footprint covers the core the composite deschedules
at.**  The transition resolves the victim's placement on the post-wake state
and the footprint on the pre-state; the two agree unless the reclaim's wake
placed the victim itself (the degenerate `holder = victim` resolution, which no
reachable state produces), and that insert lands on the declared wake core —
so the run-queue lock the removal writes under is a declared member either
way.  Relation, not presence: the footprint is resolved from the pre-state
alone, as a footprint must be, and this is what ties it to a removal resolved
later. -/
theorem cancelIpcBlockingOnCoreSchedLockSet_covers_deschedule
    (victim : SeLe4n.ThreadId) (tcb : TCB) (st : SystemState) (c : CoreId)
    (h : placedCoreOf?
        (wakeAbortedDonationHolder st (cancelIpcBlockingMigrated victim tcb st) victim tcb)
        victim = some c) :
    (SchedLockId.runQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∈ cancelIpcBlockingOnCoreSchedLockSet (placedCoreOf? st victim)
          (cancelAbortedHolderWakeCore? st (cancelIpcBlockingMigrated victim tcb st)
            victim tcb) := by
  rcases cancelIpcBlockingOnCore_placedCoreOf?_cases victim tcb st with hEq | ⟨hPre, hPost⟩
  · rw [hEq] at h
    rw [h]
    exact cancelIpcBlockingOnCoreSchedLockSet_contains_placed_runQueue_write c _
  · rw [hPost] at h
    rw [hPre, h]
    exact cancelIpcBlockingOnCoreSchedLockSet_contains_wake_runQueue_write none c (by simp)

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
    schedCoreSegment (fun c => SchedLockId.replenishQueue ⟨c⟩) [victimHome, ownerHome]

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
  · exact schedCoreSegment_write_only _ _ p hp

/-- SM6.E: the victim's home-core replenish-queue write lock is in the
donated-arm footprint (the migration source / purge slot). -/
theorem cancelDonatedDonationOnCoreSchedLockSet_contains_victimHome_write
    (victimHome ownerHome : CoreId) :
    (SchedLockId.replenishQueue ⟨victimHome⟩, Concurrency.AccessMode.write)
      ∈ cancelDonatedDonationOnCoreSchedLockSet victimHome ownerHome := by
  refine List.mem_cons_of_mem _ ?_
  exact (mem_schedCoreSegment_iff replenishQueueLock_injective _ victimHome).mpr (by simp)

/-- SM6.E: the owner's home-core replenish-queue write lock is in the
donated-arm footprint (the migration destination). -/
theorem cancelDonatedDonationOnCoreSchedLockSet_contains_ownerHome_write
    (victimHome ownerHome : CoreId) :
    (SchedLockId.replenishQueue ⟨ownerHome⟩, Concurrency.AccessMode.write)
      ∈ cancelDonatedDonationOnCoreSchedLockSet victimHome ownerHome := by
  refine List.mem_cons_of_mem _ ?_
  exact (mem_schedCoreSegment_iff replenishQueueLock_injective _ ownerHome).mpr (by simp)

/-- SM6.E: the donated-arm footprint's projected keys are duplicate-free —
the segment carries one lock per distinct home core, and the object-store key
is of a different constructor. -/
theorem cancelDonatedDonationOnCoreSchedLockSet_keys_nodup
    (victimHome ownerHome : CoreId) :
    ((cancelDonatedDonationOnCoreSchedLockSet victimHome ownerHome).map (·.1)).Nodup := by
  unfold cancelDonatedDonationOnCoreSchedLockSet
  rw [List.map_cons]
  refine List.nodup_cons.mpr ⟨fun hMem => ?_,
    schedCoreSegment_keys_nodup replenishQueueLock_injective _⟩
  obtain ⟨_, _, hEq⟩ := schedCoreSegment_map_fst_mem hMem
  exact absurd hEq (by simp)

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
  rw [List.map_cons, List.pairwise_cons]
  refine ⟨?_, schedCoreSegment_pairwise_le _ _ (fun c d h => h)⟩
  intro x hx
  obtain ⟨c, _, rfl⟩ := schedCoreSegment_map_fst_mem hx
  exact hObjLe c

/-- WS-SM SM6.E: the scheduler-domain footprint of the donation-cancellation
**dispatcher** `cancelDonationOnCore` — the union over its arms: the
`.unbound` arm touches no scheduler slot, the `.bound` arm purges the
victim's home-core replenish queue (the `victimHome` member), and the
`.donated` arm additionally writes the owner's home-core queue (the
migration destination).  The donated-arm footprint is exactly that union. -/
def cancelDonationOnCoreSchedLockSet (victimHome ownerHome : CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  cancelDonatedDonationOnCoreSchedLockSet victimHome ownerHome

/-- **WS-RR RR8.12**: the suspend pipeline's G3 **is** this dispatcher.

G3 spells the three-way binding match out again rather than calling
`cancelDonationOnCore`, because the pipeline threads `Except KernelError
SystemState` while the dispatcher answers a pair — a second spelling of one
question, and the very shape that produced RR8.12's finding one level up: a step
added to the dispatcher would not reach the live path.  The two cannot be
collapsed without restating `cancelSuspendDonation_ipcInvariantStage` and every
proof that splits on G3's match, so they are **pinned** instead, which is what
this project prescribes when a second implementation must exist.

`rfl`: a step added to either side fails to elaborate this, on the day it is
written. -/
theorem suspendDonationArm_eq_cancelDonationOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) :
    (match tcb.schedContextBinding with
     | .unbound => (Except.ok st : Except KernelError SystemState)
     | .bound _ => cancelBoundDonationOnCore st tid tcb (determineTargetCore st tid)
     | .donated _ _ => cancelDonatedDonationOnCore st tid tcb)
      = (match (cancelDonationOnCore tid tcb st).2 with
         | .ok () => .ok (cancelDonationOnCore tid tcb st).1
         | .error e => .error e) := by
  unfold cancelDonationOnCore
  cases tcb.schedContextBinding with
  | unbound => rfl
  | bound scId =>
      cases cancelBoundDonationOnCore st tid tcb (determineTargetCore st tid) <;> rfl
  | donated scId owner => cases cancelDonatedDonationOnCore st tid tcb <;> rfl

-- WS-RR RR2.4 / RR2.10, superseded at WS-RR RR8.12: the sorted same-kind
-- scheduler-lock segment lives in `Scheduler/Operations/PerCoreChooseThread.lean`,
-- beside the `SchedLockId` order it is about, so the cross-core `.call` and
-- `.reply` dispatch footprints (which sit below this module and cannot import
-- it) share the one definition.  RR2.4 and RR2.10 relocated a two-endpoint and
-- a three-endpoint spelling; RR8.12 replaced both with `schedCoreSegment`, which
-- takes the *set* of cores, because a fourth arity was about to be needed and
-- the arity was never the question.

/-- WS-SM SM6.E, re-keyed at WS-RR RR8.6: the scheduler-domain footprint of
the cross-core suspend pipeline (`suspendThreadOnCore`, the G2..G7 composite):
the object-store table write lock; the **run-queue** write locks of the core
the pre-state **places** the victim on (`placedCoreOf?` — the G4 deschedule
writes that core's queue and current slot; absent when the victim is placed
nowhere, which is every genuinely blocked victim) and of the executing core
(the G7 reschedule — inline after a local deschedule, and the local-
disinheritance preemption gate `handleRescheduleSgiOnCore` may switch/re-enqueue
under the executing core's queue when the G2b PIP revert deboosted its current
thread, PR #831 review 3); and the replenish-queue write locks of the donation
arms (victim home = purge/migration source, owner home = the migration
destination, outer home = the second pop's destination), in the plan §4.4
cross-domain ascending order `object < runQueue < replenishQueue` with each
same-kind segment in `CoreId`-ascending order.

Until RR8.6 the run-queue segment was a triple over the victim's *home*, the
executing core and the core *running* it — the two proxies the G4/G4b removal
pair read, which between them miss a victim **queued** off its home.  The
segment is the pair the placement removal and the G7 gate actually write;
the home stays a *replenish* member, because the `.bound` arm's purge really is
keyed on it (SM5.H), and the running core needs no run-queue member of its own:
it is the placed core whenever the victim is current anywhere, and the G7
reschedule at it writes nothing there when it is remote (the SGI does the
work).

**WS-RR RR8.12: and the RECLAIM's wake core, which is a third.**  G2 carries
WS-OD OD1.7's holder wake since that cut, and the wake inserts the aborted
donation holder on the **holder's** home core — neither the victim's placement
nor the executing core, and the one core no member here named.  It is an
`Option`, resolved by `cancelAbortedHolderWakeCore?` on the reclaim's own state
pair, and `none` on every arm but a reply arm whose caller had donated; the
segment's canonical form collapses it where it coincides with a core already
named.  Widening costs the two existing members nothing
(`…_contains_placed_runQueue_write`, `…_contains_executing_runQueue_write`), and
`maxLockSetSize` does not move — a `SchedLockSet` carries no cardinality bound,
the ceiling being the *object* domain's.

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
`updatePipBoostOnCore` re-bucketing.

**WS-OD OD5.3: the replenish segment is a TRIPLE, because the pipeline pops
twice at call depth ≥ 2.**  The G2 teardown's reply arm reclaims the victim's
donation and rebinds the victim through `donationReturnBinding` -- which one
level up the reply stack is `.donated scId outer`, not `.bound scId` -- and the
arm selector below it re-reads the binding from the **post-teardown** TCB
(`tcb'`).  So the `.donated` arm fires on a victim that entered the syscall
`.unbound`, and its migration's destination is the *outer caller's* home core,
a third replenish core the pre-OD4 pair could not name: at the pre-state the
victim holds no binding at all, so a footprint resolved there would declare the
self-pair `home`/`home` while the operation writes `outer`'s queue.  A footprint
that omits a written lock is false, so the third core is declared -- and
over-declaring is the safe direction: where the second pop does not fire the
caller passes `home` and the triple collapses to the pre-OD5.3 pair. -/
def suspendThreadOnCoreSchedLockSet
    (home executingCore ownerHome outerHome : CoreId) (placed wakeCore : Option CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  (SchedLockId.object schedObjStoreLockId, .write) ::
  (schedCoreSegment (fun c => SchedLockId.runQueue ⟨c⟩)
      ([placed.getD executingCore, executingCore] ++ wakeCore.toList)
    ++ schedCoreSegment (fun c => SchedLockId.replenishQueue ⟨c⟩)
        [home, ownerHome, outerHome])

/-- **WS-RR RR8.12**: the footprint holds the woken core's run-queue write lock.

`cancelIpcBlockingOnCoreSchedLockSet_contains_wake_runQueue_write`'s twin, owed
from the cut that gave the live pipeline's G2 the reclaim's holder wake: a
footprint that omits a written lock is false, and this member is the one the wake
writes (`wakeAbortedDonationHolder_runQueueOnCore_ne` says it writes no other). -/
theorem suspendThreadOnCoreSchedLockSet_contains_wake_runQueue_write
    (home executingCore ownerHome outerHome : CoreId) (placed : Option CoreId) (c : CoreId) :
    (SchedLockId.runQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∈ suspendThreadOnCoreSchedLockSet home executingCore ownerHome outerHome placed (some c) := by
  unfold suspendThreadOnCoreSchedLockSet
  refine List.mem_cons_of_mem _ (List.mem_append_left _ ?_)
  exact (mem_schedCoreSegment_iff runQueueLock_injective _ c).mpr (by simp)

/-- **WS-RR RR8.12**: ...and still holds the victim's placed core's, so widening
the run-queue segment costs the placement removal's own coverage nothing. -/
theorem suspendThreadOnCoreSchedLockSet_contains_placed_runQueue_write
    (home executingCore ownerHome outerHome : CoreId) (c : CoreId) (wakeCore : Option CoreId) :
    (SchedLockId.runQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∈ suspendThreadOnCoreSchedLockSet home executingCore ownerHome outerHome (some c) wakeCore := by
  unfold suspendThreadOnCoreSchedLockSet
  refine List.mem_cons_of_mem _ (List.mem_append_left _ ?_)
  exact (mem_schedCoreSegment_iff runQueueLock_injective _ c).mpr (by simp)

/-- **WS-RR RR8.12**: ...and the executing core's, which the G7 local preemption
gate writes on every arm. -/
theorem suspendThreadOnCoreSchedLockSet_contains_executing_runQueue_write
    (home executingCore ownerHome outerHome : CoreId) (placed wakeCore : Option CoreId) :
    (SchedLockId.runQueue ⟨executingCore⟩, Concurrency.AccessMode.write)
      ∈ suspendThreadOnCoreSchedLockSet home executingCore ownerHome outerHome placed wakeCore := by
  unfold suspendThreadOnCoreSchedLockSet
  refine List.mem_cons_of_mem _ (List.mem_append_left _ ?_)
  exact (mem_schedCoreSegment_iff runQueueLock_injective _ executingCore).mpr (by simp)

/-- **WS-OD OD5.3: the second pop's migration endpoints, read off the operation.**

`cancelDonatedDonationOnCore` migrates the reclaimed context's replenishments
from the victim's own home core to the home of the thread its binding **records
as owner**.  At call depth 1 that thread is whoever donated to the victim; at
depth ≥ 2, after the G2 teardown has already reclaimed and rebound the victim
through `donationReturnBinding`, it is the *outer caller* the reply stack
resolved -- a core the pre-state binding does not mention, because the victim
entered the syscall `.unbound`.

Stated so the footprint's third replenish member has a consumer: the destination
is `determineTargetCore stC originalOwner`, and `originalOwner` is the binding's
own field rather than anything resolvable before the teardown ran. -/
theorem cancelDonatedDonationOnCore_migrates_to_recorded_owner
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hBind : tcb.schedContextBinding = .donated scId originalOwner)
    (h : cancelDonatedDonationOnCore st tid tcb = .ok st') :
    ∃ stC, cleanupDonatedSchedContext st tid = .ok stC ∧
      st' = migrateSchedContextReplenishment stC scId
        (determineTargetCore st tid) (determineTargetCore stC originalOwner) := by
  unfold cancelDonatedDonationOnCore at h
  rw [hBind] at h
  simp only [] at h
  cases hC : cleanupDonatedSchedContext st tid with
  | error e => rw [hC] at h; cases h
  | ok stC => rw [hC] at h; exact ⟨stC, rfl, (Except.ok.inj h).symm⟩

/-- SM6.E: the suspend footprint's keys form a `SchedLockId`-ascending
acquisition sequence — the full three-domain ladder
`object < runQueue < replenishQueue` with each same-kind segment's endpoints
in `CoreId`-ascending order. -/
theorem suspendThreadOnCoreSchedLockSet_pairwise_le
    (home executingCore ownerHome outerHome : CoreId) (placed wakeCore : Option CoreId) :
    ((suspendThreadOnCoreSchedLockSet home executingCore ownerHome outerHome
        placed wakeCore).map (·.1)).Pairwise (· ≤ ·) := by
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
    · obtain ⟨c, _, rfl⟩ := schedCoreSegment_map_fst_mem hx; exact hObjRQ c
    · obtain ⟨c, _, rfl⟩ := schedCoreSegment_map_fst_mem hx; exact hObjRep c
  · rw [List.pairwise_append]
    refine ⟨schedCoreSegment_pairwise_le _ _ (fun c d h => h),
      schedCoreSegment_pairwise_le _ _ (fun c d h => h), ?_⟩
    intro x hx y hy
    obtain ⟨c, _, rfl⟩ := schedCoreSegment_map_fst_mem hx
    obtain ⟨d, _, rfl⟩ := schedCoreSegment_map_fst_mem hy
    exact hRQRep c d

-- ============================================================================
-- §13  SM6.E — the live per-core suspend (the `.tcbSuspend` dispatch target)
-- ============================================================================

namespace Lifecycle.Suspend

/-- WS-SM SM6.E: the per-core suspend's **G7 dispatch** — the local/remote
reschedule seam factored out of `suspendThreadOnCore` so the SGI discipline is
provable arm-by-arm.  `runningCore` is the core the victim was current on
(`runningCoreOf?`; the executing core when it was current nowhere, since
WS-RR RR8.6).  Four arms:

* victim was current on the **executing** core (`wasCurrent ∧ runningCore = ec`):
  reschedule inline, surface nothing;
* victim was current on a **remote** core: surface that core's `.reschedule`
  SGI — running the local preemption gate first iff the G2b PIP revert
  deboosted the executing core's own current thread (`localDeboosted`,
  PR #831 review 2);
* victim not current anywhere: surface nothing — but still run the local
  preemption gate on a local disinheritance. -/
def suspendRescheduleOnCore (st : SystemState) (runningCore executingCore : CoreId)
    (wasCurrent localDeboosted : Bool)
    : Except KernelError (SystemState × Option (CoreId × SgiKind)) :=
  if wasCurrent then
    if runningCore == executingCore then
      match handleRescheduleSgiOnCore st executingCore with
      | .ok st' => .ok (st', none)
      | .error e => .error e
    else
      if localDeboosted then
        match handleRescheduleSgiOnCore st executingCore with
        | .ok st' => .ok (st', some (runningCore, SgiKind.reschedule))
        | .error e => .error e
      else
        .ok (st, some (runningCore, SgiKind.reschedule))
  else
    if localDeboosted then
      match handleRescheduleSgiOnCore st executingCore with
      | .ok st' => .ok (st', none)
      | .error e => .error e
    else
      .ok (st, none)

/-- WS-SM SM6.E (SGI discipline, G7-dispatch level): every SGI the dispatch
surfaces is a `.reschedule` targeting the running core, and only when that core
is remote. -/
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
* **G4-precapture (WS-RR RR8.6)** — the core the state **places** the victim
  on (`placedCoreOf?`: queued or current), read on the pre-state, where the
  scheduler footprint declares it, and removed at below.
* **G7-precapture** — the core actually **running** the victim
  (`runningCoreOf?`, pre-state resolution per the SM3.B discipline), which
  G7 must make choose a successor.
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
* **G4** — `descheduleAt` at the pre-captured placement: the victim leaves
  the run queue and the current slot of the core the state places it on.  The
  single-core form's bootCore-pinned `removeRunnable` left a remote victim
  queued/current on its home core — the multi-core correctness gap this
  wiring closes — and until WS-RR RR8.6 this step removed at the victim's
  *home* and, when it differed, at the core *running* it: two proxies for
  placement, which between them miss a victim **queued** off its home.  An
  unpinned thread (home = boot) preempted on a secondary core is re-enqueued
  on that core (`preemptCurrentOnCore`), so a suspend removed it from the boot
  queue it was not on, ran no running-core removal because it was not
  current, and left it queued while `.Inactive` — a `.tcbSuspend` that did
  not suspend, reachable with ordinary syscalls (pin to a secondary core, run
  there, unpin — `none` admits every core, so the running-thread refusal does
  not fire — be preempted).
* **G5/G6** — pending-state clear + `.Inactive` write (unchanged).
* **G7 (reschedule)** — mirrors `resumeThreadOnCore`'s H5 local/remote seam,
  keyed on the running core; a victim current nowhere needs no successor
  chosen, so its target defaults to the executing core, where no SGI arises:
  * **LOCAL** (running core = `executingCore`): the executing core suspended
    its own current thread — run the per-core reschedule handler inline
    (`handleRescheduleSgiOnCore`; the current slot was just vacated, so the
    preemption gate passes unconditionally and the successor is dispatched,
    or the core stays idle when its queue is empty).
  * **REMOTE** (running core ≠ `executingCore`): return the `.reschedule` SGI
    the running core must receive so it stops executing the suspended thread
    — the same SGI the diff seam re-derives (`crossCoreSgiBody`'s SM6.E
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
      -- home core of the victim: the `.bound` arm's replenish purge core
      -- (SM5.H: a bound thread's replenishments live on its home core),
      -- pre-state resolution; the teardown never moves it
      -- (`cancelIpcBlocking_determineTargetCore_eq`).  NOT where the victim
      -- is descheduled — that is its placement, next.
      let home := determineTargetCore st tid
      -- G4-precapture (WS-RR RR8.6): the core the state PLACES the victim on,
      -- queued or current — resolved on the pre-state, where
      -- `suspendThreadOnCoreSchedLockSet` declares it, and removed at below.
      -- Nothing between here and the removal moves THE VICTIM between scheduler
      -- slots: both donation arms write no run queue and no current slot, the
      -- priority-inheritance revert re-buckets a chain member inside the queue it
      -- already sits in, and G2's reclaim wake (WS-RR RR8.12) inserts the aborted
      -- donation *holder*, which is never the victim -- the wake fires only on a
      -- holder the pre-state has blocked sending or calling, and the victim is
      -- `.blockedOnReply`.  The sentence used to say "a thread" and no longer can:
      -- the teardown does move one, just not this one.
      let placed := placedCoreOf? st tid
      -- G7-precapture (PR #831 review 4, P1): the core ACTUALLY running the
      -- victim (`runningCoreOf?`) — an unbound victim can be current on a
      -- secondary core while its home is boot (see `runningCoreOf?`), and the
      -- poke must target the running core.  Under single placement it is the
      -- placed core whenever the victim is current anywhere; it is a separate
      -- read because G7 asks a different question of it (which core must
      -- choose a successor) than G4 does (where the thread is).
      let runningCore? := runningCoreOf? st tid
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
      -- G2 (**WS-RR RR8.12**): the teardown with its reclaim COMPLETED -- the
      -- migration and the holder wake, which until this cut were only in
      -- `cancelIpcBlockingOnCore`, a composite no production path calls.  See
      -- `cancelIpcBlockingReclaimed` for what the live path was therefore
      -- missing and for why the step takes this state pair.  It is NOT the whole
      -- composite: that ends in the victim's own deschedule, which G4 below
      -- performs at the pre-captured placement.
      let st := cancelIpcBlockingReclaimed tid tcb st
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
      -- G4 (WS-RR RR8.6): deschedule the victim where the state places it —
      -- one removal, at the pre-captured placement, in place of the home
      -- removal and the running-core removal that used to stand here.
      let st := descheduleAt st tid placed
      let st := clearPendingStateValid st vtid
      -- G6 (`v0.35.72`): the typed in-place rewrite -- the single-core
      -- `suspendThread`'s G6 since `v0.35.64`, and the identity on an absent
      -- thread, exactly as the raw store's own match was.
      let st := st.updateTcb tid fun t => { t with threadState := .Inactive }
      -- Local-disinheritance recheck (PR #831 review 2): the executing core's
      -- entry-time current thread is STILL current and its effective priority
      -- dropped across the pipeline (the G2b revert deboosted it) — a ready
      -- local thread may now outrank the running choice, and no SGI ever
      -- reaches the executing core, so G7 must run the local preemption gate.
      suspendRescheduleOnCore st (runningCore?.getD executingCore) executingCore
        runningCore?.isSome (currentDeboostedFrom st executingCore execCurPre)
  | none => .error .invalidArgument

-- ============================================================================
-- §14  WS-RR RR2.17 — the `.tcbSuspend` operation preserves `ipcInvariant`
-- ============================================================================
-- SM6.E closed `ipcInvariant` over the *cancellation composite*
-- (`cancelIpcBlockingOnCore`, `cancelDonationOnCore`).  The operation the live
-- `.tcbSuspend` arm actually runs is `suspendThreadOnCore`, which is that
-- composite plus five more stages: the cross-core priority-inheritance revert,
-- two home/running-core deschedules, the pending-state clear, the
-- `threadState := .Inactive` store, and the local scheduling point.  Each of
-- those writes TCBs or scheduler slots and nothing else, which is exactly what
-- `ipcInvariant` — a statement about notification objects — needs.

/-- WS-RR RR2.17: storing a `.tcb` cannot create a notification, so a
notification the post-state holds was already in the pre-state. -/
theorem tcbInsert_notification_backward (st : SystemState) (tid : SeLe4n.ThreadId)
    (t : TCB) (hInv : st.objects.invExt) (oid : SeLe4n.ObjId) (ntfn : Notification)
    (h : ({ st with objects := st.objects.insert tid.toObjId (.tcb t) } :
      SystemState).objects[oid]? = some (.notification ntfn)) :
    st.objects[oid]? = some (.notification ntfn) := by
  simp only [RHTable_getElem?_eq_get?] at h ⊢
  by_cases hEq : (tid.toObjId == oid) = true
  · exfalso
    obtain rfl : tid.toObjId = oid := eq_of_beq hEq
    rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _ hInv] at h
    cases h
  · rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne st.objects tid.toObjId oid _
      hEq hInv] at h
    exact h

/-- WS-RR RR2.17: `clearPendingState` writes one TCB, so it preserves the
object-store invariant. -/
theorem clearPendingState_preserves_objects_invExt (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    (Lifecycle.Suspend.clearPendingState st tid).objects.invExt := by
  unfold Lifecycle.Suspend.clearPendingState
  exact SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv

/-- WS-RR RR2.17: `clearPendingState` frames every notification. -/
theorem clearPendingState_notification_backward (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (oid : SeLe4n.ObjId) (ntfn : Notification)
    (h : (Lifecycle.Suspend.clearPendingState st tid).objects[oid]? = some (.notification ntfn)) :
    st.objects[oid]? = some (.notification ntfn) := by
  revert h
  unfold Lifecycle.Suspend.clearPendingState SystemState.updateTcb
  split
  · exact fun h => tcbInsert_notification_backward st tid _ hInv oid ntfn h
  · exact id

/-- WS-RR RR2.17: a successful suspend-reschedule either left the state alone or
ran exactly one `handleRescheduleSgiOnCore`.  Its four arms differ only in which
SGI they surface, which is why every state-level consequence factors through this
dichotomy instead of repeating the case split. -/
theorem suspendRescheduleOnCore_state_dichotomy (st st' : SystemState)
    (home ec : CoreId) (wc ld : Bool) (sgi? : Option (CoreId × SgiKind))
    (hStep : suspendRescheduleOnCore st home ec wc ld = .ok (st', sgi?)) :
    st' = st ∨ handleRescheduleSgiOnCore st ec = .ok st' := by
  revert hStep
  unfold suspendRescheduleOnCore
  split
  · split
    · cases hH : handleRescheduleSgiOnCore st ec with
      | error e => intro hStep; cases hStep
      | ok stH =>
        intro hStep
        simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
        exact Or.inr (hStep.1 ▸ rfl)
    · split
      · cases hH : handleRescheduleSgiOnCore st ec with
        | error e => intro hStep; cases hStep
        | ok stH =>
          intro hStep
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          exact Or.inr (hStep.1 ▸ rfl)
      · intro hStep
        simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
        exact Or.inl hStep.1.symm
  · split
    · cases hH : handleRescheduleSgiOnCore st ec with
      | error e => intro hStep; cases hStep
      | ok stH =>
        intro hStep
        simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
        exact Or.inr (hStep.1 ▸ rfl)
    · intro hStep
      simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
      exact Or.inl hStep.1.symm

/-- WS-RR RR2.17: the suspend's local scheduling point frames every
notification — its only object write is the preempted thread's context save. -/
theorem suspendRescheduleOnCore_notification_backward (st st' : SystemState)
    (home ec : CoreId) (wc ld : Bool) (sgi? : Option (CoreId × SgiKind))
    (hInv : st.objects.invExt) (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hStep : suspendRescheduleOnCore st home ec wc ld = .ok (st', sgi?))
    (h : st'.objects[oid]? = some (.notification ntfn)) :
    st.objects[oid]? = some (.notification ntfn) := by
  rcases suspendRescheduleOnCore_state_dichotomy st st' home ec wc ld sgi? hStep with
    hEq | hH
  · exact hEq ▸ h
  · exact handleRescheduleSgiOnCore_notification_backward st ec st' hInv oid ntfn hH h

/-- WS-RR RR2.17: the suspend's local scheduling point preserves the object-store
invariant. -/
theorem suspendRescheduleOnCore_preserves_objects_invExt (st st' : SystemState)
    (home ec : CoreId) (wc ld : Bool) (sgi? : Option (CoreId × SgiKind))
    (hInv : st.objects.invExt)
    (hStep : suspendRescheduleOnCore st home ec wc ld = .ok (st', sgi?)) :
    st'.objects.invExt := by
  rcases suspendRescheduleOnCore_state_dichotomy st st' home ec wc ld sgi? hStep with
    hEq | hH
  · exact hEq ▸ hInv
  · exact handleRescheduleSgiOnCore_preserves_objects_invExt st ec st' hInv hH

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
a `.reschedule` targeting the core **actually running** the victim
(`runningCoreOf?`), emitted only when that core is **remote** — the local case
reschedules inline and surfaces nothing.  Since WS-RR RR8.6 a victim current
nowhere falls back to the executing core, where no SGI can arise, so an SGI
*names* the running core rather than a home it may never have run on. -/
theorem suspendThreadOnCore_sgi_remote_reschedule (st st' : SystemState)
    (vtid : SeLe4n.ValidThreadId) (ec : CoreId) (c : CoreId) (k : SgiKind)
    (h : suspendThreadOnCore st vtid ec = .ok (st', some (c, k))) :
    runningCoreOf? st vtid.val = some c ∧ k = SgiKind.reschedule ∧ c ≠ ec := by
  simp only [suspendThreadOnCore] at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · obtain ⟨hc, hk, hne⟩ := suspendRescheduleOnCore_sgi_shape _ _ _ _ _ _ _ _ h
        refine ⟨?_, hk, hc ▸ hne⟩
        cases hR : runningCoreOf? st vtid.val with
        | none => exact absurd (by simp [hR]) hne
        | some r =>
          rw [hR] at hc
          simp only [Option.getD_some] at hc
          rw [hc]
  · cases h

/-- WS-SM SM6.E: a victim whose resolved reschedule target — the core
actually running it, or the executing core when it is current nowhere — is the
executing core surfaces no SGI: the reschedule (when needed) happened
inline. -/
theorem suspendThreadOnCore_local_no_sgi (st st' : SystemState)
    (vtid : SeLe4n.ValidThreadId) (ec : CoreId) (sgi : Option (CoreId × SgiKind))
    (hLocal : (runningCoreOf? st vtid.val).getD ec = ec)
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

-- WS-LC LC4.7: the per-primitive `invExt` preservation lemmas that stood here
-- are gone.  This file carried a *third* copy of them — `LockSetHeld` and
-- `NonInterferencePerCore` each had one too — because no two of those modules
-- are in each other's import closure.  They now live once, beside
-- `updateObjectLockAt` in `WithLockSet`, which all three import.

-- **WS-RR RR7.4**: the two lock-write stability lemmas that stood here —
-- `updateObjectLockAt_getTcb?_ipcState` and its `schedContextBinding` twin —
-- moved to `Locks/WithLockSet.lean`, beside `updateObjectLockAt` itself.  RR7.4
-- gives the same observer treatment to the five remaining SM6 transitions and
-- each of them needs the TCB-`ipcState` lemma; a copy per file is exactly the
-- duplication WS-LC LC4.7 removed for the `invExt` preservation family.

/-- WS-SM SM6.E: the cancellation's decisive business observable — the
victim's `ipcState` (the field the teardown transitions and the wake/suspend
race would corrupt). -/
def cancellationVictimIpcStateObserver (victim : SeLe4n.ThreadId) :=
  threadIpcStateObserver victim

/-- **WS-RR RR7.4**: the victim-`ipcState` observer reads only the object
store, and a lock-field-only write leaves it alone — the two facts the shared
`lockPrimitives_insensitiveOn_of_objectStoreObserver` needs. -/
theorem cancellationObserver_insensitiveOn (core : CoreId)
    (victim : SeLe4n.ThreadId) :
    AcquireInsensitiveOn (fun s => s.objects.invExt) core
      (cancellationVictimIpcStateObserver victim) ∧
    UnwindInsensitiveOn (fun s => s.objects.invExt) core
      (cancellationVictimIpcStateObserver victim) :=
  threadIpcStateObserver_insensitiveOn core victim

/-- WS-SM SM6.E: the victim-`ipcState` observer is `invExt`-guardedly
acquire-insensitive — every lock acquire is a lock-field-only write. -/
theorem cancellationObserver_acquireInsensitiveOn (core : CoreId)
    (victim : SeLe4n.ThreadId) :
    AcquireInsensitiveOn (fun s => s.objects.invExt) core
      (cancellationVictimIpcStateObserver victim) :=
  (cancellationObserver_insensitiveOn core victim).1

/-- WS-SM SM6.E: the victim-`ipcState` observer is `invExt`-guardedly
release-insensitive. -/
theorem cancellationObserver_unwindInsensitiveOn (core : CoreId)
    (victim : SeLe4n.ThreadId) :
    UnwindInsensitiveOn (fun s => s.objects.invExt) core
      (cancellationVictimIpcStateObserver victim) :=
  (cancellationObserver_insensitiveOn core victim).2

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
    (rdSc : Option SeLe4n.SchedContextId) (dhTid : Option SeLe4n.ThreadId)
    (holderEp : Option SeLe4n.ObjId)
    (holderNb : Option SeLe4n.ThreadId × Option SeLe4n.ThreadId)
    -- WS-OD (`v0.35.4`): declared explicitly, at the footprint's full arity.
    (belowHeadReply? : Option SeLe4n.ReplyId) (outerCaller? : Option SeLe4n.ThreadId)
    (reclaimHead? frameAbove? : Option SeLe4n.ReplyId)
    -- **WS-HP HP3.1**: the frame below the cut, which the splice re-links.
    (splicedBelow? : Option SeLe4n.ReplyId)
    (s : SystemState) (hInv : s.objects.invExt) :
    cancellationVictimIpcStateObserver victim
        (acquireAll executingCore
          (lockSet_cancelIpcBlocking victim blEp blN
            consumedReplyId rdSc dhTid holderEp holderNb belowHeadReply? outerCaller? reclaimHead? frameAbove? splicedBelow?).lockAcquireSequence s)
      = cancellationVictimIpcStateObserver victim s
    ∧ cancellationVictimIpcStateObserver victim
        (withLockSet (lockSet_cancelIpcBlocking victim blEp blN consumedReplyId rdSc dhTid holderEp holderNb belowHeadReply? outerCaller? reclaimHead? frameAbove? splicedBelow?)
          executingCore (cancelIpcBlockingOnCore victim tcb executingCore) s).1
      = cancellationVictimIpcStateObserver victim
          (cancelIpcBlockingOnCore victim tcb executingCore
            (acquireAll executingCore
              (lockSet_cancelIpcBlocking victim blEp blN
                consumedReplyId rdSc dhTid holderEp holderNb belowHeadReply? outerCaller? reclaimHead? frameAbove? splicedBelow?).lockAcquireSequence s)).1 := by
  have hAcqStable : ∀ (s' : SystemState) l m, s'.objects.invExt →
      (acquireLockOnObject s' executingCore l m).objects.invExt :=
    fun s' l m h => acquireLockOnObject_preserves_invExt s' executingCore l m h
  have hInvAcq : (acquireAll executingCore
      (lockSet_cancelIpcBlocking victim blEp blN
        consumedReplyId rdSc dhTid holderEp holderNb belowHeadReply? outerCaller? reclaimHead? frameAbove? splicedBelow?).lockAcquireSequence s).objects.invExt :=
    (acquireAll_lockInsensitiveOn _ executingCore _
      (cancellationObserver_acquireInsensitiveOn executingCore victim) hAcqStable
      _ s hInv).2
  exact lockSet_observer_atomic_on _ executingCore _ s
    (fun st => st.objects.invExt)
    (cancellationVictimIpcStateObserver victim)
    (cancellationObserver_acquireInsensitiveOn executingCore victim)
    (cancellationObserver_unwindInsensitiveOn executingCore victim)
    hAcqStable
    (fun s' l m h => releaseLockOnObject_preserves_invExt s' executingCore l m h)
    (fun s' l m h => cancelLockOnObject_preserves_invExt s' executingCore l m h)
    hInv
    (cancelIpcBlockingOnCore_preserves_objects_invExt victim tcb executingCore _ hInvAcq)

/-- Audit closure (F3ii): the cancellation's donation-side decisive
observable — the victim's `schedContextBinding`. -/
def cancellationVictimBindingObserver (victim : SeLe4n.ThreadId) :=
  fun s : SystemState => (s.getTcb? victim).map TCB.schedContextBinding

/-- **WS-RR RR7.4**: the binding observer's two facts, as above. -/
theorem cancellationBindingObserver_insensitiveOn (core : CoreId)
    (victim : SeLe4n.ThreadId) :
    AcquireInsensitiveOn (fun s => s.objects.invExt) core
      (cancellationVictimBindingObserver victim) ∧
    UnwindInsensitiveOn (fun s => s.objects.invExt) core
      (cancellationVictimBindingObserver victim) :=
  lockPrimitives_insensitiveOn_of_objectStoreObserver core _
    (fun _ _ h => by simp only [cancellationVictimBindingObserver,
      SystemState.getTcb?, h])
    (fun s l op hExt =>
      updateObjectLockAt_getTcb?_schedContextBinding s l op victim hExt)

/-- The binding observer is `invExt`-guardedly acquire-insensitive. -/
theorem cancellationBindingObserver_acquireInsensitiveOn (core : CoreId)
    (victim : SeLe4n.ThreadId) :
    AcquireInsensitiveOn (fun s => s.objects.invExt) core
      (cancellationVictimBindingObserver victim) :=
  (cancellationBindingObserver_insensitiveOn core victim).1

/-- The binding observer is `invExt`-guardedly release-insensitive. -/
theorem cancellationBindingObserver_unwindInsensitiveOn (core : CoreId)
    (victim : SeLe4n.ThreadId) :
    UnwindInsensitiveOn (fun s => s.objects.invExt) core
      (cancellationVictimBindingObserver victim) :=
  (cancellationBindingObserver_insensitiveOn core victim).2

/-- Audit closure (F3ii): the **donation-side observer capstone** — the 2PL
machinery around `cancelDonationOnCore` is invisible to the cancellation's
donation observable (the victim's `schedContextBinding`): the acquire phase
changes nothing the observer sees, and the bracketed run shows exactly the
transition's own effect.  The `schedContextBinding` mirror of
`cancelIpcBlockingOnCore_observer_atomic`. -/
theorem cancelDonationOnCore_observer_atomic
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (bindingScId : Option SeLe4n.SchedContextId)
    (donatedOwner : Option SeLe4n.ThreadId)
    -- WS-OD (`v0.35.4`): at the pop's arity.
    (headReplyId belowHeadReplyId : Option SeLe4n.ReplyId)
    (outerCallerTid : Option SeLe4n.ThreadId)
    (s : SystemState) (hInv : s.objects.invExt) :
    cancellationVictimBindingObserver victim
        (acquireAll executingCore
          (lockSet_cancelDonation victim bindingScId donatedOwner
            headReplyId belowHeadReplyId outerCallerTid).lockAcquireSequence s)
      = cancellationVictimBindingObserver victim s
    ∧ cancellationVictimBindingObserver victim
        (withLockSet (lockSet_cancelDonation victim bindingScId donatedOwner
            headReplyId belowHeadReplyId outerCallerTid)
          executingCore (cancelDonationOnCore victim tcb) s).1
      = cancellationVictimBindingObserver victim
          (cancelDonationOnCore victim tcb
            (acquireAll executingCore
              (lockSet_cancelDonation victim bindingScId donatedOwner
            headReplyId belowHeadReplyId outerCallerTid).lockAcquireSequence s)).1 := by
  have hAcqStable : ∀ (s' : SystemState) l m, s'.objects.invExt →
      (acquireLockOnObject s' executingCore l m).objects.invExt :=
    fun s' l m h => acquireLockOnObject_preserves_invExt s' executingCore l m h
  have hInvAcq : (acquireAll executingCore
      (lockSet_cancelDonation victim bindingScId donatedOwner
            headReplyId belowHeadReplyId outerCallerTid).lockAcquireSequence s).objects.invExt :=
    (acquireAll_lockInsensitiveOn _ executingCore _
      (cancellationBindingObserver_acquireInsensitiveOn executingCore victim) hAcqStable
      _ s hInv).2
  exact lockSet_observer_atomic_on _ executingCore _ s
    (fun st => st.objects.invExt)
    (cancellationVictimBindingObserver victim)
    (cancellationBindingObserver_acquireInsensitiveOn executingCore victim)
    (cancellationBindingObserver_unwindInsensitiveOn executingCore victim)
    hAcqStable
    (fun s' l m h => releaseLockOnObject_preserves_invExt s' executingCore l m h)
    (fun s' l m h => cancelLockOnObject_preserves_invExt s' executingCore l m h)
    hInv
    (cancelDonationOnCore_preserves_objects_invExt victim tcb _ hInvAcq)

-- ============================================================================
-- §15  SM6.E — boot-instance bridges + placement/affinity corollaries
-- ============================================================================

/-- WS-SM SM6.E, re-keyed at WS-RR RR8.6: at a victim the pre-state places on
the boot core — in particular every single-core configuration — the cross-core
cancellation's state is exactly the boot-pinned `removeRunnable` over the
teardown and the wake. -/
theorem cancelIpcBlockingOnCore_bootPlaced_state_eq
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId)
    (st : SystemState)
    (hPlaced : placedCoreOf? st victim = some bootCoreId) :
    (cancelIpcBlockingOnCore victim tcb executingCore st).1
      = removeRunnable
          (wakeAbortedDonationHolder st (cancelIpcBlockingMigrated victim tcb st) victim tcb)
          victim := by
  rw [cancelIpcBlockingOnCore_state_eq]
  unfold descheduleAtPlacement descheduleAt
  simp only [cancelIpcBlockingOnCore_placedCoreOf?_of_some victim tcb st bootCoreId hPlaced,
    removeRunnableOnCore_bootCoreId]

/-- WS-SM SM6.E (placement corollary), re-keyed at WS-RR RR8.6: under single
placement — the thread is queued or current on at most one core — the
deschedule removes it from **every** core: the placed core by the removal, and
every other core vacuously, because the thread was not there.

What the pre-RR8.6 statement needed instead was the *home-placement*
discipline — the thread sits only on `determineTargetCore`'s core — which is
false of an unpinned thread preempted off its home, so the corollary was silent
on exactly the shape the deschedule got wrong.  Single placement is what the
scheduler maintains by construction (`enqueueRunnableOnCore`'s global guard,
dequeue-on-dispatch, `currentThreadUniqueAcrossCores`). -/
theorem descheduleThread_fully_descheduled
    (st : SystemState) (tid : SeLe4n.ThreadId) (executingCore : CoreId)
    (hUnique : ∀ c c' : CoreId,
        (tid ∈ st.scheduler.runQueueOnCore c ∨ st.scheduler.currentOnCore c = some tid) →
        (tid ∈ st.scheduler.runQueueOnCore c' ∨ st.scheduler.currentOnCore c' = some tid) →
        c = c') :
    ∀ c : CoreId,
      tid ∉ (descheduleThread st tid executingCore).1.scheduler.runQueueOnCore c
      ∧ (descheduleThread st tid executingCore).1.scheduler.currentOnCore c
          ≠ some tid := by
  intro c
  cases hP : placedCoreOf? st tid with
  | none =>
    rw [descheduleThread_unplaced st tid executingCore hP]
    have hIs := placedCoreOf?_isSome_iff st tid
    rw [hP, Option.isSome_none] at hIs
    have hBoth := (Bool.or_eq_false_iff.mp hIs.symm)
    exact ⟨fun hMem => by
        have := not_placed_of_unplaced st tid hBoth.1 hBoth.2 c
        rw [Bool.or_eq_false_iff] at this
        exact absurd hMem (by simpa using this.1),
      fun hCur => by
        have := not_placed_of_unplaced st tid hBoth.1 hBoth.2 c
        rw [Bool.or_eq_false_iff] at this
        rw [hCur] at this
        simp at this⟩
  | some p =>
    by_cases hc : c = p
    · subst hc
      exact descheduleThread_descheduled_at_placement st tid executingCore c hP
    · obtain ⟨hRQ, hCur⟩ := descheduleThread_independent_of_other_core st tid executingCore c
        (fun h => hc (Option.some.inj (hP.symm.trans h)).symm)
      rw [hRQ, hCur]
      have hp := placedCoreOf?_sound st tid p hP
      have hPlacedP : tid ∈ st.scheduler.runQueueOnCore p
          ∨ st.scheduler.currentOnCore p = some tid := by
        rcases Bool.or_eq_true_iff.mp hp with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (by simpa using h2)
      exact ⟨fun hMem => hc (hUnique c p (Or.inl hMem) hPlacedP),
             fun hCurC => hc (hUnique c p (Or.inr hCurC) hPlacedP)⟩

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
  rw [SystemState.updateTcb_scheduler, SystemState.updateSchedContext_scheduler] at hMem
  by_cases hc : c = rqCore
  · subst hc
    simp only [SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_self] at hMem
    intro hEq
    have hf := (List.mem_filter.mp hMem).2
    simp [hEq] at hf
  · simp only [SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne
        _ _ _ _ (fun hEq => hc hEq.symm)] at hMem
    exact hOnlyHome c hc e hMem

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




/-- WS-RR RR2.17: one stage of a composite, as far as `ipcInvariant` is
concerned — it carries the object-store invariant its successor needs, and it
carries `ipcInvariant` itself.

Bundling the two is what makes an eight-stage composite eight one-line
compositions rather than eight interleaved inductions: each stage needs its
predecessor's `invExt` to state its own preservation, so neither fact can be
threaded alone. -/
structure IpcInvariantStage (st st' : SystemState) : Prop where
  /-- the object-store invariant survives the stage -/
  invExt : st.objects.invExt → st'.objects.invExt
  /-- and so does `ipcInvariant` -/
  ipc : st.objects.invExt → ipcInvariant st → ipcInvariant st'

namespace IpcInvariantStage

theorem refl (st : SystemState) : IpcInvariantStage st st := ⟨id, fun _ h => h⟩

theorem trans {st st' st'' : SystemState}
    (h1 : IpcInvariantStage st st') (h2 : IpcInvariantStage st' st'') :
    IpcInvariantStage st st'' :=
  ⟨h2.invExt ∘ h1.invExt,
   fun hInv hIpc => h2.ipc (h1.invExt hInv) (h1.ipc hInv hIpc)⟩

/-- A stage that leaves the object store alone. -/
theorem of_objects_eq {st st' : SystemState} (hObjs : st'.objects = st.objects) :
    IpcInvariantStage st st' :=
  ⟨fun h => by rw [hObjs]; exact h,
   fun _ h => ipcInvariant_of_objects_eq hObjs h⟩

/-- A stage whose every object write stores a `.tcb`: it cannot invent a
notification, so `ipcInvariant` transports backwards through its readings. -/
theorem of_notification_backward {st st' : SystemState}
    (hInvExt : st.objects.invExt → st'.objects.invExt)
    (hBack : ∀ (oid : SeLe4n.ObjId) (ntfn : Notification),
      st.objects.invExt →
      st'.objects[oid]? = some (.notification ntfn) →
      st.objects[oid]? = some (.notification ntfn)) :
    IpcInvariantStage st st' :=
  ⟨hInvExt, fun hInv hIpc oid ntfn hObj => hIpc oid ntfn (hBack oid ntfn hInv hObj)⟩

end IpcInvariantStage


/-- WS-RR RR2.17: the IPC teardown is a stage — SM6.E proved both halves. -/
theorem cancelIpcBlocking_ipcInvariantStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) : IpcInvariantStage st (cancelIpcBlocking st tid tcb) :=
  ⟨fun h => cancelIpcBlocking_preserves_objects_invExt st tid tcb h,
   fun hInv hIpc => cancelIpcBlocking_preserves_ipcInvariant st tid tcb hInv hIpc⟩

/-- **WS-RR RR8.12**: and so is the teardown with its reclaim completed — the
reclaim's migration and holder wake write only scheduler state
(`cancelIpcBlockingReclaimed_objects`), so the stage is the bare teardown's
followed by an object-store-preserving one. -/
theorem cancelIpcBlockingReclaimed_ipcInvariantStage (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) :
    IpcInvariantStage st (cancelIpcBlockingReclaimed tid tcb st) :=
  IpcInvariantStage.trans (cancelIpcBlocking_ipcInvariantStage st tid tcb)
    (IpcInvariantStage.of_objects_eq (cancelIpcBlockingReclaimed_objects tid tcb st))

/-- WS-RR RR2.17: the cross-core priority-inheritance revert is a stage — it
writes `pipBoost` and run-queue buckets, never a notification. -/
theorem propagatePipChainCrossCore_ipcInvariantStage (st : SystemState)
    (serverId : SeLe4n.ThreadId) (ec : CoreId) (fuel : Nat) :
    IpcInvariantStage st (PriorityInheritance.propagatePipChainCrossCore st serverId ec fuel).1 :=
  IpcInvariantStage.of_notification_backward
    (fun h => PriorityInheritance.propagatePipChainCrossCore_preserves_objects_invExt st
      serverId ec fuel h)
    (fun oid ntfn hInv hObj =>
      PriorityInheritance.propagatePipChainCrossCore_notification_backward st serverId ec fuel
        hInv oid ntfn hObj)

/-- WS-RR RR2.17: the donation-cancellation dispatcher is a stage on the arm that
succeeds; on an error arm the composite never reaches the next stage. -/
theorem cancelSuspendDonation_ipcInvariantStage (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (home : CoreId)
    (hStep : (match tcb.schedContextBinding with
              | .unbound => (Except.ok st : Except KernelError SystemState)
              | .bound _ => cancelBoundDonationOnCore st tid tcb home
              | .donated _ _ => cancelDonatedDonationOnCore st tid tcb) = .ok st') :
    IpcInvariantStage st st' := by
  revert hStep
  cases hB : tcb.schedContextBinding with
  | unbound =>
      intro hStep
      simp only [Except.ok.injEq] at hStep
      exact hStep ▸ IpcInvariantStage.refl st
  | bound scId =>
      cases hE : cancelBoundDonationOnCore st tid tcb home with
      | error e => intro hStep; cases hStep
      | ok stB =>
        intro hStep
        simp only [Except.ok.injEq] at hStep
        exact hStep ▸ ⟨fun h => cancelBoundDonationOnCore_preserves_objects_invExt st stB tid
            tcb home h hE,
          fun hInv hIpc => cancelBoundDonationOnCore_preserves_ipcInvariant st stB tid tcb home
            hInv hIpc hE⟩
  | donated scId owner =>
      cases hE : cancelDonatedDonationOnCore st tid tcb with
      | error e => intro hStep; cases hStep
      | ok stD =>
        intro hStep
        simp only [Except.ok.injEq] at hStep
        exact hStep ▸ ⟨fun h => cancelDonatedDonationOnCore_preserves_objects_invExt st stD tid
            tcb h hE,
          fun hInv hIpc => cancelDonatedDonationOnCore_preserves_ipcInvariant st stD tid tcb
            hInv hIpc hE⟩

/-- WS-RR RR2.17: the per-core deschedule is a stage — it writes no object. -/
theorem removeRunnableOnCore_ipcInvariantStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : CoreId) : IpcInvariantStage st (removeRunnableOnCore st tid c) :=
  IpcInvariantStage.of_objects_eq (removeRunnableOnCore_preserves_objects st tid c)

/-- WS-RR RR2.17: the pending-state clear is a stage — it writes one TCB. -/
theorem clearPendingState_ipcInvariantStage (st : SystemState) (tid : SeLe4n.ThreadId) :
    IpcInvariantStage st (Lifecycle.Suspend.clearPendingState st tid) :=
  IpcInvariantStage.of_notification_backward
    (fun h => clearPendingState_preserves_objects_invExt st tid h)
    (fun oid ntfn hInv hObj => clearPendingState_notification_backward st tid hInv oid ntfn hObj)

/-- WS-RR RR2.17: a single-TCB record store is a stage — the shape the suspend's
`threadState := .Inactive` write takes. -/
theorem tcbStore_ipcInvariantStage (st st' : SystemState) (tid : SeLe4n.ThreadId) (t : TCB)
    (hEq : st' = { st with objects := st.objects.insert tid.toObjId (.tcb t) }) :
    IpcInvariantStage st st' := by
  subst hEq
  exact IpcInvariantStage.of_notification_backward
    (fun h => RHTable_insert_preserves_invExt st.objects tid.toObjId _ h)
    (fun oid ntfn hInv hObj => tcbInsert_notification_backward st tid t hInv oid ntfn hObj)

/-- WS-RR RR2.17: the suspend's local scheduling point is a stage. -/
theorem suspendRescheduleOnCore_ipcInvariantStage (st st' : SystemState)
    (home ec : CoreId) (wc ld : Bool) (sgi? : Option (CoreId × SgiKind))
    (hStep : suspendRescheduleOnCore st home ec wc ld = .ok (st', sgi?)) :
    IpcInvariantStage st st' :=
  IpcInvariantStage.of_notification_backward
    (fun h => suspendRescheduleOnCore_preserves_objects_invExt st st' home ec wc ld sgi? h hStep)
    (fun oid ntfn hInv hObj =>
      suspendRescheduleOnCore_notification_backward st st' home ec wc ld sgi? hInv oid ntfn
        hStep hObj)





/-- WS-RR RR2.17 / WS-RR RR8.6: the placement removal is a stage on either
arm — a `removeRunnableOnCore` at the resolved core, or the identity at
`none`. -/
theorem descheduleAt_ipcInvariantStage (s : SystemState) (tid : SeLe4n.ThreadId)
    (placed : Option CoreId) : IpcInvariantStage s (descheduleAt s tid placed) := by
  unfold descheduleAt
  cases placed with
  | none => exact IpcInvariantStage.refl s
  | some c => exact removeRunnableOnCore_ipcInvariantStage s tid c

/-- `v0.35.72`: the typed in-place rewrite of one TCB is a stage — the shape the
suspend's `threadState := .Inactive` write takes since the raw store became
`updateTcb`.  Store-or-identity, decided by the primitive's own match rather
than by a case split at the composite. -/
theorem updateTcb_ipcInvariantStage (s : SystemState) (tid : SeLe4n.ThreadId)
    (f : TCB → TCB) :
    IpcInvariantStage s (s.updateTcb tid f) := by
  unfold SystemState.updateTcb
  split
  · exact tcbStore_ipcInvariantStage s _ tid _ rfl
  · exact IpcInvariantStage.refl s


/-- **WS-RR RR2.17: the operation the live `.tcbSuspend` arm runs is one
`IpcInvariantStage` end to end.**

SM6.E closed `ipcInvariant` over the *cancellation composite*
(`cancelIpcBlockingOnCore`, `cancelDonationOnCore`).  What the dispatch entry
actually calls is `suspendThreadOnCore`, which is that composite plus six more
stages: the cross-core priority-inheritance revert, the donated-context return,
the placement deschedule, the pending-state clear, the
`threadState := .Inactive` store, and the local scheduling point.  None of them
writes a notification object, which is the whole of what `ipcInvariant` says —
so the claim extends, and now says so about the reachable transition rather than
about a prefix of one.

The stage relation carries the object-store invariant alongside `ipcInvariant`,
because every stage needs its predecessor's to state its own preservation; that
is also why this is the shared root of both public forms below rather than each
of them re-running the chain. -/
theorem suspendThreadOnCore_ipcInvariantStage
    (st st' : SystemState) (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId)
    (sgi? : Option (CoreId × SgiKind))
    (hStep : suspendThreadOnCore st vtid executingCore = .ok (st', sgi?)) :
    IpcInvariantStage st st' := by
  have hChain : IpcInvariantStage st st' := by
    simp only [suspendThreadOnCore] at hStep
    split at hStep
    case h_2 => cases hStep
    case h_1 tcb hTcb =>
      split at hStep
      case isTrue => cases hStep
      case isFalse =>
        -- Stages 1-2: the IPC teardown, then the cross-core PIP revert.
        refine IpcInvariantStage.trans (st' := ?_) ?_ ?_
        · exact (match PriorityInheritance.blockingServer st vtid.val with
                 | some serverId => (PriorityInheritance.propagatePipChainCrossCore
                     (cancelIpcBlockingReclaimed vtid.val tcb st) serverId executingCore).1
                 | none => cancelIpcBlockingReclaimed vtid.val tcb st)
        · cases PriorityInheritance.blockingServer st vtid.val with
          | none => exact cancelIpcBlockingReclaimed_ipcInvariantStage st vtid.val tcb
          | some serverId =>
              exact IpcInvariantStage.trans
                (cancelIpcBlockingReclaimed_ipcInvariantStage st vtid.val tcb)
                (propagatePipChainCrossCore_ipcInvariantStage _ serverId executingCore _)
        · -- Stage 3 onwards, on the post-revert state.
          revert hStep
          split
          · intro hStep; cases hStep
          · next s3 hDon =>
            intro hStep
            refine IpcInvariantStage.trans
              (cancelSuspendDonation_ipcInvariantStage _ s3 vtid.val _
                (determineTargetCore st vtid.val) hDon) ?_
            refine IpcInvariantStage.trans ?_
              (suspendRescheduleOnCore_ipcInvariantStage _ st' _ executingCore _ _ sgi? hStep)
            refine IpcInvariantStage.trans
              (descheduleAt_ipcInvariantStage s3 vtid.val (placedCoreOf? st vtid.val)) ?_
            refine IpcInvariantStage.trans (clearPendingState_ipcInvariantStage _ vtid.val) ?_
            exact updateTcb_ipcInvariantStage _ vtid.val _
  exact hChain

/-- **WS-RR RR2.17: the live `.tcbSuspend` arm preserves the object-store
invariant.**  The extended-object invariant is the half of the stage relation
every later stage consumes to state its own preservation; exposing it is what
lets a caller compose `suspendThreadOnCore` with anything that needs
`invExt` of the post-state. -/
theorem suspendThreadOnCore_preserves_objects_invExt
    (st st' : SystemState) (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId)
    (sgi? : Option (CoreId × SgiKind))
    (hObjInv : st.objects.invExt)
    (hStep : suspendThreadOnCore st vtid executingCore = .ok (st', sgi?)) :
    st'.objects.invExt :=
  (suspendThreadOnCore_ipcInvariantStage st st' vtid executingCore sgi? hStep).invExt hObjInv

/-- **WS-RR RR2.17: the operation the live `.tcbSuspend` arm runs preserves
`ipcInvariant`.**  This is the theorem the pre-SM10 audit found missing: SM6.E's
five `*_preserves_ipcInvariant` composites are all about functions the module
header warns must not be wired live as-is, while `suspendThreadOnCore` — the one
`API.dispatchCapabilityOnly`'s `.tcbSuspend` arm and the
`suspend_thread_cross_core` seam actually call — carried no preservation theorem
at all. -/
theorem suspendThreadOnCore_preserves_ipcInvariant
    (st st' : SystemState) (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId)
    (sgi? : Option (CoreId × SgiKind))
    (hObjInv : st.objects.invExt) (hIpc : ipcInvariant st)
    (hStep : suspendThreadOnCore st vtid executingCore = .ok (st', sgi?)) :
    ipcInvariant st' :=
  (suspendThreadOnCore_ipcInvariantStage st st' vtid executingCore sgi? hStep).ipc hObjInv hIpc

-- ============================================================================
-- §15  WS-RR RR8.12 (Cut 4) — the reclaim's payoff reaches the end of the
--      suspend pipeline
-- ============================================================================
--
-- WS-OD OD1.7's `wakeAbortedDonationHolder_holder_runnable` says the reclaim
-- leaves the aborted donation holder queued or running.  The guarantee a user
-- sees is that a `.tcbSuspend` **does not strand the server its victim called**,
-- and G2 is only the first of seven stages — so until this section the guarantee
-- rested on `tests/SmpCancellationSuite.lean` §3.26 measuring it rather than on a
-- proof.  The six stages that follow either write objects alone, re-bucket a
-- thread inside the queue it already sits in, deschedule the **victim**, or run a
-- scheduling point; each is a frame, and the composition is the theorem.

-- **WS-RR RR8.12 (fifth cut)**: the four lemmas that read the wake's own guards
-- moved with the wake, to `SeLe4n/Kernel/Lifecycle/Suspend.lean`.  The payoff
-- below still consumes them; only their declaration site changed.

/-- **WS-RR RR8.12 (Cut 4)**: G2b — the priority-inheritance revert frames every
thread's placement.  A boost migrates a run-queue *bucket* and writes no
`current` slot, so the walk neither admits nor drops a member anywhere. -/
theorem propagatePipChainCrossCore_threadPlacedOnSomeCore (st : SystemState)
    (startTid u : SeLe4n.ThreadId) (ec : CoreId) (fuel : Nat) :
    threadPlacedOnSomeCore
        (PriorityInheritance.propagatePipChainCrossCore st startTid ec fuel).1 u
      = threadPlacedOnSomeCore st u :=
  threadPlacedOnSomeCore_congr_at st _ u
    (fun c => by
      rw [PriorityInheritance.propagatePipChainCrossCore_currentOnCore fuel st startTid ec c])
    (fun c =>
      PriorityInheritance.propagatePipChainCrossCore_mem_runQueueOnCore fuel st startTid u ec c)

/-- **WS-RR RR8.12 (Cut 4)**: G4 — the placement removal is about the **victim**,
so it frames every other thread's placement.  `threadPlacedOnSomeCore_congr` will
not serve here: the removal clears the victim's `current` slot, so the slots are
not equal; what is equal is what they say **about `u`**. -/
theorem descheduleAt_threadPlacedOnSomeCore_ne (st : SystemState)
    (tid u : SeLe4n.ThreadId) (placed : Option CoreId) (hNe : u ≠ tid) :
    threadPlacedOnSomeCore (descheduleAt st tid placed) u
      = threadPlacedOnSomeCore st u := by
  unfold descheduleAt
  cases placed with
  | none => rfl
  | some c =>
    refine threadPlacedOnSomeCore_congr_at st _ u ?_ ?_
    · intro c'
      by_cases hc : c' = c
      · subst hc
        rw [removeRunnableOnCore_currentOnCore_self]
        split
        · rename_i hCur
          constructor
          · intro hx; exact absurd hx (by simp)
          · intro hx; rw [hCur] at hx; exact absurd (Option.some.inj hx).symm hNe
        · exact Iff.rfl
      · rw [removeRunnableOnCore_currentOnCore_ne _ _ _ _ (fun hEq => hc hEq.symm)]
    · intro c'
      by_cases hc : c' = c
      · subst hc
        rw [removeRunnableOnCore_runQueueOnCore_self, RunQueue.mem_remove]
        exact ⟨fun hx => hx.1, fun hx => ⟨hx, hNe⟩⟩
      · rw [removeRunnableOnCore_runQueueOnCore_ne _ _ _ _ (fun hEq => hc hEq.symm)]

/-- **WS-RR RR8.12 (Cut 4)**: G7 — the suspend's scheduling point keeps a placed
thread placed.  Its identity arms are immediate and its three handler arms are
`handleRescheduleSgiOnCore`, through the dichotomy the module already states. -/
theorem suspendRescheduleOnCore_preserves_threadPlacedOnSomeCore
    (st st' : SystemState) (home ec : CoreId) (wc ld : Bool)
    (sgi? : Option (CoreId × SgiKind)) (u : SeLe4n.ThreadId)
    (hTcb : (st.getTcb? u).isSome)
    (hStep : suspendRescheduleOnCore st home ec wc ld = .ok (st', sgi?))
    (h : threadPlacedOnSomeCore st u = true) :
    threadPlacedOnSomeCore st' u = true := by
  rcases suspendRescheduleOnCore_state_dichotomy st st' home ec wc ld sgi? hStep with
    hEq | hH
  · exact hEq ▸ h
  · exact handleRescheduleSgiOnCore_preserves_threadPlacedOnSomeCore st st' ec u hTcb hH h

/-- **WS-RR RR8.12 (Cut 4)**: the bound arm's per-core purge destroys no TCB —
its two typed writes are a SchedContext rewrite and an in-place TCB rewrite, and
the two record updates between them touch the scheduler and the SchedContext
index rather than the object store. -/
theorem cancelBoundDonationOnCore_getTcb?_isSome (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (rqCore : CoreId) (u : SeLe4n.ThreadId)
    (hInv : st.objects.invExt)
    (hStep : cancelBoundDonationOnCore st tid tcb rqCore = .ok st')
    (h : (st.getTcb? u).isSome) : (st'.getTcb? u).isSome := by
  simp only [cancelBoundDonationOnCore] at hStep
  split at hStep
  · rename_i scId _
    rw [← Except.ok.inj hStep]
    refine SystemState.updateTcb_getTcb?_isSome _ tid _ ?_ u ?_
    · exact SystemState.updateSchedContext_preserves_objects_invExt st scId _ hInv
    · exact (SystemState.updateSchedContext_getTcb? st scId _ hInv u) ▸ h
  · exact absurd hStep (by simp)

/-- **WS-RR RR8.12 (Cut 4)**: and the donated arm destroys none either — the
donation pop rewrites bindings in place and the replenishment migration writes
only replenish queues. -/
theorem cancelDonatedDonationOnCore_getTcb?_isSome (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (u : SeLe4n.ThreadId)
    (hInv : st.objects.invExt)
    (hStep : cancelDonatedDonationOnCore st tid tcb = .ok st')
    (h : (st.getTcb? u).isSome) : (st'.getTcb? u).isSome := by
  simp only [cancelDonatedDonationOnCore] at hStep
  split at hStep
  · split at hStep
    · exact absurd hStep (by simp)
    · rename_i stC hC
      rw [← Except.ok.inj hStep, migrateSchedContextReplenishment_getTcb?]
      exact cleanupDonatedSchedContext_getTcb?_isSome st stC tid u hInv hC h
  · exact absurd hStep (by simp)

/-- **WS-RR RR8.12 (Cut 4)**: G3 — the donation-cancellation dispatcher frames
every thread's placement, on both arms.  Donation cancellation wakes nothing and
deschedules nothing, which is the SM6.E.3 reading; this is that reading in the
vocabulary the payoff composes. -/
theorem cancelSuspendDonation_threadPlacedOnSomeCore (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (home : CoreId) (u : SeLe4n.ThreadId)
    (hStep : (match tcb.schedContextBinding with
              | .unbound => (Except.ok st : Except KernelError SystemState)
              | .bound _ => cancelBoundDonationOnCore st tid tcb home
              | .donated _ _ => cancelDonatedDonationOnCore st tid tcb) = .ok st') :
    threadPlacedOnSomeCore st' u = threadPlacedOnSomeCore st u := by
  revert hStep
  cases hB : tcb.schedContextBinding with
  | unbound =>
      intro hStep
      rw [← Except.ok.inj hStep]
  | bound scId =>
      cases hE : cancelBoundDonationOnCore st tid tcb home with
      | error e => intro hStep; exact absurd hStep (by simp)
      | ok stB =>
        intro hStep
        rw [← Except.ok.inj hStep]
        exact threadPlacedOnSomeCore_congr st stB u
          (fun c => (cancelBoundDonationOnCore_runQueue_current_eq st stB tid tcb home c hE).2)
          (fun c => by
            rw [(cancelBoundDonationOnCore_runQueue_current_eq st stB tid tcb home c hE).1])
  | donated scId owner =>
      cases hE : cancelDonatedDonationOnCore st tid tcb with
      | error e => intro hStep; exact absurd hStep (by simp)
      | ok stD =>
        intro hStep
        rw [← Except.ok.inj hStep]
        exact threadPlacedOnSomeCore_congr st stD u
          (fun c => (cancelDonatedDonationOnCore_runQueue_current_eq st stD tid tcb c hE).2)
          (fun c => by
            rw [(cancelDonatedDonationOnCore_runQueue_current_eq st stD tid tcb c hE).1])

/-- **WS-RR RR8.12 (Cut 4)**: ...and destroys no TCB, on either arm. -/
theorem cancelSuspendDonation_getTcb?_isSome (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (home : CoreId) (u : SeLe4n.ThreadId)
    (hInv : st.objects.invExt)
    (hStep : (match tcb.schedContextBinding with
              | .unbound => (Except.ok st : Except KernelError SystemState)
              | .bound _ => cancelBoundDonationOnCore st tid tcb home
              | .donated _ _ => cancelDonatedDonationOnCore st tid tcb) = .ok st')
    (h : (st.getTcb? u).isSome) : (st'.getTcb? u).isSome := by
  revert hStep
  cases hB : tcb.schedContextBinding with
  | unbound =>
      intro hStep
      rw [← Except.ok.inj hStep]; exact h
  | bound scId =>
      cases hE : cancelBoundDonationOnCore st tid tcb home with
      | error e => intro hStep; exact absurd hStep (by simp)
      | ok stB =>
        intro hStep
        rw [← Except.ok.inj hStep]
        exact cancelBoundDonationOnCore_getTcb?_isSome st stB tid tcb home u hInv hE h
  | donated scId owner =>
      cases hE : cancelDonatedDonationOnCore st tid tcb with
      | error e => intro hStep; exact absurd hStep (by simp)
      | ok stD =>
        intro hStep
        rw [← Except.ok.inj hStep]
        exact cancelDonatedDonationOnCore_getTcb?_isSome st stD tid tcb u hInv hE h

/-- **WS-RR RR8.12 (Cut 4) — the payoff: a `.tcbSuspend` does not strand the
server its victim called.**

WS-OD OD1.7's `wakeAbortedDonationHolder_holder_runnable` says the reclaim's wake
leaves the aborted donation holder placed.  That is a statement about the state
**G2** leaves, and the live `.tcbSuspend` runs six more stages after it — so
until this theorem the user-visible guarantee rested on
`tests/SmpCancellationSuite.lean` §3.26 *measuring* the whole transition rather
than on a proof of it.  This is that lift, and it is a composition of frames
rather than a new argument: the chain revert re-buckets inside the queue a thread
already sits in, both donation arms wake and deschedule nothing, the placement
removal is about the **victim**, the pending-state clear and the `.Inactive`
write touch objects alone, and the scheduling point re-enqueues what it displaces.

**Two hypotheses are load-bearing rather than bookkeeping.**  `holder ≠ victim`
is not assumed — it is `cancelAbortedHolderWake?_ne_victim`, derived from the
wake's own two guards, which is what licenses G4 to leave the holder alone.  And
the holder's TCB has to travel *with* its placement: a scheduling point strands a
thread whose TCB does not resolve (`preemptCurrentOnCore` re-enqueues the
outgoing thread only when it does), so the chain carries resolvability forward at
every stage rather than assuming it at the end. -/
theorem suspendThreadOnCore_holder_still_placed
    (st st' : SystemState) (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId)
    (sgi? : Option (CoreId × SgiKind)) (tcb : TCB)
    (holder : SeLe4n.ThreadId) (t : TCB)
    (hObjInv : st.objects.invExt)
    (hTcb : st.getTcb? vtid.val = some tcb)
    (hW : cancelAbortedHolderWake? st (cancelIpcBlockingMigrated vtid.val tcb st)
            vtid.val tcb = some holder)
    (hT : (cancelIpcBlockingMigrated vtid.val tcb st).getTcb? holder = some t)
    (hStep : suspendThreadOnCore st vtid executingCore = .ok (st', sgi?)) :
    threadPlacedOnSomeCore st' holder = true := by
  have hNe : holder ≠ vtid.val :=
    cancelAbortedHolderWake?_ne_victim st _ vtid.val tcb holder hTcb hW
  -- G2 — the reclaim, where OD1.7's payoff lands.
  have hP1 : threadPlacedOnSomeCore (cancelIpcBlockingReclaimed vtid.val tcb st) holder
      = true := by
    have hRun := wakeAbortedDonationHolder_holder_runnable st
      (cancelIpcBlockingMigrated vtid.val tcb st) vtid.val tcb holder t hW hT
    show (threadRunningOnSomeCore _ holder || threadQueuedOnSomeCore _ holder) = true
    unfold threadRunningOnSomeCore threadQueuedOnSomeCore
    rw [Bool.or_comm]
    exact hRun
  have hS1 : ((cancelIpcBlockingReclaimed vtid.val tcb st).getTcb? holder).isSome := by
    show ((wakeAbortedDonationHolder st (cancelIpcBlockingMigrated vtid.val tcb st)
      vtid.val tcb).getTcb? holder).isSome
    rw [wakeAbortedDonationHolder_getTcb?, hT]
    rfl
  have hI1 : (cancelIpcBlockingReclaimed vtid.val tcb st).objects.invExt :=
    (cancelIpcBlockingReclaimed_ipcInvariantStage st vtid.val tcb).invExt hObjInv
  simp only [suspendThreadOnCore] at hStep
  split at hStep
  case h_2 => exact absurd hStep (by simp)
  case h_1 tcb0 hTcb0 =>
    obtain rfl : tcb = tcb0 := by rw [hTcb] at hTcb0; exact Option.some.inj hTcb0
    split at hStep
    case isTrue => exact absurd hStep (by simp)
    case isFalse =>
      -- G2b — the cross-core priority-inheritance revert.
      have hP2 : threadPlacedOnSomeCore
          (match PriorityInheritance.blockingServer st vtid.val with
           | some serverId => (PriorityInheritance.propagatePipChainCrossCore
               (cancelIpcBlockingReclaimed vtid.val tcb st) serverId executingCore).1
           | none => cancelIpcBlockingReclaimed vtid.val tcb st) holder = true := by
        cases PriorityInheritance.blockingServer st vtid.val with
        | none => exact hP1
        | some serverId =>
            rw [propagatePipChainCrossCore_threadPlacedOnSomeCore]; exact hP1
      have hS2 : ((match PriorityInheritance.blockingServer st vtid.val with
           | some serverId => (PriorityInheritance.propagatePipChainCrossCore
               (cancelIpcBlockingReclaimed vtid.val tcb st) serverId executingCore).1
           | none => cancelIpcBlockingReclaimed vtid.val tcb st).getTcb? holder).isSome := by
        cases PriorityInheritance.blockingServer st vtid.val with
        | none => exact hS1
        | some serverId =>
            exact PriorityInheritance.propagatePipChainCrossCore_getTcb?_isSome _ _ _ _ _ hI1 hS1
      have hI2 : (match PriorityInheritance.blockingServer st vtid.val with
           | some serverId => (PriorityInheritance.propagatePipChainCrossCore
               (cancelIpcBlockingReclaimed vtid.val tcb st) serverId executingCore).1
           | none => cancelIpcBlockingReclaimed vtid.val tcb st).objects.invExt := by
        cases PriorityInheritance.blockingServer st vtid.val with
        | none => exact hI1
        | some serverId =>
            exact PriorityInheritance.propagatePipChainCrossCore_preserves_objects_invExt
              _ _ _ _ hI1
      -- G3 onwards, on the post-revert state.
      revert hStep
      split
      · intro hStep; exact absurd hStep (by simp)
      · next s3 hDon =>
        intro hStep
        -- G3 — the donation arm.
        have hP3 : threadPlacedOnSomeCore s3 holder = true := by
          rw [cancelSuspendDonation_threadPlacedOnSomeCore _ s3 vtid.val _
            (determineTargetCore st vtid.val) holder hDon]
          exact hP2
        have hS3 : (s3.getTcb? holder).isSome :=
          cancelSuspendDonation_getTcb?_isSome _ s3 vtid.val _
            (determineTargetCore st vtid.val) holder hI2 hDon hS2
        have hI3 : s3.objects.invExt :=
          (cancelSuspendDonation_ipcInvariantStage _ s3 vtid.val _
            (determineTargetCore st vtid.val) hDon).invExt hI2
        -- G4 — the placement removal, which is about the VICTIM.
        have hP4 : threadPlacedOnSomeCore
            (descheduleAt s3 vtid.val (placedCoreOf? st vtid.val)) holder = true := by
          rw [descheduleAt_threadPlacedOnSomeCore_ne s3 vtid.val holder _ hNe]; exact hP3
        have hS4 : ((descheduleAt s3 vtid.val (placedCoreOf? st vtid.val)).getTcb? holder).isSome := by
          unfold descheduleAt
          cases placedCoreOf? st vtid.val with
          | none => exact hS3
          | some c => rw [removeRunnableOnCore_getTcb?]; exact hS3
        have hI4 : (descheduleAt s3 vtid.val (placedCoreOf? st vtid.val)).objects.invExt :=
          (descheduleAt_ipcInvariantStage s3 vtid.val (placedCoreOf? st vtid.val)).invExt hI3
        -- G5 / G6 — two object writes, both scheduler-free.
        have hP6 : threadPlacedOnSomeCore
            ((Lifecycle.Suspend.clearPendingState
              (descheduleAt s3 vtid.val (placedCoreOf? st vtid.val)) vtid.val).updateTcb
                vtid.val (fun t => { t with threadState := .Inactive })) holder = true := by
          rw [threadPlacedOnSomeCore_updateTcb, Lifecycle.Suspend.clearPendingState,
            threadPlacedOnSomeCore_updateTcb]
          exact hP4
        have hS6 : (((Lifecycle.Suspend.clearPendingState
              (descheduleAt s3 vtid.val (placedCoreOf? st vtid.val)) vtid.val).updateTcb
                vtid.val (fun t => { t with threadState := .Inactive })).getTcb? holder).isSome := by
          refine SystemState.updateTcb_getTcb?_isSome _ vtid.val _ ?_ holder ?_
          · exact (clearPendingState_ipcInvariantStage _ vtid.val).invExt hI4
          · exact SystemState.updateTcb_getTcb?_isSome _ vtid.val _ hI4 holder hS4
        have hI6 : ((Lifecycle.Suspend.clearPendingState
              (descheduleAt s3 vtid.val (placedCoreOf? st vtid.val)) vtid.val).updateTcb
                vtid.val (fun t => { t with threadState := .Inactive })).objects.invExt :=
          (updateTcb_ipcInvariantStage _ vtid.val _).invExt
            ((clearPendingState_ipcInvariantStage _ vtid.val).invExt hI4)
        -- G7 — the local scheduling point.
        exact suspendRescheduleOnCore_preserves_threadPlacedOnSomeCore _ st' _ executingCore
          _ _ sgi? holder hS6 hStep hP6

end SeLe4n.Kernel
