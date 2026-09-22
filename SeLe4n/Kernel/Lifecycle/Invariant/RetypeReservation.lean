-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Invariant.CancellationNotificationShape

/-!
# `v0.35.166` (WS-RR RR8.12, register row 63) — the destroy path's reservation theorems

`v0.35.164` gave the retype's TCB cleanup the suspend pipeline's donation arm
(`cancelDonationArmOnCore`, seL4's `finaliseCap` → `unbindFromSc`), and
`v0.35.165` gave its SchedContext cleanup the binding release
(`releaseSchedContextBinding`, seL4's `schedContext_unbindAllTCBs`).  Each landed
with the arm's own `replenishQueueAffinityConsistent_smp` theorem and **no
theorem about the program that runs it** — because a frame the composite needs
was `private` in a module the composite's own module cannot see.

## Why this module exists at all

`lifecyclePreRetypeCleanup` lives in `Lifecycle/Operations/CleanupPreservation.lean`
and `lifecycleRetypeDirectWithCleanup` in `Lifecycle/Operations/RetypeWrappers.lean`.
Between them the `.tcb` arm's reference sweep (`cleanupTcbReferences`) runs two
whole-store folds — `removeFromAllEndpointQueues` and
`removeFromAllNotificationWaitLists` — whose `getSchedContext?` and `cpuAffinity`
frames WS-RR RR8.11 wrote `private` in `IPC/Invariant/CancellationBundle.lean`,
which is **downstream of both**.  So neither program's own module could state a
reservation theorem over its own sweep, and register row 63 recorded the blocker
as a layering fact rather than an effort estimate.

`v0.35.166` moved each frame to the module holding the fact its proof rests on
(see that bundle's §4 tombstone for where each went), which puts all of
them in `CancellationNotificationShape`'s import closure — and that module is
downstream of the cleanup, of the retype wrapper and of `ReplenishAffinity`,
while nothing in the other direction imports it.  So this is where the two
composites can finally be stated, and it is the *only* place they can be.

## What is proved

* §1 — the reference sweep's frames (`cleanupTcbReferences`): it moves no
  replenish entry, no scheduling context's `boundThread`, and no thread's home
  core, so it preserves the invariant.  Each is one application per step of a
  frame that already existed; what did not exist is the composition, because the
  two sweeps' halves were out of reach.
* §2 — `lifecyclePreRetypeCleanup_preserves_replenishQueueAffinityConsistent_smp`,
  over all six object kinds.  The two arms that *do* move a reservation
  (`.tcb`'s `cancelDonationArmOnCore`, `.schedContext`'s
  `releaseSchedContextBinding`) cite the theorems `v0.35.164` and `v0.35.165`
  proved of them; the other four move none.

## What is deliberately **not** proved here, and why

Two things, and both are **effort** facts rather than layering ones — which is
the whole of what this cut changes about register row 63's remainder.

**`schedContextBindingConsistent` across either program.**  Measured on the tree
at `v0.35.165`: there is no `preserves_schedContextBindingConsistent` theorem
anywhere — not for a queue sweep, not for the two donation arms, not for
`storeObject` — so the reciprocity would have to be built for eight operations
before either composite could cite it.  Its *behaviour* is not unwitnessed:
`tests/SmpIpcSuite.lean` §3.31 and §3.32 assert the decidable reading of it on
every post-retype state they produce, with the retired cleanup computed beside
the live one falsifying it.

**The retype composite's own preservation of the affinity invariant.**
`lifecycleRetypeDirectWithCleanup` runs this cleanup, then `scrubObjectMemory`
(which frames both `objects` and `scheduler` outright), then a `storeObject` of
the replacement at `target` — and the store is what needs more than a frame: it
rewrites `getSchedContext?` and `determineTargetCore` at `target`, so the
invariant survives it exactly when no surviving scheduling context is bound to
the thread the retype destroys.  That is a consequence of
`schedContextBindingConsistent` and of the target's binding after the cleanup, so
it is the *first* thing the deferred half buys and it cannot be had before it.
Stating it as a hypothesis instead would be a predicate no transition
establishes, which `v0.35.126` (WS-RR RR8.16) is the tree's own name for.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.RobinHood
open SeLe4n.Kernel.Concurrency (CoreId)

-- ============================================================================
-- §1  The reference sweep's frames
-- ============================================================================

/-- `v0.35.166`: the reference sweep preserves the object store's extension
invariant — the run-queue removal writes no object at all, and each of the three
folds after it preserves it. -/
theorem cleanupTcbReferences_preserves_objects_invExt (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    (cleanupTcbReferences st tid).objects.invExt := by
  unfold cleanupTcbReferences
  refine clearDonationOriginReferences_preserves_objects_invExt _ tid ?_
  refine removeFromAllNotificationWaitLists_preserves_objects_invExt _ tid ?_
  refine removeFromAllEndpointQueues_preserves_objects_invExt _ tid ?_
  rw [removeRunnableFromAllCores_objects]
  exact hInv

/-- `v0.35.166`: the reference sweep moves no replenish entry.

Three of its four steps write no scheduler state at all and the fourth writes
only run queues, which is what `cleanupTcbReferences_scheduler_eq_removeRunnableFromAllCores`
already says; this reads the replenish projection off it. -/
theorem cleanupTcbReferences_replenishQueueOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) :
    (cleanupTcbReferences st tid).scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
  rw [cleanupTcbReferences_scheduler_eq_removeRunnableFromAllCores]
  exact removeRunnableFromAllCores_replenishQueueOnCore st tid c

/-- `v0.35.166`: the reference sweep moves no scheduling context's bound thread.

The run-queue removal writes no object; the endpoint sweep writes endpoints and
queue links; the notification purge writes notifications; and the origin scrub
writes `SchedContext.donationOrigin` and nothing else — which is why this is the
`boundThread` *projection* rather than a `getSchedContext?` equality: the scrub
genuinely rewrites scheduling contexts, and the invariant reads only the field it
leaves alone. -/
theorem cleanupTcbReferences_boundThread_frame (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (scId : SeLe4n.SchedContextId) :
    ((cleanupTcbReferences st tid).getSchedContext? scId).map (·.boundThread)
      = (st.getSchedContext? scId).map (·.boundThread) := by
  have h0 : (removeRunnableFromAllCores st tid).objects.invExt := by
    rw [removeRunnableFromAllCores_objects]; exact hInv
  have h1 : (removeFromAllEndpointQueues (removeRunnableFromAllCores st tid) tid).objects.invExt :=
    removeFromAllEndpointQueues_preserves_objects_invExt _ tid h0
  have h2 : (removeFromAllNotificationWaitLists
      (removeFromAllEndpointQueues (removeRunnableFromAllCores st tid) tid) tid).objects.invExt :=
    removeFromAllNotificationWaitLists_preserves_objects_invExt _ tid h1
  have hRun : (removeRunnableFromAllCores st tid).getSchedContext? scId
      = st.getSchedContext? scId := by
    unfold SystemState.getSchedContext?; rw [removeRunnableFromAllCores_objects]
  unfold cleanupTcbReferences
  rw [clearDonationOriginReferences_boundThread_eq _ tid h2 scId,
    removeFromAllNotificationWaitLists_getSchedContext?_eq _ tid h1 scId,
    removeFromAllEndpointQueues_getSchedContext?_eq _ tid h0 scId, hRun]

/-- `v0.35.166`: the reference sweep moves no thread's home core.

`determineTargetCore` reads `cpuAffinity` through `getTcb?`, and the sweep writes
intrusive queue links (through the splice), endpoints, notifications and
`donationOrigin` — no affinity.  Stated in the `Option.map` form
`determineTargetCore_congr` consumes. -/
theorem cleanupTcbReferences_affinity_frame (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (x : SeLe4n.ThreadId) :
    ((cleanupTcbReferences st tid).getTcb? x).map (·.cpuAffinity)
      = (st.getTcb? x).map (·.cpuAffinity) := by
  have h0 : (removeRunnableFromAllCores st tid).objects.invExt := by
    rw [removeRunnableFromAllCores_objects]; exact hInv
  have h1 : (removeFromAllEndpointQueues (removeRunnableFromAllCores st tid) tid).objects.invExt :=
    removeFromAllEndpointQueues_preserves_objects_invExt _ tid h0
  unfold cleanupTcbReferences
  rw [clearDonationOriginReferences_getTcb?_eq _ tid
      (removeFromAllNotificationWaitLists_preserves_objects_invExt _ tid h1),
    removeFromAllNotificationWaitLists_getTcb?_eq _ tid h1,
    removeFromAllEndpointQueues_affinity_frame _ tid h0,
    show (removeRunnableFromAllCores st tid).getTcb? x = st.getTcb? x from by
      unfold SystemState.getTcb?; rw [removeRunnableFromAllCores_objects]]

/-- `v0.35.166`: the reference sweep leaves every thread's home core where it
found it — the affinity frame above, read through `determineTargetCore_congr`. -/
theorem cleanupTcbReferences_determineTargetCore_eq (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (x : SeLe4n.ThreadId) :
    determineTargetCore (cleanupTcbReferences st tid) x = determineTargetCore st x :=
  determineTargetCore_congr st _ x (cleanupTcbReferences_affinity_frame st tid hInv x)

/-- **`v0.35.166`: the reference sweep preserves the SM5.H replenish-affinity
invariant.**

It moves no replenish entry, no bound thread and no home core, so the predicate's
three readings are all fixed and the congruence carries it whole. -/
theorem cleanupTcbReferences_preserves_replenishQueueAffinityConsistent_smp
    (st : SystemState) (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st) :
    replenishQueueAffinityConsistent_smp (cleanupTcbReferences st tid) := by
  intro c
  refine replenishQueueAffinityConsistentOnCore_transfer st _ c ?_ ?_ ?_ (hCons c)
  · intro e hMem
    rw [cleanupTcbReferences_replenishQueueOnCore] at hMem
    exact hMem
  · exact fun scId => cleanupTcbReferences_boundThread_frame st tid hInv scId
  · exact fun x => cleanupTcbReferences_determineTargetCore_eq st tid hInv x

/-- **`v0.35.166`: the destroy path's `.tcb` arm, both steps.**

`lifecyclePreRetypeCleanup`'s TCB arm is the donation teardown followed by the
reference sweep, and the two are what carry the reservation invariant between
them: the first is the only step of the whole cleanup that *moves* a replenish
entry (`v0.35.164`'s arm — a purge on a `.bound` target's home core, a migration
on a `.donated` holder's), and the second is the one §1 exists for.

Stated as a lemma of its own rather than inlined in the composite below, because
the composite then has six arms each of which is one `exact` — and because a
consumer that runs the same two steps (the suspend pipeline's G2/G3 pair is the
same shape) has something to cite. -/
theorem cleanupTcbReferences_after_donationArm_preserves_replenishQueueAffinityConsistent_smp
    (st stArm : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : lookupTcb st tid = some tcb)
    (hInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st)
    (hArm : cancelDonationArmOnCore st tid tcb = .ok stArm) :
    replenishQueueAffinityConsistent_smp (cleanupTcbReferences stArm tid) :=
  cleanupTcbReferences_preserves_replenishQueueAffinityConsistent_smp stArm tid
    (cancelDonationArmOnCore_preserves_objects_invExt st stArm tid tcb hInv hArm)
    (cancelDonationArmOnCore_preserves_replenishQueueAffinityConsistent_smp
      st stArm tid tcb hTcb hInv hCons hArm)

-- ============================================================================
-- §2  The pre-retype cleanup
-- ============================================================================

/-- **`v0.35.166`: the destroy path's pre-retype cleanup preserves the SM5.H
replenish-affinity invariant.**

Register row 63's core content, and the theorem `v0.35.164` and `v0.35.165` each
left owed: both cuts gave an *arm* its reservation theorem and neither could
state one about the program that runs it.

Six object kinds, and exactly two of them move a reservation.  The `.tcb` arm's
`cancelDonationArmOnCore` unbinds a `.bound` target's context with its
replenishments purged from the thread's home core and returns a `.donated`
holder's **with** its replenishments migrated to the owner's home
(`v0.35.164`); the `.schedContext` arm's `releaseSchedContextBinding` unbinds a
destroyed context's thread with the same purge (`v0.35.165`).  Both cite their
own theorems.  What the other four arms — and the reference sweep every `.tcb`
retype runs after its donation arm — needed is §1: they move no replenish entry,
no bound thread and no home core, but *proving* that needed two whole-store folds'
frames this module's header explains were out of reach.

`hTcb` is the arm's own soundness condition, stated where it binds: the donation
arm reads the TCB it is handed out of the store, so a caller that supplies a
record the store does not hold at that thread's key is describing a different
state.  The live `.lifecycleRetype` dispatch supplies it from the `getObject?`
it resolved `currentObj` with. -/
theorem lifecyclePreRetypeCleanup_preserves_replenishQueueAffinityConsistent_smp
    (st st' : SystemState) (target : SeLe4n.ObjId) (currentObj newObj : KernelObject)
    (hInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st)
    (hTcb : ∀ tcb : TCB, currentObj = .tcb tcb → lookupTcb st tcb.tid = some tcb)
    (h : lifecyclePreRetypeCleanup st target currentObj newObj = .ok st') :
    replenishQueueAffinityConsistent_smp st' := by
  unfold lifecyclePreRetypeCleanup at h
  cases hC : currentObj with
  | tcb tcb =>
    -- The donation arm, then the reference sweep, then the reply-link guard.
    subst hC
    simp only at h
    split at h
    · exact absurd h (by simp)
    · rename_i stArm hRun
      have hArm : cancelDonationArmOnCore st tcb.tid tcb = .ok stArm := by
        split at hRun
        · exact absurd hRun (by simp)
        · exact hRun
      split at h
      · exact absurd h (by simp)
      · injection h with h
        subst h
        exact cleanupTcbReferences_after_donationArm_preserves_replenishQueueAffinityConsistent_smp
          st stArm tcb.tid tcb (hTcb tcb rfl) hInv hCons hArm
  | endpoint ep =>
    -- The service-registry revoke writes no object and no scheduler state.
    subst hC
    simp only at h
    injection h with h
    subst h
    exact (replenishQueueAffinityConsistent_smp_frame
      (st := st) (st' := cleanupEndpointServiceRegistrations st target)
      (fun c => by rw [cleanupEndpointServiceRegistrations_scheduler_eq])
      (cleanupEndpointServiceRegistrations_objects_eq st target)).mpr hCons
  | cnode cn =>
    -- The CDT detach writes no object and no scheduler state.
    subst hC
    simp only at h
    split at h
    · exact absurd h (by simp)
    · injection h with h
      subst h
      exact (replenishQueueAffinityConsistent_smp_frame
        (st := st) (st' := detachCNodeSlots st target cn)
        (fun c => by rw [detachCNodeSlots_scheduler_eq])
        (detachCNodeSlots_objects_eq st target cn)).mpr hCons
  | reply r =>
    subst hC
    simp only at h
    split at h
    · exact absurd h (by simp)
    · injection h with h; subst h; exact hCons
  | schedContext sc =>
    -- The binding release: `v0.35.165`'s theorem, at the context the retype destroys.
    subst hC
    simp only at h
    split at h
    · exact absurd h (by simp)
    · injection h with h
      subst h
      exact releaseSchedContextBinding_preserves_replenishQueueAffinityConsistent_smp
        st (SeLe4n.SchedContextId.ofObjId target) sc hInv hCons
  | _ =>
    subst hC
    simp only at h
    injection h with h; subst h; exact hCons
