-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Invariant.CancellationNotificationShape
import SeLe4n.Kernel.IPC.Invariant.DonationPreservation

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

/-- **`v0.35.183` (register row 63): the reference sweep moves no thread's
scheduling-context binding.**

The `boundThread` frame's partner, over the other projection
`schedContextBindingConsistent` reads.  The run-queue removal writes no object;
the endpoint sweep's TCB writes are the splice's, which rewrite queue links only;
the notification purge and the origin scrub frame `getTcb?` outright. -/
theorem cleanupTcbReferences_binding_frame (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (x : SeLe4n.ThreadId) :
    ((cleanupTcbReferences st tid).getTcb? x).map (·.schedContextBinding)
      = (st.getTcb? x).map (·.schedContextBinding) := by
  have h0 : (removeRunnableFromAllCores st tid).objects.invExt := by
    rw [removeRunnableFromAllCores_objects]; exact hInv
  have h1 : (removeFromAllEndpointQueues (removeRunnableFromAllCores st tid) tid).objects.invExt :=
    removeFromAllEndpointQueues_preserves_objects_invExt _ tid h0
  unfold cleanupTcbReferences
  rw [clearDonationOriginReferences_getTcb?_eq _ tid
      (removeFromAllNotificationWaitLists_preserves_objects_invExt _ tid h1),
    removeFromAllNotificationWaitLists_getTcb?_eq _ tid h1,
    removeFromAllEndpointQueues_binding_frame _ tid h0,
    show (removeRunnableFromAllCores st tid).getTcb? x = st.getTcb? x from by
      unfold SystemState.getTcb?; rw [removeRunnableFromAllCores_objects]]

/-- **`v0.35.183` (register row 63): the reference sweep preserves Z4-O.**

Its two projections are framed above, so `schedContextBindingConsistent_transfer`
carries the invariant whole.  This is the first
`preserves_schedContextBindingConsistent` theorem in the tree — register row 63
recorded that none existed, which is why every consumer of Z4-O had to take it as
a hypothesis rather than inherit it across a step. -/
theorem cleanupTcbReferences_preserves_schedContextBindingConsistent
    (st : SystemState) (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (hBind : schedContextBindingConsistent st) :
    schedContextBindingConsistent (cleanupTcbReferences st tid) :=
  schedContextBindingConsistent_transfer
    (fun x => cleanupTcbReferences_binding_frame st tid hInv x)
    (fun scId => cleanupTcbReferences_boundThread_frame st tid hInv scId) hBind

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


-- ============================================================================
-- §3  `v0.35.183` (register row 63): Z4-O across the destroy path
-- ============================================================================

/-- **`v0.35.183`: the destroy path's donated arm preserves Z4-O.**

`cleanupDonatedSchedContext` is the resolved donation pop at the thread's own
recorded `(scId, owner)`, so this is one lift of the pop's own theorem through
`returnDonatedSchedContextResolved_lift` — the resolver's answer is a parameter
the pop's preservation does not read.

The arm's two non-pop branches are the identity: a thread the store has lost, and
a thread whose binding is not `.donated`. -/
theorem cleanupDonatedSchedContext_preserves_schedContextBindingConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt)
    (hCons : schedContextBindingConsistent st)
    (h : cleanupDonatedSchedContext st tid = .ok st') :
    schedContextBindingConsistent st' := by
  unfold cleanupDonatedSchedContext at h
  cases hLk : lookupTcb st tid with
  | none => rw [hLk] at h; injection h with h; exact h ▸ hCons
  | some tcb =>
    rw [hLk] at h
    simp only [] at h
    cases hB : tcb.schedContextBinding with
    | unbound => rw [hB] at h; injection h with h; exact h ▸ hCons
    | bound _ => rw [hB] at h; injection h with h; exact h ▸ hCons
    | donated scId owner =>
      rw [hB] at h
      exact returnDonatedSchedContextResolved_lift h (fun newOwner? s hPop =>
        returnDonatedSchedContext_preserves_schedContextBindingConsistent st s tid scId
          owner newOwner? tcb hInv (getTcb?_of_lookupTcb st tid tcb hLk) hB hCons hPop)

/-- **`v0.35.183`: and so does the arm that migrates its replenishments.**

The migration writes replenish queues and nothing else
(`migrateSchedContextReplenishment_objects`), so Z4-O crosses it by the
objects-frame form. -/
theorem cancelDonatedDonationOnCore_preserves_schedContextBindingConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : st.objects.invExt)
    (hCons : schedContextBindingConsistent st)
    (h : cancelDonatedDonationOnCore st tid tcb = .ok st') :
    schedContextBindingConsistent st' := by
  unfold cancelDonatedDonationOnCore at h
  cases hB : tcb.schedContextBinding with
  | unbound => rw [hB] at h; exact absurd h (by simp)
  | bound _ => rw [hB] at h; exact absurd h (by simp)
  | donated scId owner =>
    rw [hB] at h
    cases hRet : cleanupDonatedSchedContext st tid with
    | error e => rw [hRet] at h; exact absurd h (by simp)
    | ok stRet =>
      rw [hRet] at h
      injection h with h
      subst h
      exact schedContextBindingConsistent_of_objects_eq
        (migrateSchedContextReplenishment_objects _ _ _ _)
        (cleanupDonatedSchedContext_preserves_schedContextBindingConsistent st stRet tid
          hInv hCons hRet)

/-- **`v0.35.183`: the destroy path's reservation arm preserves Z4-O, on every
binding.**

`.unbound` is the identity, `.bound` is the unbind that clears a whole reciprocal
pair, and `.donated` is the pop that moves one.  The suspend pipeline's G3 runs
the same three (`suspendDonationArm_eq_cancelDonationArmOnCore`), so this is a
theorem about both programs.

`hTcb` is the arm's standing soundness condition: it is handed a record and
resolves the rest of the state around it, so a caller supplying one the store
does not hold at that key is describing a different state.  Both callers have
it — the destroy path from the `getObject?` it resolved `currentObj` with, the
suspend pipeline from its own G1 lookup. -/
theorem cancelDonationArmOnCore_preserves_schedContextBindingConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb)
    (hInv : st.objects.invExt)
    (hCons : schedContextBindingConsistent st)
    (h : cancelDonationArmOnCore st tid tcb = .ok st') :
    schedContextBindingConsistent st' := by
  unfold cancelDonationArmOnCore at h
  cases hB : tcb.schedContextBinding with
  | unbound => rw [hB] at h; injection h with h; exact h ▸ hCons
  | bound scId =>
    rw [hB] at h
    exact cancelBoundDonationOnCore_preserves_schedContextBindingConsistent st st' tid tcb
      (determineTargetCore st tid) scId hB hTcb hInv hCons h
  | donated scId owner =>
    rw [hB] at h
    exact cancelDonatedDonationOnCore_preserves_schedContextBindingConsistent st st' tid tcb
      hInv hCons h

/-- **`v0.35.183` (register row 63): the SchedContext arm does NOT preserve Z4-O,
and that is deliberate.**

`releaseSchedContextBinding` clears the bound thread's binding and leaves the
scheduling context's `boundThread` naming it — `v0.35.165` says so in terms:
*"what it does **not** do is rewrite the SchedContext record — the retype replaces
the object outright"*.  So Z4-O's **backward** clause is false at `scId` on the
arm's own post-state, and it is repaired one step later, by the `storeObject` the
retype performs at that very key.

Stated as a refutation rather than left implicit, because the alternative
readings are both wrong and both plausible.  A reader who assumed the arm
preserves the invariant would look for a proof that cannot exist; a cut that
"fixed" it by writing `boundThread := none` here would add a store to an object
the very next step replaces, for no property that is not already had.  This is
the tree's own standard for a hypothesis that has to be taken (WS-RR RR8.7's
`replyCallerLinkage_refutes_woken_linked_caller`): the premise is *shown*
necessary, not asserted to be.

The retype's own detachment pack excludes the arm outright (`retypeTargetDetached`'s
`notSc`), so the composite below takes the same condition rather than a relaxed
view of the invariant. -/
theorem releaseSchedContextBinding_refutes_schedContextBindingConsistent
    (st : SystemState) (scId : SeLe4n.SchedContextId) (sc : SeLe4n.Kernel.SchedContext)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : st.objects.invExt)
    (hSc : st.getSchedContext? scId = some sc)
    (hBound : sc.boundThread = some tid)
    (hTcb : st.getTcb? tid = some tcb) :
    ¬ schedContextBindingConsistent (releaseSchedContextBinding st scId sc) := by
  intro hCons
  rw [releaseSchedContextBinding_of_bound st scId sc tid tcb hBound hTcb] at hCons
  -- The released state still holds `sc` at `scId`: the arm writes a TCB, a
  -- replenish queue and an index entry, none of which is a scheduling context,
  -- and the last two are record updates of fields `getSchedContext?` never reads
  -- — so the released state's object table *is* the `updateTcb`'s.
  have hScPost : (st.updateTcb tid
      (fun t => { t with schedContextBinding := SchedContextBinding.unbound
        })).getSchedContext? scId = some sc := by
    rw [SystemState.updateTcb_getSchedContext? _ _ _ hInv]; exact hSc
  obtain ⟨tcbPost, hTcbPost, hBindPost⟩ := hCons.2 scId sc
    ((SystemState.getSchedContext?_eq_some_iff _ scId sc).mp hScPost) tid hBound
  -- ...but the thread it names is now unbound, which is what the release wrote.
  have hTcbRead : (st.updateTcb tid
      (fun t => { t with schedContextBinding := SchedContextBinding.unbound })).getTcb? tid
      = some { tcb with schedContextBinding := SchedContextBinding.unbound } := by
    rw [SystemState.updateTcb_getTcb?_self _ _ _ hInv, hTcb]; rfl
  have hPostRead : (st.updateTcb tid
      (fun t => { t with schedContextBinding := SchedContextBinding.unbound })).getTcb? tid
      = some tcbPost :=
    (SystemState.getTcb?_eq_some_iff _ tid tcbPost).mpr hTcbPost
  have hSame : tcbPost = { tcb with schedContextBinding := SchedContextBinding.unbound } :=
    Option.some.inj (hPostRead.symm.trans hTcbRead)
  rw [hSame] at hBindPost
  rcases hBindPost with hc | ⟨_, hc⟩ <;> exact absurd hc (by simp)

/-- **`v0.35.183`: the destroy path's `.tcb` arm, both steps.**

§2's `cleanupTcbReferences_after_donationArm_preserves_replenishQueueAffinityConsistent_smp`
for the other invariant, and the same pairing for the same reason: the donation
arm is the only step of the whole cleanup that *rewrites* a scheduling-context
binding, and the reference sweep is the one §1 exists for.

Stated as a lemma of its own rather than inlined below, so the suspend
pipeline — whose G2/G3 pair runs the same two steps — has something to cite. -/
theorem cleanupTcbReferences_after_donationArm_preserves_schedContextBindingConsistent
    (st stArm : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : lookupTcb st tid = some tcb)
    (hInv : st.objects.invExt)
    (hCons : schedContextBindingConsistent st)
    (hArm : cancelDonationArmOnCore st tid tcb = .ok stArm) :
    schedContextBindingConsistent (cleanupTcbReferences stArm tid) :=
  cleanupTcbReferences_preserves_schedContextBindingConsistent stArm tid
    (cancelDonationArmOnCore_preserves_objects_invExt st stArm tid tcb hInv hArm)
    (cancelDonationArmOnCore_preserves_schedContextBindingConsistent st stArm tid tcb
      (getTcb?_of_lookupTcb st tid tcb hTcb) hInv hCons hArm)

/-- **`v0.35.183` (register row 63): the destroy path's pre-retype cleanup
preserves Z4-O, on every object kind the retype's own detachment pack admits.**

The other half of §2, and the half register row 63 carried after `v0.35.166`
closed the reservation one: the row recorded that *no*
`preserves_schedContextBindingConsistent` theorem existed anywhere in the tree,
so every consumer of Z4-O had to take it as a hypothesis rather than inherit it
across a step.

Six object kinds again, and the split is not the reservation invariant's.  The
`.tcb` arm rewrites bindings — `cancelDonationArmOnCore`'s unbind clears a whole
reciprocal pair and its pop moves one — and the lemma above carries both through
the reference sweep that follows.  The `.endpoint`, `.cnode`, `.reply` and
default arms write no object at all, so `schedContextBindingConsistent_of_objects_eq`
is the whole argument.

**`hNotSc` is not a convenience**, and the theorem immediately above it is what
says so: `releaseSchedContextBinding` genuinely refutes Z4-O on its own
post-state, because it clears the bound thread's binding and deliberately leaves
the destroyed context's `boundThread` naming it for the retype's own `storeObject`
to replace.  The hypothesis is therefore the honest scope of this theorem rather
than a gap in it — and it is free at the live call site, where
`retypeTargetDetached`'s `notSc` excludes a SchedContext target outright.

`hTcb` is the `.tcb` arm's standing soundness condition, as in §2. -/
theorem lifecyclePreRetypeCleanup_preserves_schedContextBindingConsistent
    (st st' : SystemState) (target : SeLe4n.ObjId) (currentObj newObj : KernelObject)
    (hInv : st.objects.invExt)
    (hCons : schedContextBindingConsistent st)
    (hTcb : ∀ tcb : TCB, currentObj = .tcb tcb → lookupTcb st tcb.tid = some tcb)
    (hNotSc : ∀ sc : SeLe4n.Kernel.SchedContext, currentObj ≠ .schedContext sc)
    (h : lifecyclePreRetypeCleanup st target currentObj newObj = .ok st') :
    schedContextBindingConsistent st' := by
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
        exact cleanupTcbReferences_after_donationArm_preserves_schedContextBindingConsistent
          st stArm tcb.tid tcb (hTcb tcb rfl) hInv hCons hArm
  | endpoint ep =>
    -- The service-registry revoke writes no object.
    subst hC
    simp only at h
    injection h with h
    subst h
    exact schedContextBindingConsistent_of_objects_eq
      (cleanupEndpointServiceRegistrations_objects_eq st target) hCons
  | cnode cn =>
    -- The CDT detach writes no object.
    subst hC
    simp only at h
    split at h
    · exact absurd h (by simp)
    · injection h with h
      subst h
      exact schedContextBindingConsistent_of_objects_eq
        (detachCNodeSlots_objects_eq st target cn) hCons
  | reply r =>
    subst hC
    simp only at h
    split at h
    · exact absurd h (by simp)
    · injection h with h; subst h; exact hCons
  | schedContext sc =>
    -- Excluded: the binding release refutes the invariant (above).
    exact absurd hC (hNotSc sc)
  | _ =>
    subst hC
    simp only at h
    injection h with h; subst h; exact hCons
