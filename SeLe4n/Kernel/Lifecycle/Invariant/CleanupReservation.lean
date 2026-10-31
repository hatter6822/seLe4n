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
import SeLe4n.Kernel.SchedContext.YieldLinkFrame

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

`lifecyclePreRetypeCleanup` lives in `Lifecycle/Operations/CleanupPreservation.lean`.
Its `.tcb` arm's reference sweep (`cleanupTcbReferences`) runs two
whole-store folds — `removeFromAllEndpointQueues` and
`removeFromNotificationWaitQueue` — whose `getSchedContext?` and `cpuAffinity`
frames WS-RR RR8.11 wrote `private` in `IPC/Invariant/CancellationBundle.lean`,
which is **downstream of both**.  So the cleanup's own module could not state a
reservation theorem over its own sweep, and register row 63 recorded the blocker
as a layering fact rather than an effort estimate.

`v0.35.166` moved each frame to the module holding the fact its proof rests on
(see that bundle's §4 tombstone for where each went), which puts all of
them in `CancellationNotificationShape`'s import closure — and that module is
downstream of the cleanup and of `ReplenishAffinity`,
while nothing in the other direction imports it.  So this is where the
composite can be stated, and it is the *only* place it can be.

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

## Where the cleanup runs

The in-place retype that ran this cleanup (`lifecycleRetypeDirectWithCleanup` and
its wrappers) was retired at WS-ZA ZA5.4 part 14, and its composite theorems with
it; every object is now carved from an untyped.  The cleanup and these theorems
are kept for the finalisation a kernel object's final delete runs, seL4's
`finaliseCap` (`docs/planning/UNTYPED_RESET_PLAN.md`, part 24).-/

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
  refine removeFromNotificationWaitQueue_preserves_objects_invExt _ tid ?_
  refine removeFromAllEndpointQueues_preserves_objects_invExt _ tid ?_
  exact removeRunnableFromAllCores_objects_invExt st tid hInv

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
queue links; and the notification purge writes notifications, so no scheduling
context moves at all.  It is stated as the `boundThread` projection the
replenish-affinity invariant reads. -/
theorem cleanupTcbReferences_boundThread_frame (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (scId : SeLe4n.SchedContextId) :
    ((cleanupTcbReferences st tid).getSchedContext? scId).map (·.boundThread)
      = (st.getSchedContext? scId).map (·.boundThread) := by
  have h0 : (removeRunnableFromAllCores st tid).objects.invExt := by
    exact removeRunnableFromAllCores_objects_invExt st tid hInv
  have h1 : (removeFromAllEndpointQueues (removeRunnableFromAllCores st tid) tid).objects.invExt :=
    removeFromAllEndpointQueues_preserves_objects_invExt _ tid h0
  have hRun : (removeRunnableFromAllCores st tid).getSchedContext? scId
      = st.getSchedContext? scId :=
    (removeRunnableFromAllCores_objectsAgreeOffRunLinks st tid).getSchedContext? scId
  unfold cleanupTcbReferences
  rw [removeFromNotificationWaitQueue_getSchedContext?_eq _ tid h1 scId,
    removeFromAllEndpointQueues_getSchedContext?_eq _ tid h0 scId, hRun]

/-- **`v0.35.183` (register row 63): the reference sweep moves no thread's
scheduling-context binding.**

The `boundThread` frame's partner, over the other projection
`schedContextBindingConsistent` reads.  The run-queue removal writes no object;
the endpoint sweep's TCB writes are the splice's, which rewrite queue links only;
the notification purge frames `getTcb?` outright. -/
theorem cleanupTcbReferences_binding_frame (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (x : SeLe4n.ThreadId) :
    ((cleanupTcbReferences st tid).getTcb? x).map (·.schedContextBinding)
      = (st.getTcb? x).map (·.schedContextBinding) := by
  have h0 : (removeRunnableFromAllCores st tid).objects.invExt := by
    exact removeRunnableFromAllCores_objects_invExt st tid hInv
  have h1 : (removeFromAllEndpointQueues (removeRunnableFromAllCores st tid) tid).objects.invExt :=
    removeFromAllEndpointQueues_preserves_objects_invExt _ tid h0
  unfold cleanupTcbReferences
  rw [removeFromNotificationWaitQueue_tcbField_frame (·.schedContextBinding)
      (fun _ _ _ _ _ _ => rfl) _ tid h1 x,
    removeFromAllEndpointQueues_binding_frame _ tid h0,
    TCB.map_proj_eq_of_map_withoutRunLinks_eq (·.schedContextBinding)
      ((removeRunnableFromAllCores_objectsAgreeOffRunLinks st tid).getTcb? x)]

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
    exact removeRunnableFromAllCores_objects_invExt st tid hInv
  have h1 : (removeFromAllEndpointQueues (removeRunnableFromAllCores st tid) tid).objects.invExt :=
    removeFromAllEndpointQueues_preserves_objects_invExt _ tid h0
  unfold cleanupTcbReferences
  rw [removeFromNotificationWaitQueue_tcbField_frame (·.cpuAffinity)
      (fun _ _ _ _ _ _ => rfl) _ tid h1 x,
    TCB.map_cpuAffinity_of_placement (removeFromAllEndpointQueues_placement_frame _ tid h0 x),
    TCB.map_proj_eq_of_map_withoutRunLinks_eq (·.cpuAffinity)
      ((removeRunnableFromAllCores_objectsAgreeOffRunLinks st tid).getTcb? x)]

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

/-- **WS-ZA ZA6.6: a step that writes the yield writes alone keeps the
replenish-affinity invariant** — it moves no replenish entry (`hS`), no
context's bound thread and no thread's home core. -/
theorem replenishQueueAffinityConsistent_smp_of_objectsAgreeOffYield {st st' : SystemState}
    (hA : st'.objectsAgreeOffYield st) (hS : st'.scheduler = st.scheduler)
    (h : replenishQueueAffinityConsistent_smp st) : replenishQueueAffinityConsistent_smp st' :=
  fun c => replenishQueueAffinityConsistentOnCore_transfer st st' c
    (fun _ hm => by rw [hS] at hm; exact hm)
    (fun scId => hA.getSchedContext?_map _ (fun _ => rfl) scId)
    (fun tid => determineTargetCore_congr st st' tid (hA.getTcb?_map _ (fun _ => rfl) tid)) (h c)

/-- ...and every binding (Z4-O reads two projections the yield writes leave). -/
theorem schedContextBindingConsistent_of_objectsAgreeOffYield {st st' : SystemState}
    (hA : st'.objectsAgreeOffYield st) (h : schedContextBindingConsistent st) :
    schedContextBindingConsistent st' :=
  schedContextBindingConsistent_transfer (fun tid => hA.getTcb?_map _ (fun _ => rfl) tid)
    (fun scId => hA.getSchedContext?_map _ (fun _ => rfl) scId) h

/-- ...and an unpaired retype target. -/
theorem retypeTargetUnpaired_of_objectsAgreeOffYield {st st' : SystemState}
    {target : SeLe4n.ObjId} (hA : st'.objectsAgreeOffYield st)
    (h : retypeTargetUnpaired st target) : retypeTargetUnpaired st' target := by
  have e := hA target
  refine ⟨fun t hT => ?_, fun sc hS => ?_⟩
  · rw [hT] at e
    cases h0 : st.objects[target]? with
    | none => rw [h0] at e; cases e
    | some o =>
      rw [h0] at e
      cases o with
      | tcb t0 =>
        have hB : t.schedContextBinding = t0.schedContextBinding :=
          congrArg (fun x => match x with
            | some (.tcb u) => u.schedContextBinding | _ => .unbound) e
        rw [hB]; exact h.1 t0 h0
      | _ => simp [KernelObject.withoutYield] at e
  · rw [hS] at e
    cases h0 : st.objects[target]? with
    | none => rw [h0] at e; cases e
    | some o =>
      rw [h0] at e
      cases o with
      | schedContext s0 =>
        have hB : sc.boundThread = s0.boundThread :=
          congrArg (fun x => match x with
            | some (.schedContext u) => u.boundThread | _ => none) e
        rw [hB]; exact h.2 s0 h0
      | _ => simp [KernelObject.withoutYield] at e

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
state. -/
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
      · obtain rfl := Except.ok.inj h
        -- The held context's completion and the thread's cancel write the yield
        -- writes alone (`objectsAgreeOffYield`); the sweep between them keeps the
        -- invariant on any state (§1), and the slot detach writes link words alone.
        have hInvA := cancelDonationArmOnCore_preserves_objects_invExt st stArm tcb.tid tcb hInv hArm
        have hInvH := SystemState.completeHeldYield_preserves_objects_invExt stArm
          tcb.scBindingScCode hInvA
        have hInvC := cleanupTcbReferences_preserves_objects_invExt _ tcb.tid hInvH
        have hS := replenishQueueAffinityConsistent_smp_of_objectsAgreeOffYield
          (SystemState.cancelYieldTo_objectsAgreeOffYield _ tcb.tid hInvC)
          (SystemState.cancelYieldTo_scheduler _ _)
          (cleanupTcbReferences_preserves_replenishQueueAffinityConsistent_smp _ tcb.tid hInvH
            (replenishQueueAffinityConsistent_smp_of_objectsAgreeOffYield
              (SystemState.completeHeldYield_objectsAgreeOffYield _ _ hInvA)
              (SystemState.completeHeldYield_scheduler _ _)
              (cancelDonationArmOnCore_preserves_replenishQueueAffinityConsistent_smp
                st stArm tcb.tid tcb (hTcb tcb rfl) hInv hCons hArm)))
        have hA := (detachTcbSlots_agree (SystemState.cancelYieldTo_preserves_objects_invExt _
          tcb.tid hInvC) target).1
        exact fun c => (replenishQueueAffinityConsistentOnCore_congr
          (by rw [detachTcbSlots_scheduler_eq]) (fun scId => hA.getSchedContext? scId)
          (fun tid => by
            have e := TCB.map_proj_of_map_withoutLinks_eq (·.cpuAffinity) (hA.getTcb? tid)
            unfold determineTargetCore
            revert e
            cases (detachTcbSlots (cancelYieldTo (cleanupTcbReferences
                (completeHeldYield stArm tcb.scBindingScCode) tcb.tid) tcb.tid) target).getTcb? tid <;>
              cases (cancelYieldTo (cleanupTcbReferences
                (completeHeldYield stArm tcb.scBindingScCode) tcb.tid) tcb.tid).getTcb? tid <;>
              simp_all)).mpr (hS c)
  | endpoint ep =>
    -- An endpoint is not swept: the state is the one the arm found.
    subst hC
    simp only at h
    injection h with h
    subst h
    exact hCons
  | cnode cn =>
    -- The CDT detach writes no object and no scheduler state.
    subst hC
    simp only at h
    split at h
    · exact absurd h (by simp)
    · injection h with h
      subst h
      have hA := (detachCNodeSlots_agree hInv target cn).1
      exact fun c => (replenishQueueAffinityConsistentOnCore_congr
        (by rw [detachCNodeSlots_scheduler_eq]) (fun scId => hA.getSchedContext? scId)
        (fun tid => by
          have e := TCB.map_proj_of_map_withoutLinks_eq (·.cpuAffinity) (hA.getTcb? tid)
          unfold determineTargetCore
          revert e
          cases (detachCNodeSlots st target cn).getTcb? tid <;> cases st.getTcb? tid <;>
            simp_all)).mpr (hCons c)
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
      exact replenishQueueAffinityConsistent_smp_of_objectsAgreeOffYield
        (SystemState.completeYieldFrom_objectsAgreeOffYield _ _
          (releaseSchedContextBinding_preserves_objects_invExt _ _ sc hInv))
        (SystemState.completeYieldFrom_scheduler _ _)
        (releaseSchedContextBinding_preserves_replenishQueueAffinityConsistent_smp
          st (SeLe4n.SchedContextId.ofObjId target) sc hInv hCons)
  | frame _ | pageTable _ | untyped _ | vspaceRoot _ =>
    -- WS-BP BP7.1: a frame target is refused — and since slice 4a (`v0.36.8`)
    -- an untyped one — so there is no `.ok` post-state.
    subst hC; simp at h
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
          owner newOwner? hInv hCons hPop)

/-- **`v0.35.183`: and so does the arm that migrates its replenishments.**

The migration writes the release-queue links and nothing else
(`migrateSchedContextReplenishment_agree`), so Z4-O crosses it by the
release-links frame form. -/
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
      exact schedContextBindingConsistent_of_objectsAgreeOffReleaseLinks
        (migrateSchedContextReplenishment_agree _ _ _ _)
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
      scId hB hTcb hInv hCons h
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
  -- The release's one object write off the release links is the TCB rewrite
  -- (the replenish purge writes release links alone, the index removal and the
  -- reschedule-pending mark no object), and the invariant reads no release
  -- link, so it transfers to the rewrite's state.
  have hObjEq := releaseSchedContextBinding_objects_of_bound st scId sc tid tcb hBound hTcb
  replace hCons := schedContextBindingConsistent_of_objectsAgreeOffReleaseLinks hObjEq.symm hCons
  -- The released state still holds `sc` at `scId`: the arm writes a TCB, a
  -- replenish queue and an index entry, none of which is a scheduling context,
  -- and the last two are record updates of fields `getSchedContext?` never reads
  -- — so the released state's object table *is* the `updateTcb`'s.
  have hScPost : (st.updateTcb tid
      (fun t => { t with scBindingScCode := 0, scBindingOwnerCode := 0
        })).getSchedContext? scId = some sc := by
    rw [SystemState.updateTcb_getSchedContext? _ _ _ hInv]; exact hSc
  obtain ⟨tcbPost, hTcbPost, hBindPost⟩ := hCons.2 scId sc
    ((SystemState.getSchedContext?_eq_some_iff _ scId sc).mp hScPost) tid hBound
  -- ...but the thread it names is now unbound, which is what the release wrote.
  have hTcbRead : (st.updateTcb tid
      (fun t => { t with scBindingScCode := 0, scBindingOwnerCode := 0 })).getTcb? tid
      = some { tcb with scBindingScCode := 0, scBindingOwnerCode := 0 } := by
    rw [SystemState.updateTcb_getTcb?_self _ _ _ hInv, hTcb]; rfl
  have hPostRead : (st.updateTcb tid
      (fun t => { t with scBindingScCode := 0, scBindingOwnerCode := 0 })).getTcb? tid
      = some tcbPost :=
    (SystemState.getTcb?_eq_some_iff _ tid tcbPost).mpr hTcbPost
  have hSame : tcbPost = { tcb with scBindingScCode := 0, scBindingOwnerCode := 0 } :=
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
      · obtain rfl := Except.ok.inj h
        have hInvA := cancelDonationArmOnCore_preserves_objects_invExt st stArm tcb.tid tcb hInv hArm
        have hInvH := SystemState.completeHeldYield_preserves_objects_invExt stArm
          tcb.scBindingScCode hInvA
        have hInvC := cleanupTcbReferences_preserves_objects_invExt _ tcb.tid hInvH
        have hS := schedContextBindingConsistent_of_objectsAgreeOffYield
          (SystemState.cancelYieldTo_objectsAgreeOffYield _ tcb.tid hInvC)
          (cleanupTcbReferences_preserves_schedContextBindingConsistent _ tcb.tid hInvH
            (schedContextBindingConsistent_of_objectsAgreeOffYield
              (SystemState.completeHeldYield_objectsAgreeOffYield _ _ hInvA)
              (cancelDonationArmOnCore_preserves_schedContextBindingConsistent st stArm tcb.tid tcb
                (getTcb?_of_lookupTcb st tcb.tid tcb (hTcb tcb rfl)) hInv hCons hArm)))
        -- The slot detach then writes link words alone (`detachTcbSlots_agree`).
        have hA := (detachTcbSlots_agree (SystemState.cancelYieldTo_preserves_objects_invExt _
          tcb.tid hInvC) target).1
        exact schedContextBindingConsistent_transfer
          (fun tid => TCB.map_proj_of_map_withoutLinks_eq _ (hA.getTcb? tid))
          (fun scId => by rw [hA.getSchedContext? scId]) hS
  | endpoint ep =>
    -- An endpoint is not swept: the state is the one the arm found.
    subst hC
    simp only at h
    injection h with h
    subst h
    exact hCons
  | cnode cn =>
    -- The CDT detach writes no object.
    subst hC
    simp only at h
    split at h
    · exact absurd h (by simp)
    · injection h with h
      subst h
      have hA := (detachCNodeSlots_agree hInv target cn).1
      exact schedContextBindingConsistent_transfer
        (fun tid => TCB.map_proj_of_map_withoutLinks_eq _ (hA.getTcb? tid))
        (fun scId => by rw [hA.getSchedContext? scId]) hCons
  | reply r =>
    subst hC
    simp only at h
    split at h
    · exact absurd h (by simp)
    · injection h with h; subst h; exact hCons
  | schedContext sc =>
    -- Excluded: the binding release refutes the invariant (above).
    exact absurd hC (hNotSc sc)
  | frame _ | pageTable _ | untyped _ | vspaceRoot _ =>
    -- WS-BP BP7.1: a frame target is refused — and since slice 4a (`v0.36.8`)
    -- an untyped one — so there is no `.ok` post-state.
    subst hC; simp at h
  | _ =>
    subst hC
    simp only at h
    injection h with h; subst h; exact hCons

-- ============================================================================
-- §4  `v0.35.185` (register row 63): the destroyed key's binding
-- ============================================================================

/-! A destroy is the cleanup, then a write at `target`, and the two invariants
cross it through **one** intermediate: `schedContextBindingRetypeReady`, Z4-O with the target carved out of
both sides.

It has to be an intermediate rather than Z4-O itself, because the cleanup's
`.schedContext` arm *refutes* Z4-O on its own post-state by design (§3) — and it
is the same intermediate for both invariants, which is the measurement that it is
the destroy path's own fact rather than one proof's scaffolding: the replenish
half needs exactly the carve-out that says a surviving context names no thread at
the destroyed key. -/

/-- **`v0.35.185`: the donated arm leaves the target `.unbound`.**

The pop's own per-thread characterisation at the holder, lifted through the
resolver and framed across the replenishment migration (which writes no
object). -/
theorem cancelDonatedDonationOnCore_target_unbound
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hLk : lookupTcb st tid = some tcb)
    (hInv : st.objects.invExt)
    (h : cancelDonatedDonationOnCore st tid tcb = .ok st')
    (t : TCB) (hT : st'.getTcb? tid = some t) :
    t.schedContextBinding = SchedContextBinding.unbound := by
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
      -- The migration writes replenish queues only, so the reading at `tid` is
      -- the pop's own.
      have hTRet : stRet.getTcb? tid = some t := by
        rw [← (migrateSchedContextReplenishment_agree _ _ _ _).getTcb?]; exact hT
      -- Unfold the arm down to the resolved pop and read its holder clause.
      unfold cleanupDonatedSchedContext at hRet
      rw [hLk] at hRet
      simp only [] at hRet
      rw [hB] at hRet
      refine returnDonatedSchedContextResolved_lift
        (P := fun s => ∀ tX : TCB, s.getTcb? tid = some tX →
          tX.schedContextBinding = SchedContextBinding.unbound)
        hRet (fun newOwner? s hPop => ?_) t hTRet
      have hNe : owner ≠ tid :=
        returnDonatedSchedContext_ok_recipient_ne_server st s tid scId owner newOwner? tcb
          (getTcb?_of_lookupTcb st tid tcb hLk) (by rw [hB]; simp) hPop
      obtain ⟨_, ⟨srvTcb, _, hSrvPost⟩, _⟩ :=
        returnDonatedSchedContext_getTcb?_char st s tid scId owner hInv hNe newOwner? hPop
      intro tX hRead
      rw [hRead] at hSrvPost
      have hEq : tX = { srvTcb with scBindingScCode := 0, scBindingOwnerCode := 0 } :=
        Option.some.inj hSrvPost
      rw [hEq]; rfl

/-- **`v0.35.185`: and so does the reservation arm, on every binding.**

`.unbound` is the identity, `.bound` is the unbind that clears it, `.donated` is
the pop that unbinds the holder — and the holder is the target, because the arm
is handed the target's own record. -/
theorem cancelDonationArmOnCore_target_unbound
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hLk : lookupTcb st tid = some tcb)
    (hInv : st.objects.invExt)
    (h : cancelDonationArmOnCore st tid tcb = .ok st')
    (t : TCB) (hT : st'.getTcb? tid = some t) :
    t.schedContextBinding = SchedContextBinding.unbound := by
  unfold cancelDonationArmOnCore at h
  cases hB : tcb.schedContextBinding with
  | unbound =>
    rw [hB] at h; injection h with h; subst h
    have hSame : tcb = t :=
      Option.some.inj ((getTcb?_of_lookupTcb st tid tcb hLk).symm.trans hT)
    rw [← hSame]; exact hB
  | bound scId =>
    rw [hB] at h
    exact cancelBoundDonationOnCore_target_unbound st st' tid tcb
      scId hB (getTcb?_of_lookupTcb st tid tcb hLk) hInv h t hT
  | donated scId owner =>
    rw [hB] at h
    exact cancelDonatedDonationOnCore_target_unbound st st' tid tcb hLk hInv h t hT

/-- **`v0.35.185`: and it never removes the TCB it is handed.**

The sibling of the fact above, and what rules out the *other* half of an unpaired
target: the arm writes a thread's binding, a scheduling context and scheduler
state, so the key it operates on still holds a TCB — hence no scheduling
context. -/
theorem cancelDonationArmOnCore_target_isSome
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hLk : lookupTcb st tid = some tcb)
    (hInv : st.objects.invExt)
    (h : cancelDonationArmOnCore st tid tcb = .ok st') :
    (st'.getTcb? tid).isSome := by
  unfold cancelDonationArmOnCore at h
  cases hB : tcb.schedContextBinding with
  | unbound =>
    rw [hB] at h; injection h with h; subst h
    rw [getTcb?_of_lookupTcb st tid tcb hLk]; rfl
  | bound scId =>
    rw [hB] at h
    have hSelf := (cancelBoundDonationOnCore_getTcb? st st' tid tcb
      scId hB hInv h).1
    rw [hSelf, getTcb?_of_lookupTcb st tid tcb hLk]; rfl
  | donated scId owner =>
    rw [hB] at h
    -- The pop stores the holder's record back; the migration writes no object.
    unfold cancelDonatedDonationOnCore at h
    rw [hB] at h
    cases hRet : cleanupDonatedSchedContext st tid with
    | error e => rw [hRet] at h; exact absurd h (by simp)
    | ok stRet =>
      rw [hRet] at h
      injection h with h
      subst h
      have hIs := cleanupDonatedSchedContext_getTcb?_isSome st stRet tid tid hInv hRet
        (by rw [getTcb?_of_lookupTcb st tid tcb hLk]; rfl)
      rw [(migrateSchedContextReplenishment_agree _ _ _ _).getTcb?]
      exact hIs

/-- **`v0.35.185` (register row 63): the pre-retype cleanup keeps the object
table's extension invariant.**

Six arms, and every one of them is a composition of steps whose own `invExt`
preservation the tree already has: the `.tcb` arm's reservation step and
reference sweep, the `.schedContext` arm's release, and the three arms that write
no object at all.

It lives here rather than beside the cleanup for the reason §2's header gives:
its `.tcb` arm needs `cleanupTcbReferences_preserves_objects_invExt`, which §1
could only state once the two sweeps' frames had been relocated. -/
theorem lifecyclePreRetypeCleanup_preserves_objects_invExt
    (st st' : SystemState) (target : SeLe4n.ObjId) (currentObj newObj : KernelObject)
    (hInv : st.objects.invExt)
    (h : lifecyclePreRetypeCleanup st target currentObj newObj = .ok st') :
    st'.objects.invExt := by
  unfold lifecyclePreRetypeCleanup at h
  cases hC : currentObj with
  | tcb tcb =>
    subst hC; simp only at h
    split at h
    · exact absurd h (by simp)
    · rename_i stArm hRun
      have hArm : cancelDonationArmOnCore st tcb.tid tcb = .ok stArm := by
        split at hRun
        · exact absurd hRun (by simp)
        · exact hRun
      split at h
      · exact absurd h (by simp)
      · obtain rfl := Except.ok.inj h
        exact (detachTcbSlots_agree (SystemState.cancelYieldTo_preserves_objects_invExt _ tcb.tid
          (cleanupTcbReferences_preserves_objects_invExt _ tcb.tid
            (SystemState.completeHeldYield_preserves_objects_invExt _ _
              (cancelDonationArmOnCore_preserves_objects_invExt st stArm tcb.tid tcb hInv hArm))))
          target).2
  | endpoint ep =>
    subst hC; simp only at h; injection h with h; subst h
    exact hInv
  | cnode cn =>
    subst hC; simp only at h
    split at h
    · exact absurd h (by simp)
    · injection h with h; subst h
      exact (detachCNodeSlots_agree hInv target cn).2
  | reply r =>
    subst hC; simp only at h
    split at h
    · exact absurd h (by simp)
    · injection h with h; subst h; exact hInv
  | schedContext sc =>
    subst hC; simp only at h
    split at h
    · exact absurd h (by simp)
    · injection h with h; subst h
      exact SystemState.completeYieldFrom_preserves_objects_invExt _ _
        (releaseSchedContextBinding_preserves_objects_invExt _ _ sc hInv)
  | frame _ | pageTable _ | untyped _ | vspaceRoot _ =>
    -- WS-BP BP7.1: a frame target is refused — and since slice 4a (`v0.36.8`)
    -- an untyped one — so there is no `.ok` post-state.
    subst hC; simp at h
  | _ =>
    subst hC; simp only at h; injection h with h; subst h; exact hInv

/-- An unpaired target stays unpaired across a run of derivation-link writes:
a TCB's binding and a context's bound thread are not link words. -/
private theorem retypeTargetUnpaired_of_agree {st st' : SystemState} {target : SeLe4n.ObjId}
    (hA : SystemState.objectsAgreeOffDerivationLinks st' st)
    (h : retypeTargetUnpaired st target) : retypeTargetUnpaired st' target :=
  ⟨fun t hT => by
    obtain ⟨t0, h0, e⟩ := hA.tcb_back hT
    have hB : t.schedContextBinding = t0.schedContextBinding := Option.some.inj
      (TCB.map_proj_of_map_withoutLinks_eq TCB.schedContextBinding
        (o := some t0) (o' := some t) (by simp [e]))
    rw [hB]; exact h.1 t0 h0,
   fun sc hS => h.2 sc (hA.obj_back hS (fun _ e => KernelObject.noConfusion e))⟩

/-- **`v0.35.185` (register row 63): the cleanup leaves the target unpaired.**

Five of the six arms, and `hNotSc` is the sixth — excluded for the reason §3
states and proves: `releaseSchedContextBinding` deliberately leaves the destroyed
context's `boundThread` naming the thread it has just unbound, so that arm's
post-state is not unpaired and its readiness has to be argued from the *pre*-state
invariant instead.  It is free at the live call site, where
`retypeTargetDetached`'s `notSc` excludes a SchedContext target outright.

`hIdentity` is the one hypothesis this needs beyond §2's, and it binds on the
`.tcb` arm alone (it is vacuous for every other `currentObj`).  The arm is handed
`tcb` and operates on `tcb.tid`, while the store the retype performs is at
`target`, so without it the cleanup can clear a binding at one key and leave the
retype's own key paired — a state the store does not repair.  Three measurements
place it: `PlatformConfig.wellFormed`'s `tcbIdentitiesMatchSlots` establishes it
for every boot TCB; **no transition writes `TCB.tid`**; and the one path that
installs a TCB, the carve (`carvedTcb`), sets it to the child's own id
(`untypedRetypeObject_ok_tcb`).  So it holds of every state
this kernel reaches — and is stated by no invariant, which is what keeps it a
hypothesis here and a register row rather than a `hCons`-style premise. -/
theorem lifecyclePreRetypeCleanup_targetUnpaired
    (st st' : SystemState) (target : SeLe4n.ObjId) (currentObj newObj : KernelObject)
    (hInv : st.objects.invExt)
    (hStored : st.objects[target]? = some currentObj)
    (hTcb : ∀ tcb : TCB, currentObj = .tcb tcb → lookupTcb st tcb.tid = some tcb)
    (hIdentity : ∀ tcb : TCB, currentObj = .tcb tcb → tcb.tid.toObjId = target)
    (hNotSc : ∀ sc, currentObj ≠ .schedContext sc)
    (h : lifecyclePreRetypeCleanup st target currentObj newObj = .ok st') :
    retypeTargetUnpaired st' target := by
  unfold lifecyclePreRetypeCleanup at h
  cases hC : currentObj with
  | tcb tcb =>
    -- The arm clears the target's own binding; the sweep frames it.
    have hId : tcb.tid.toObjId = target := hIdentity tcb hC
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
      · obtain rfl := Except.ok.inj h
        have hArmInv : stArm.objects.invExt :=
          cancelDonationArmOnCore_preserves_objects_invExt st stArm tcb.tid tcb hInv hArm
        -- The held context's completion writes the yield writes alone, so its
        -- state reads every binding the arm left (`objectsAgreeOffYield`).
        have hHInv := SystemState.completeHeldYield_preserves_objects_invExt stArm
          tcb.scBindingScCode hArmInv
        have hHA := SystemState.completeHeldYield_objectsAgreeOffYield stArm
          tcb.scBindingScCode hArmInv
        have hCInv := cleanupTcbReferences_preserves_objects_invExt _ tcb.tid hHInv
        -- The slot detach writes link words alone and the cancel the yield
        -- writes alone, so the sweep's reading stands.
        refine retypeTargetUnpaired_of_agree (detachTcbSlots_agree
          (SystemState.cancelYieldTo_preserves_objects_invExt _ tcb.tid hCInv) target).1 ?_
        refine retypeTargetUnpaired_of_objectsAgreeOffYield
          (SystemState.cancelYieldTo_objectsAgreeOffYield _ tcb.tid hCInv) ?_
        have hFrame := (cleanupTcbReferences_binding_frame _ tcb.tid hHInv tcb.tid).trans
          (hHA.getTcb?_map (·.schedContextBinding) (fun _ => rfl) tcb.tid)
        have hArmSome := cancelDonationArmOnCore_target_isSome st stArm tcb.tid tcb
          (hTcb tcb rfl) hInv hArm
        refine ⟨fun t hT => ?_, fun sc hS => ?_⟩
        · -- The sweep frames the binding, so the reading is the arm's.
          have hPost : (cleanupTcbReferences (completeHeldYield stArm tcb.scBindingScCode) tcb.tid).getTcb? tcb.tid = some t :=
            (SystemState.getTcb?_eq_some_iff _ tcb.tid t).mpr (by rw [hId]; exact hT)
          rw [hPost] at hFrame
          cases hArmRead : stArm.getTcb? tcb.tid with
          | none => rw [hArmRead] at hFrame; exact absurd hFrame (by simp)
          | some tArm =>
            rw [hArmRead] at hFrame
            have hSame : t.schedContextBinding = tArm.schedContextBinding := by
              simpa using hFrame
            rw [hSame]
            exact cancelDonationArmOnCore_target_unbound st stArm tcb.tid tcb
              (hTcb tcb rfl) hInv hArm tArm hArmRead
        · -- The key still holds a TCB, so it holds no scheduling context.
          exfalso
          have hNone : (cleanupTcbReferences (completeHeldYield stArm tcb.scBindingScCode) tcb.tid).getTcb? tcb.tid = none := by
            unfold SystemState.getTcb?; rw [hId, hS]
          rw [hNone] at hFrame
          cases hArmRead : stArm.getTcb? tcb.tid with
          | none => rw [hArmRead] at hArmSome; exact absurd hArmSome (by simp)
          | some tArm => rw [hArmRead] at hFrame; exact absurd hFrame (by simp)
  | schedContext sc => exact absurd hC (hNotSc sc)
  | endpoint ep =>
    subst hC; simp only at h; injection h with h; subst h
    exact retypeTargetUnpaired_of_objects_eq rfl
      ⟨fun t hT => by rw [hStored] at hT; exact absurd hT (by simp),
       fun s0 hS => by rw [hStored] at hS; exact absurd hS (by simp)⟩
  | cnode cn =>
    subst hC; simp only at h
    split at h
    · exact absurd h (by simp)
    · injection h with h; subst h
      have hA := (detachCNodeSlots_agree hInv target cn).1
      exact ⟨fun t hT => (hA.tcb_back hT).elim fun t0 h0 =>
          absurd h0.1 (by rw [hStored]; simp),
        fun s0 hS => absurd (hA.obj_back hS (fun _ h => KernelObject.noConfusion h))
          (by rw [hStored]; simp)⟩
  | reply r =>
    subst hC; simp only at h
    split at h
    · exact absurd h (by simp)
    · injection h with h; subst h
      exact ⟨fun t hT => by rw [hStored] at hT; exact absurd hT (by simp),
             fun s0 hS => by rw [hStored] at hS; exact absurd hS (by simp)⟩
  | frame _ | pageTable _ | untyped _ | vspaceRoot _ =>
    -- WS-BP BP7.1: a frame target is refused — and since slice 4a (`v0.36.8`)
    -- an untyped one — so there is no `.ok` post-state.
    subst hC; simp at h
  | _ =>
    subst hC; simp only at h; injection h with h; subst h
    exact ⟨fun t hT => by rw [hStored] at hT; exact absurd hT (by simp),
           fun s0 hS => by rw [hStored] at hS; exact absurd hS (by simp)⟩

end SeLe4n.Kernel
