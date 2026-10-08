-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Operations.RetypeWrappers
import SeLe4n.Kernel.Lifecycle.Invariant.RetypeReservation
import SeLe4n.Kernel.Architecture.PerCoreCacheModel
import SeLe4n.Kernel.SchedContext.ReplenishAffinity
import SeLe4n.Kernel.SchedContext.SchedContextFootprint

/-!
# The `.lifecycleRetype` arm's scheduler footprint

`threadOccupiedCores`, the retype write set and replenish-core resolvers, and
`schedLockSet_lifecycleRetypeOnCore`, beside the transitions they are about
(`Lifecycle/Operations/RetypeWrappers.lean`, the cleanup in
`Lifecycle/Operations/Cleanup.lean`), with the exactness halves — what the
destroy path writes, up to the live `lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache`
— and the per-member coverage theorems.  Moved here from
`SyscallSchedFootprint.lean` at WS-LS LS2.5, unchanged.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId
  LockKey LockSet)

-- ============================================================================
-- §8  The `.lifecycleRetype` arm
-- ============================================================================
--
-- The destroy path's scheduler effects are the pre-retype cleanup's, and since
-- `v0.35.164`/`v0.35.165` there are two of them: a TCB target ends its
-- reservation the way a suspended thread's is (`cancelDonationArmOnCore`), and a
-- SchedContext target releases the binding it holds (`releaseSchedContextBinding`,
-- seL4's `schedContext_unbindAllTCBs` per core).  Both read the **pre-state** --
-- for a SchedContext target every earlier step of the cleanup is the identity,
-- and for a TCB target the arm IS the first step -- so this whole footprint is
-- pre-state computable with no mid-state bridge.


/-- **The cores a destroy sweep actually touches** — those the thread occupies in
the pre-state.

`removeRunnableFromAllCores` folds over *every* core, so the naive bound is
`allCores`, which is true and useless; the step is **guarded** by
`threadOccupiesCore` precisely so a sharper bound is available, and this is that
bound.

SM8.B.2's resolver, moved here from the staged
`InformationFlow/NonInterferenceCrossCore.lean` at `v0.35.169` with the retype
write set that reads it. -/
def threadOccupiedCores (st : SystemState) (tid : SeLe4n.ThreadId) : List CoreId :=
  Concurrency.allCores.filter (threadOccupiesCore st tid)

/-- **Where a `.lifecycleRetype` writes a RUN QUEUE**, as a function of the object
being destroyed.

Only the TCB arm names any core, and it names the ones the doomed thread
occupies.  Every other kind — CNode, endpoint, notification, reply, VSpace root,
untyped, scheduling context — writes no run queue and no current slot, so its set
is empty.  **A SchedContext target is not an exception**: its release writes a
replenish queue, which is not one of the six slots
`observableSlotsConfinedToCores` covers, and which the replenish segment below
declares instead.

SM8.B.2's write set, moved here from the staged non-interference module at
`v0.35.169`. -/
def lifecycleRetypeWriteSetOf (st : SystemState) (currentObj : KernelObject) :
    List CoreId :=
  match currentObj with
  | .tcb tcb => threadOccupiedCores st tcb.tid
  | _ => []

/-- The same set, resolved from the target's id through the pre-state store.
Retyping an absent object writes nothing (the pipeline errors out).

SM8.B.2's write set, moved here from the staged non-interference module at
`v0.35.169`. -/
def lifecycleRetypeWriteSet (st : SystemState) (target : SeLe4n.ObjId) : List CoreId :=
  match st.getObject? target with
  | some obj => lifecycleRetypeWriteSetOf st obj
  | none => []

/-- **`v0.35.169`: the cores the destroy path's donation arm moves a RESERVATION
on**, keyed on the doomed thread's own binding — `cancelDonationArmOnCore`'s
three arms, read as cores.

`.unbound` moves nothing; `.bound` purges on the thread's home core; `.donated`
returns the context and migrates its replenishments from the holder's home to the
recorded owner's, the destination read at the **post-return** state exactly as
`cancelDonatedDonationOnCore` reads it.  A refused return migrates nothing, and
the empty list there is the transition's own behaviour rather than a narrowing. -/
def cancelDonationArmReplenishCoresAt (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (home : CoreId) : List CoreId :=
  match tcb.schedContextBinding with
  | .unbound => []
  | .bound _ => [home]
  | .donated _ owner =>
      match cleanupDonatedSchedContext st tid with
      | .error _ => []
      | .ok st' => [determineTargetCore st tid, determineTargetCore st' owner]

/-- The same, at the purge core `cancelDonationArmOnCore` itself computes — the
destroy path's instance.  The suspend pipeline's G3 passes the home it captured
**before** the teardown, which is why the general form exists at all. -/
def cancelDonationArmReplenishCores (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) : List CoreId :=
  cancelDonationArmReplenishCoresAt st tid tcb (determineTargetCore st tid)

/-- **`v0.35.169`: the cores a binding release moves a RESERVATION on**, and the
second place in this module where a segment is EVERY core.

`releaseSchedContextBinding` purges on the bound thread's home core when that
thread resolves, and sweeps every core when it does not — with the TCB gone from
the store there is no `cpuAffinity` left to read and no home to name, which is
`schedContextUnbindReplenishCores`' reasoning on the same shape one operation
over.  A context bound to nothing has no binding to release, hence the empty
list. -/
def releaseSchedContextBindingReplenishCores (st : SystemState)
    (sc : SchedContext) : List CoreId :=
  match sc.boundThread with
  | none => []
  | some tid =>
      match st.getTcb? tid with
      | some _ => [determineTargetCore st tid]
      | none => Concurrency.allCores

/-- **`v0.35.169`: the cores a `.lifecycleRetype` moves a RESERVATION on**, as a
function of the object being destroyed — the TCB arm's donation cores, the
SchedContext arm's release cores, and nothing for any other kind. -/
def lifecycleRetypeReplenishCoresOf (st : SystemState) (target : SeLe4n.ObjId)
    (currentObj : KernelObject) : List CoreId :=
  match currentObj with
  | .tcb tcb => cancelDonationArmReplenishCores st tcb.tid tcb
  | .schedContext sc => releaseSchedContextBindingReplenishCores st sc
  | _ => (fun _ => []) target

/-- The same set, resolved from the target's id through the pre-state store. -/
def lifecycleRetypeReplenishCores (st : SystemState) (target : SeLe4n.ObjId) :
    List CoreId :=
  match st.getObject? target with
  | some obj => lifecycleRetypeReplenishCoresOf st target obj
  | none => []

/-- **`v0.35.169`: the live `.lifecycleRetype` arm's scheduler-domain
footprint.** -/
def schedLockSet_lifecycleRetypeOnCore (st : SystemState) (target : SeLe4n.ObjId) :
    List (LockKey × Concurrency.AccessMode) :=
  schedFootprintOfCores (lifecycleRetypeWriteSet st target)
    (lifecycleRetypeReplenishCores st target)

/-- `v0.35.169`: the footprint holds the run-queue write lock of every core the
doomed thread occupies — the destroy sweep's own. -/
theorem schedLockSet_lifecycleRetypeOnCore_contains_occupied_runQueue_write
    (st : SystemState) (target : SeLe4n.ObjId) (tcb : TCB) (c : CoreId)
    (h : st.getObject? target = some (.tcb tcb))
    (hOcc : threadOccupiesCore st tcb.tid c = true) :
    (LockKey.runQueue c, Concurrency.AccessMode.write)
      ∈ schedLockSet_lifecycleRetypeOnCore st target :=
  (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr
    (by simp only [lifecycleRetypeWriteSet, lifecycleRetypeWriteSetOf, h,
          threadOccupiedCores, List.mem_filter]
        exact ⟨Concurrency.mem_allCores c, hOcc⟩)

/-- `v0.35.169`: ...and the replenish-queue write lock of a `.bound` doomed
thread's home core, which is the unbind's purge core. -/
theorem schedLockSet_lifecycleRetypeOnCore_contains_bound_replenishQueue_write
    (st : SystemState) (target : SeLe4n.ObjId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (h : st.getObject? target = some (.tcb tcb))
    (hBind : tcb.schedContextBinding = .bound scId) :
    (LockKey.replenishQueue (determineTargetCore st tcb.tid), Concurrency.AccessMode.write)
      ∈ schedLockSet_lifecycleRetypeOnCore st target :=
  (mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mpr
    (by unfold lifecycleRetypeReplenishCores
        rw [h]
        simp [lifecycleRetypeReplenishCoresOf, cancelDonationArmReplenishCores,
          cancelDonationArmReplenishCoresAt, hBind])

/-- `v0.35.169`: ...and both of a `.donated` holder's, which are the return's
migration endpoints. -/
theorem schedLockSet_lifecycleRetypeOnCore_contains_donated_replenishQueue_writes
    (st st' : SystemState) (target : SeLe4n.ObjId) (tcb : TCB)
    (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId)
    (h : st.getObject? target = some (.tcb tcb))
    (hBind : tcb.schedContextBinding = .donated scId owner)
    (hRet : cleanupDonatedSchedContext st tcb.tid = .ok st') :
    (LockKey.replenishQueue (determineTargetCore st tcb.tid),
      Concurrency.AccessMode.write) ∈ schedLockSet_lifecycleRetypeOnCore st target ∧
    (LockKey.replenishQueue (determineTargetCore st' owner),
      Concurrency.AccessMode.write) ∈ schedLockSet_lifecycleRetypeOnCore st target := by
  constructor <;>
    exact (mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mpr
      (by unfold lifecycleRetypeReplenishCores
          rw [h]
          simp [lifecycleRetypeReplenishCoresOf, cancelDonationArmReplenishCores,
            cancelDonationArmReplenishCoresAt, hBind, hRet])

/-- `v0.35.169`: ...and the bound thread's home core's, on a SchedContext
target whose bound TCB resolves. -/
theorem schedLockSet_lifecycleRetypeOnCore_contains_release_replenishQueue_write
    (st : SystemState) (target : SeLe4n.ObjId) (sc : SchedContext)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (h : st.getObject? target = some (.schedContext sc))
    (hBound : sc.boundThread = some tid)
    (hTcb : st.getTcb? tid = some tcb) :
    (LockKey.replenishQueue (determineTargetCore st tid), Concurrency.AccessMode.write)
      ∈ schedLockSet_lifecycleRetypeOnCore st target :=
  (mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mpr
    (by unfold lifecycleRetypeReplenishCores
        rw [h]
        simp [lifecycleRetypeReplenishCoresOf, releaseSchedContextBindingReplenishCores,
          hBound, hTcb])

/-- **`v0.35.169`: and EVERY core's, where that TCB is already gone** — the
honest declaration of `purgeReplenishmentFromAllCores`, which the release runs
when there is no `cpuAffinity` left to read. -/
theorem schedLockSet_lifecycleRetypeOnCore_contains_every_replenishQueue_write_of_sweep
    (st : SystemState) (target : SeLe4n.ObjId) (sc : SchedContext)
    (tid : SeLe4n.ThreadId) (c : CoreId)
    (h : st.getObject? target = some (.schedContext sc))
    (hBound : sc.boundThread = some tid)
    (hTcb : st.getTcb? tid = none) :
    (LockKey.replenishQueue c, Concurrency.AccessMode.write)
      ∈ schedLockSet_lifecycleRetypeOnCore st target :=
  (mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mpr
    (by unfold lifecycleRetypeReplenishCores
        rw [h]
        simp only [lifecycleRetypeReplenishCoresOf, releaseSchedContextBindingReplenishCores,
          hBound, hTcb]
        exact Concurrency.mem_allCores c)

/-- **`v0.35.169`: and NO scheduler lock at all for every other kind of target.**

A CNode, endpoint, notification, reply, VSpace root or untyped target has no
scheduling effect: the cleanup's arms for them write the object store, the CDT
and the service registry, and nothing per-core.  Stated over both segments, so a
kind that acquires one has to move a definition rather than a proof. -/
theorem schedLockSet_lifecycleRetypeOnCore_empty_of_other (st : SystemState)
    (target : SeLe4n.ObjId) (obj : KernelObject)
    (h : st.getObject? target = some obj)
    (hTcb : ∀ tcb, obj ≠ .tcb tcb)
    (hSc : ∀ sc, obj ≠ .schedContext sc) :
    schedLockSet_lifecycleRetypeOnCore st target
      = [(LockKey.objStore, Concurrency.AccessMode.write)] := by
  unfold schedLockSet_lifecycleRetypeOnCore lifecycleRetypeWriteSet
    lifecycleRetypeReplenishCores
  rw [h]
  cases obj with
  | tcb t => exact absurd rfl (hTcb t)
  | schedContext s => exact absurd rfl (hSc s)
  | _ =>
    simp [lifecycleRetypeWriteSetOf, lifecycleRetypeReplenishCoresOf,
      schedFootprintOfCores, schedCoreSegment, Concurrency.canonicalCores]

-- ============================================================================
-- §9  The exactness halves — what the destroy path writes
-- ============================================================================

/-- **`v0.35.169`: the `.bound` unbind writes exactly the core it is handed.** -/
theorem cancelBoundDonationOnCore_replenishQueueOnCore_ne (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (rqCore c : CoreId)
    (hne : rqCore ≠ c)
    (h : cancelBoundDonationOnCore st tid tcb rqCore = .ok st') :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold cancelBoundDonationOnCore at h
  split at h
  · rw [Except.ok.injEq] at h
    rw [← h, markKeyChangeFrom_replenishQueueOnCore]
    simp only [SystemState.updateTcb_scheduler]
    rw [SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne _ _ _ _ hne,
      SystemState.updateSchedContext_scheduler]
  · exact absurd h (by simp)

/-- **`v0.35.169`: the `.donated` return writes exactly its migration's two
endpoints.** -/
theorem cancelDonatedDonationOnCore_replenishQueueOnCore_ne (st st' stRet : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (owner : SeLe4n.ThreadId) (c : CoreId)
    (hBind : tcb.schedContextBinding = .donated scId owner)
    (hRet : cleanupDonatedSchedContext st tid = .ok stRet)
    (hFrom : determineTargetCore st tid ≠ c)
    (hTo : determineTargetCore stRet owner ≠ c)
    (h : cancelDonatedDonationOnCore st tid tcb = .ok st') :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold cancelDonatedDonationOnCore at h
  rw [hBind, hRet] at h
  dsimp only at h
  rw [Except.ok.injEq] at h
  rw [← h, migrateSchedContextReplenishment_replenishQueueOnCore_other _ _ _ _ _ hFrom hTo]
  exact cleanupDonatedSchedContext_scheduler_eq st stRet tid hRet ▸ rfl

/-- **`v0.35.170`: the donation arm writes exactly the cores its own resolver
names, at whatever purge core it is handed.**

Stated over the three-way match at an **explicit** `home` because that is the
question both askers ask, and they hand it different cores:
`cancelDonationArmOnCore` — the destroy path's arm — reads it off the state it
runs on, while `suspendThreadOnCore`'s G3 was handed it from the **pre**-G2
state, captured before the teardown for the reason that transition records.  A
frame stated at `determineTargetCore st tid` covers the first and not the
second, so it is the *parameter* that is general here and both consumers below
are instances of one proof. -/
theorem donationArmAt_replenishQueueOnCore_ne (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (home c : CoreId)
    (hne : c ∉ cancelDonationArmReplenishCoresAt st tid tcb home)
    (h : (match tcb.schedContextBinding with
          | .unbound => (Except.ok st : Except KernelError SystemState)
          | .bound _ => cancelBoundDonationOnCore st tid tcb home
          | .donated _ _ => cancelDonatedDonationOnCore st tid tcb) = .ok st') :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold cancelDonationArmReplenishCoresAt at hne
  cases hBind : tcb.schedContextBinding with
  | unbound =>
      rw [hBind] at h
      rw [Except.ok.injEq] at h; rw [← h]
  | bound scId =>
      rw [hBind] at h hne
      exact cancelBoundDonationOnCore_replenishQueueOnCore_ne st st' tid tcb _ c
        (by simp only [List.mem_singleton] at hne; exact fun hc => hne hc.symm) h
  | donated scId owner =>
      rw [hBind] at h hne
      cases hRet : cleanupDonatedSchedContext st tid with
      | error e =>
          rw [hRet] at hne
          unfold cancelDonatedDonationOnCore at h
          rw [hBind, hRet] at h
          exact absurd h (by simp)
      | ok stRet =>
          rw [hRet] at hne
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hne
          exact cancelDonatedDonationOnCore_replenishQueueOnCore_ne st st' stRet tid tcb
            scId owner c hBind hRet (fun hc => hne.1 hc.symm) (fun hc => hne.2 hc.symm) h

/-- **`v0.35.169`: the destroy path's donation arm writes exactly the cores its
own resolver names** — the exactness half of the retype footprint's `.tcb`
replenish segment, and the instance of the frame above at the purge core that
arm reads for itself. -/
theorem cancelDonationArmOnCore_replenishQueueOnCore_ne (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (c : CoreId)
    (hne : c ∉ cancelDonationArmReplenishCores st tid tcb)
    (h : cancelDonationArmOnCore st tid tcb = .ok st') :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c :=
  donationArmAt_replenishQueueOnCore_ne st st' tid tcb (determineTargetCore st tid) c hne h

/-- **`v0.35.169`: the binding release writes exactly the cores its own resolver
names** — the exactness half of the retype footprint's `.schedContext` replenish
segment.  The sweep arm names every core, so the hypothesis is unsatisfiable
there and the statement is about the bound arm. -/
theorem releaseSchedContextBinding_replenishQueueOnCore_ne (st : SystemState)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (c : CoreId)
    (hne : c ∉ releaseSchedContextBindingReplenishCores st sc) :
    (releaseSchedContextBinding st scId sc).scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
  unfold releaseSchedContextBinding
  unfold releaseSchedContextBindingReplenishCores at hne
  cases hBound : sc.boundThread with
  | none => rfl
  | some tid =>
      rw [hBound] at hne
      dsimp only at hne ⊢
      cases hTcb : st.getTcb? tid with
      | none => rw [hTcb] at hne; exact absurd (Concurrency.mem_allCores c) hne
      | some tcb =>
          rw [hTcb] at hne
          dsimp only
          simp only [List.mem_singleton] at hne
          rw [markKeyChangeFor_replenishQueueOnCore]
          dsimp only
          rw [SchedContextOps.purgeReplenishmentOnCore_replenishQueueOnCore_ne _ _ _ _
            (fun hc => hne hc.symm), SystemState.updateTcb_scheduler]

/-- **`v0.35.169`: and the whole pre-retype cleanup writes exactly the cores
`lifecycleRetypeReplenishCoresOf` names.**

The exactness half of `schedLockSet_lifecycleRetypeOnCore`'s replenish segment,
over all six object kinds: the TCB arm's donation step and the SchedContext
arm's release are the only two that move a replenishment, and every other step
of the pipeline — the reference sweep, the service-registry revoke, the CDT
detach, the reply and VSpace guards — frames the scheduler outright. -/
theorem lifecyclePreRetypeCleanup_replenishQueueOnCore_ne (st st' : SystemState)
    (target : SeLe4n.ObjId) (currentObj newObj : KernelObject) (c : CoreId)
    (hne : c ∉ lifecycleRetypeReplenishCoresOf st target currentObj)
    (h : lifecyclePreRetypeCleanup st target currentObj newObj = .ok st') :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold lifecyclePreRetypeCleanup at h
  unfold lifecycleRetypeReplenishCoresOf at hne
  cases hC : currentObj with
  | tcb tcb =>
      subst hC
      simp only at h hne
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
          rw [cleanupTcbReferences_replenishQueueOnCore]
          exact cancelDonationArmOnCore_replenishQueueOnCore_ne st stArm tcb.tid tcb c hne hArm
  | schedContext sc =>
      subst hC
      simp only at h hne
      split at h
      · exact absurd h (by simp)
      · injection h with h
        subst h
        exact releaseSchedContextBinding_replenishQueueOnCore_ne st _ sc c hne
  | endpoint ep =>
      subst hC
      simp only at h
      injection h with h
      subst h
      rw [cleanupEndpointServiceRegistrations_scheduler_eq]
  | cnode cn =>
      subst hC
      simp only at h
      split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        injection h with h
        subst h
        rw [detachCNodeSlots_scheduler_eq]
  | reply r =>
      subst hC
      simp only at h
      split at h
      · exact absurd h (by simp)
      · injection h with h; subst h; rfl
  | frame _ | pageTable _ | untyped _ | vspaceRoot _ =>
      -- WS-BP BP7.1: a frame target is refused — and since slice 4a (`v0.36.8`)
      -- an untyped one — so there is no `.ok` step.
      subst hC
      simp at h
  | _ =>
      subst hC
      simp only at h
      first
        | (injection h with h; subst h; rfl)
        | (split at h
           · exact absurd h (by simp)
           · injection h with h; subst h; rfl)

/-- **WS-RR RR8.12 Cut C6g (the exactness frame)**: the base retype-with-cleanup
writes no replenish queue outside `lifecycleRetypeReplenishCores` — the
FOOTPRINT's own segment.

Mirrors `lifecycleRetypeDirectWithCleanup_confinedToCores` clause for clause: the
well-formedness reject commits nothing, the absent-target arm is
`lifecycleRetypeDirect` (a store, so scheduler-silent), and the present arm is the
cleanup — the one step that moves a replenishment — then the scrub and the store,
both scheduler-silent. -/
theorem lifecycleRetypeDirectWithCleanup_replenishQueueOnCore_ne (authCap : Capability)
    (target : SeLe4n.ObjId) (newObj : KernelObject) (st st' : SystemState) (c : CoreId)
    (hne : c ∉ lifecycleRetypeReplenishCores st target)
    (h : lifecycleRetypeDirectWithCleanup authCap target newObj st = .ok ((), st')) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold lifecycleRetypeDirectWithCleanup at h
  unfold lifecycleRetypeReplenishCores at hne
  split at h
  · exact absurd h (by simp)
  · cases hObj : SystemState.getObject? st target with
    | none =>
      rw [hObj] at h
      simp only [] at h
      rw [(lifecycleRetypeDirect_scheduler_machine_eq authCap target newObj st st' h).1]
    | some currentObj =>
      rw [hObj] at h hne
      simp only [] at h
      cases hClean : lifecyclePreRetypeCleanup st target currentObj newObj with
      | error e => rw [hClean] at h; simp only [] at h; exact absurd h (by simp)
      | ok stClean =>
        rw [hClean] at h
        simp only [] at h
        rw [(lifecycleRetypeDirect_scheduler_machine_eq authCap target newObj
          (scrubObjectMemory stClean target currentObj.objectType) st' h).1,
          scrubObjectMemory_scheduler_eq stClean target currentObj.objectType]
        exact lifecyclePreRetypeCleanup_replenishQueueOnCore_ne st stClean target currentObj
          newObj c hne hClean

/-- **Cut C6g**: the ASID shootdown rounds move no replenishment — TLB maintenance
is not scheduling. -/
theorem lifecycleRetypeDirectWithCleanupShootdown_replenishQueueOnCore_ne
    (executingCore : CoreId) (authCap : Capability) (target : SeLe4n.ObjId)
    (newObj : KernelObject) (st st' : SystemState) (c : CoreId)
    (hne : c ∉ lifecycleRetypeReplenishCores st target)
    (h : lifecycleRetypeDirectWithCleanupShootdown executingCore authCap target newObj st
      = .ok ((), st')) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold lifecycleRetypeDirectWithCleanupShootdown at h
  cases hBase : lifecycleRetypeDirectWithCleanup authCap target newObj st with
  | error e => rw [hBase] at h; simp only [] at h; exact absurd h (by simp)
  | ok pair =>
    obtain ⟨u, stBase⟩ := pair
    cases u
    rw [hBase] at h
    simp only [] at h
    rw [retypeShootdownAsids_eq] at h
    rw [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, he⟩ := h
    subst he
    rw [retypeAsidRoundFold_scheduler]
    exact lifecycleRetypeDirectWithCleanup_replenishQueueOnCore_ne authCap target newObj st
      stBase c hne hBase

/-- **Cut C6g**: nor does the initiator's own per-core TLB view drain. -/
theorem lifecycleRetypeDirectWithCleanupShootdownPerCore_replenishQueueOnCore_ne
    (executingCore : CoreId) (authCap : Capability) (target : SeLe4n.ObjId)
    (newObj : KernelObject) (st st' : SystemState) (c : CoreId)
    (hne : c ∉ lifecycleRetypeReplenishCores st target)
    (h : lifecycleRetypeDirectWithCleanupShootdownPerCore executingCore authCap target newObj st
      = .ok ((), st')) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold lifecycleRetypeDirectWithCleanupShootdownPerCore at h
  cases hRound : lifecycleRetypeDirectWithCleanupShootdown executingCore authCap target newObj st
    with
  | error e => rw [hRound] at h; simp only [] at h; exact absurd h (by simp)
  | ok pair =>
    obtain ⟨u, stRound⟩ := pair
    cases u
    rw [hRound] at h
    simp only [] at h
    rw [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, he⟩ := h
    subst he
    rw [retypeInitiatorDrain_scheduler]
    exact lifecycleRetypeDirectWithCleanupShootdown_replenishQueueOnCore_ne executingCore authCap
      target newObj st stRound c hne hRound

/-- **Cut C6g (the live `.lifecycleRetype` arm's exactness frame)**: and neither
does the domain-wide instruction-cache broadcast, so the arm the syscall runs
writes no replenish queue outside the segment its footprint declares. -/
theorem lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_replenishQueueOnCore_ne
    (executingCore : CoreId) (authCap : Capability) (target : SeLe4n.ObjId)
    (newObj : KernelObject) (st st' : SystemState) (c : CoreId)
    (hne : c ∉ lifecycleRetypeReplenishCores st target)
    (h : lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache executingCore authCap target
      newObj st = .ok ((), st')) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache at h
  cases hBase : lifecycleRetypeDirectWithCleanupShootdownPerCore executingCore authCap target
      newObj st with
  | error e =>
    rw [(Architecture.withIcacheBroadcast_error_iff (retypeIcacheOperand target)
      (lifecycleRetypeDirectWithCleanupShootdownPerCore executingCore authCap target newObj)
      st e).mpr hBase] at h
    exact absurd h (by simp)
  | ok pair =>
    obtain ⟨u, stB⟩ := pair
    cases u
    rw [(Architecture.withIcacheBroadcast_frame hBase h).2.2.1]
    exact lifecycleRetypeDirectWithCleanupShootdownPerCore_replenishQueueOnCore_ne
      executingCore authCap target newObj st stB c hne hBase


end SeLe4n.Kernel
