-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Operations.RetypeWrappers
import SeLe4n.Kernel.Lifecycle.Invariant.CleanupReservation
import SeLe4n.Kernel.Architecture.PerCoreCacheModel
import SeLe4n.Kernel.SchedContext.ReplenishAffinity
import SeLe4n.Kernel.SchedContext.SchedContextFootprint

/-!
# The destroy cleanup's scheduler footprint

`threadOccupiedCores` and the donation-arm and binding-release replenish-core
resolvers, beside the cleanup they are about
(`lifecyclePreRetypeCleanup`, `Lifecycle/Operations/CleanupPreservation.lean`),
with the exactness halves: what the destroy path writes.  The suspend pipeline's
G3 reuses the donation arm's (`SuspendFootprint.lean`).

The in-place retype that ran this cleanup, and its arm's lock set, were retired
at WS-ZA ZA5.4 part 14; the cleanup is kept for a kernel object's final-delete
finalisation (`docs/planning/UNTYPED_RESET_PLAN.md`, part 24).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId
  LockKey LockSet)

-- ============================================================================
-- §1  The destroy path's cores
-- ============================================================================
--
-- The destroy path's scheduler effects are the cleanup's, and there are two of
-- them: a TCB target ends its reservation the way a suspended thread's is
-- (`cancelDonationArmOnCore`), and a SchedContext target releases the binding it
-- holds (`releaseSchedContextBinding`, seL4's `schedContext_unbindAllTCBs` per
-- core).  Both read the **pre-state**, so this footprint is pre-state
-- computable with no mid-state bridge.

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

/-- **`v0.35.169`: the cores the destroy path's donation arm moves a RESERVATION
on**, keyed on the doomed thread's own binding — `cancelDonationArmOnCore`'s
three arms, read as cores.

`.unbound` moves nothing; `.bound` purges on the core the context's own release
link names (WS-ZA ZA6.3), read at the state the purge runs on — the context's
binding cleared, which moves no link; `.donated` returns the context and
migrates its replenishments from the holder's home to the recorded owner's, the
destination read at the **post-return** state exactly as
`cancelDonatedDonationOnCore` reads it.  A refused return migrates nothing, and
the empty list there is the transition's own behaviour rather than a narrowing.
The suspend pipeline's G3 reads it at its post-revert state. -/
def cancelDonationArmReplenishCores (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) : List CoreId :=
  match tcb.schedContextBinding with
  | .unbound => []
  | .bound scId =>
      SchedContextOps.purgeReplenishCores (st.updateSchedContext scId fun sc =>
        { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }) scId
  | .donated _ owner =>
      match cleanupDonatedSchedContext st tid with
      | .error _ => []
      | .ok st' => [determineTargetCore st tid, determineTargetCore st' owner]

/-- **`v0.35.169`: the core a binding release moves a RESERVATION on.**

`releaseSchedContextBinding` purges the context on the core its own release link
names (WS-ZA ZA6.3), read at the state the purge runs on: after the bound
thread's binding is cleared when that thread resolves, at the pre-state when it
does not.  It swept every core on the second arm while the purge had no core to
read.  A context bound to nothing has no binding to release, hence the empty
list. -/
def releaseSchedContextBindingReplenishCores (st : SystemState) (scId : SeLe4n.SchedContextId)
    (sc : SchedContext) : List CoreId :=
  match sc.boundThread with
  | none => []
  | some tid =>
      match st.getTcb? tid with
      | some _ => SchedContextOps.purgeReplenishCores (st.updateTcb tid fun t =>
          { t with scBindingScCode := 0, scBindingOwnerCode := 0 }) scId
      | none => SchedContextOps.purgeReplenishCores st scId

-- ============================================================================
-- §2  The exactness halves — what the destroy path writes
-- ============================================================================

/-- **`v0.35.169`: the `.bound` unbind writes exactly the core the context's own
release link names** (WS-ZA ZA6.3). -/
theorem cancelBoundDonationOnCore_replenishQueueOnCore_ne (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (c : CoreId) (scId : SeLe4n.SchedContextId)
    (hBind : tcb.schedContextBinding = .bound scId)
    (hne : c ∉ SchedContextOps.purgeReplenishCores (st.updateSchedContext scId fun sc =>
        { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }) scId)
    (h : cancelBoundDonationOnCore st tid tcb = .ok st') :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold cancelBoundDonationOnCore at h
  rw [hBind] at h
  rw [Except.ok.injEq] at h
  rw [← h, markKeyChangeFrom_replenishQueueOnCore]
  simp only [SystemState.updateTcb_scheduler]
  rw [SchedContextOps.purgeReplenishment_replenishQueueOnCore_of_not_mem _ _ _ hne,
    SystemState.updateSchedContext_scheduler]

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

Stated over the three-way match at an **explicit** `home`, because the
operation's `.bound` arm is handed one: `cancelDonationArmOnCore` — the destroy
path's arm — reads it off the state it runs on, while `suspendThreadOnCore`'s G3
was handed it from the **pre**-G2 state.  The purge reads its core from the
context's own release link (WS-ZA ZA6.3), so the resolver names no home and the
frame holds at every one. -/
theorem donationArmAt_replenishQueueOnCore_ne (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (home c : CoreId)
    (hne : c ∉ cancelDonationArmReplenishCores st tid tcb)
    (h : (match tcb.schedContextBinding with
          | .unbound => (Except.ok st : Except KernelError SystemState)
          | .bound _ => cancelBoundDonationOnCore st tid tcb
          | .donated _ _ => cancelDonatedDonationOnCore st tid tcb) = .ok st') :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold cancelDonationArmReplenishCores at hne
  cases hBind : tcb.schedContextBinding with
  | unbound =>
      rw [hBind] at h
      rw [Except.ok.injEq] at h; rw [← h]
  | bound scId =>
      rw [hBind] at h hne
      exact cancelBoundDonationOnCore_replenishQueueOnCore_ne st st' tid tcb c scId hBind hne h
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
segment, on both of its arms. -/
theorem releaseSchedContextBinding_replenishQueueOnCore_ne (st : SystemState)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (c : CoreId)
    (hne : c ∉ releaseSchedContextBindingReplenishCores st scId sc) :
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
      | none =>
          rw [hTcb] at hne
          exact SchedContextOps.purgeReplenishment_replenishQueueOnCore_of_not_mem _ _ _ hne
      | some tcb =>
          rw [hTcb] at hne
          dsimp only
          rw [markKeyChangeFor_replenishQueueOnCore,
            SchedContextOps.purgeReplenishment_replenishQueueOnCore_of_not_mem _ _ _ hne,
            SystemState.updateTcb_scheduler]

/-- **Where the pre-retype cleanup writes a RUN QUEUE**, as a function of the
object being destroyed.

Only the TCB arm names any core, and it names the ones the doomed thread
occupies.  Every other kind writes no run queue and no current slot, so its set
is empty.  **A SchedContext target is not an exception**: its release writes a
replenish queue, which is not one of the six slots
`observableSlotsConfinedToCores` covers, and which
`preRetypeCleanupReplenishCoresOf` declares instead. -/
def preRetypeCleanupWriteSetOf (st : SystemState) (currentObj : KernelObject) :
    List CoreId :=
  match currentObj with
  | .tcb tcb => threadOccupiedCores st tcb.tid
  | _ => []

/-- **`v0.35.169`: the cores the pre-retype cleanup moves a RESERVATION on**, as
a function of the object being destroyed — the TCB arm's donation cores, the
SchedContext arm's release cores, and nothing for any other kind. -/
def preRetypeCleanupReplenishCoresOf (st : SystemState) (target : SeLe4n.ObjId)
    (currentObj : KernelObject) : List CoreId :=
  match currentObj with
  | .tcb tcb => cancelDonationArmReplenishCores st tcb.tid tcb
  | .schedContext sc =>
      releaseSchedContextBindingReplenishCores st (SeLe4n.SchedContextId.ofObjId target) sc
  | _ => (fun _ => []) target

/-- **`v0.35.169`: and the whole pre-retype cleanup writes exactly the cores
`preRetypeCleanupReplenishCoresOf` names.**

Over all six object kinds: the TCB arm's donation step and the SchedContext
arm's release are the only two that move a replenishment, and every other step
of the pipeline — the reference sweep, the service-registry revoke, the CDT
detach, the reply and VSpace guards — frames the scheduler outright. -/
theorem lifecyclePreRetypeCleanup_replenishQueueOnCore_ne (st st' : SystemState)
    (target : SeLe4n.ObjId) (currentObj newObj : KernelObject) (c : CoreId)
    (hne : c ∉ preRetypeCleanupReplenishCoresOf st target currentObj)
    (h : lifecyclePreRetypeCleanup st target currentObj newObj = .ok st') :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold lifecyclePreRetypeCleanup at h
  unfold preRetypeCleanupReplenishCoresOf at hne
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
        · obtain rfl := Except.ok.inj h
          rw [detachTcbSlots_scheduler_eq, SystemState.cancelYieldTo_scheduler,
            cleanupTcbReferences_replenishQueueOnCore, SystemState.completeHeldYield_scheduler]
          exact cancelDonationArmOnCore_replenishQueueOnCore_ne st stArm tcb.tid tcb c hne hArm
  | schedContext sc =>
      subst hC
      simp only at h hne
      split at h
      · exact absurd h (by simp)
      · injection h with h
        subst h
        rw [SystemState.completeYieldFrom_scheduler]
        exact releaseSchedContextBinding_replenishQueueOnCore_ne st _ sc c hne
  | endpoint ep =>
      subst hC
      simp only at h
      injection h with h
      subst h
      rfl
  | cnode cn =>
      subst hC
      simp only at h
      split at h
      · exact absurd h (by simp)
      · injection h with h
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


end SeLe4n.Kernel
