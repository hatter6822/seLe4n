-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-SM SM6.C: PRODUCTION (LANDED).  The pure cross-core `.reply` dispatch op below
-- the API layer; the live `API.dispatchWithCap{,Checked}` `.reply` arm routes through
-- `endpointReplyCrossCoreDispatch{,Checked}` here, deriving the executing core from
-- the live state (`determineExecutingCore`).  The live `.replyRecv` arm routes
-- through the reply-object-aware `replyRecvBody` (in `API`), which resolves the
-- *reply capability* (authority flows from holding the reply cap, exactly like
-- `.reply`) and consumes / re-links the first-class Reply object — it does NOT use a
-- raw-thread dispatch here.  See docs/planning/SMP_CROSS_CORE_IPC_PLAN.md §3.1, §4.3,
-- §5 (SM6.C).

import SeLe4n.Kernel.IPC.CrossCore.EndpointReply
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyInvariant
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallDispatch
import SeLe4n.Kernel.IPC.Operations.Donation.Primitives
import SeLe4n.Kernel.SchedContext.ReplenishAffinity
import SeLe4n.Kernel.InformationFlow.Enforcement.Wrappers

/-!
# WS-SM SM6.C — Cross-core `.reply` / `.replyRecv` dispatch (pure; below the API layer)

The pure cross-core `.reply` dispatch operation — `endpointReplyCrossCoreDispatch`
and the information-flow-checked `endpointReplyCrossCoreDispatchChecked`.  These live
*below* `SeLe4n.Kernel.API` (no `Platform.FFI` dependency) so the live `.reply`
dispatch arm can route through them — the cross-core generalisation of the
single-core `endpointReplyWithDonation`.

The live `.replyRecv` syscall is handled one layer up by `API.replyRecvBody`, which
resolves the reply *capability* and consumes / re-links the first-class Reply object;
the underlying combined reply-and-receive transition (`endpointReplyRecvOnCore`, in
`EndpointReply`) remains available as a below-API building block.  There is
deliberately **no** raw-thread `.replyRecv` dispatch wrapper here — it would expose a
reply-without-the-reply-cap surface that bypasses the single-use Reply object.

Each dispatch composes:

* the cross-core reply (`endpointReplyOnCore` / `endpointReplyRecvOnCore` — wakes
  the original caller on its *home* core);
* the SchedContext **donation return** (`applyReplyDonationOnCore` — returns the
  replier's donated SC to the original owner and deschedules the now-passive
  replier on *its own* core); and
* the cross-core priority-inheritance **reversion** (`propagatePipChainCrossCore`
  — `revert_eq_propagate`: reversion is functionally propagation, walking the
  blocking chain up from the unblocked caller, migrating each link's run-queue
  bucket on its home core, plan §4.3).

The surfaced SGI is the reply-leg caller wake's; the cross-core PIP-chain SGIs are
re-derived from the committed-state diff by the live syscall entry
(`computeCrossCoreSgis`), exactly as the SM6.A `.call` dispatch surfaces only the
receiver-wake SGI and takes `propagatePipChainCrossCore.1` for the state.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  SM6.C.3 — Cross-core donation return (`applyReplyDonationOnCore`)
-- ============================================================================

/-- WS-SM SM6.C.3 (plan §4.3) / WS-RR RR2.8: the cross-core generalisation of
`applyReplyDonation`.  Three effects, in order:

1. the SchedContext **return** (`returnDonatedSchedContextValid`, an
   object-store-only rebinding from the server back to the original owner);
2. the SM5.H.4 **replenishment migration** from the replier's home core to the
   original owner's — the RR2.8 mirror of the `.call` path's RR2.2 migration.
   The SchedContext's pending CBS replenishments live on its *bound thread's*
   home core (`replenishQueueAffinityConsistentOnCore`), and the return moves
   that binding across cores, so without this the entries are stranded on the
   server's core, where nothing drains them for a SchedContext that is now the
   owner's.  This is the same primitive, and the same argument, the cancellation
   arm `cancelDonatedDonationOnCore` has used since SM6.E;
3. the **deschedule** of the now-passive replier on *its own* core via
   `removeRunnableOnCore … executingCore` (rather than the boot-pinned
   `removeRunnable`).

A replier that holds no donated SchedContext is a no-op (the common
non-donating reply), and self-migration — a shared home core, and in particular
every single-core configuration — is a definitional no-op, so the boot-core
instance is exactly `applyReplyDonation`
(`applyReplyDonationOnCore_bootCoreId`).

`replierHome` / `ownerHome` are the migration's endpoints, resolved by the
caller from the **pre**-state, so the `withLockSet` bracket can declare and
acquire both `SchedLockId.replenishQueue` write locks before the transition
runs; the return itself never touches a `cpuAffinity`
(`returnDonatedSchedContext_getTcb?_cpuAffinity_eq`), so a pre-state reading is
the post-state's. -/
def applyReplyDonationOnCore (st : SystemState) (replierVtid : SeLe4n.ValidThreadId)
    (executingCore : CoreId) (replierHome ownerHome : CoreId) :
    Except KernelError SystemState :=
  let replier : SeLe4n.ThreadId := replierVtid.val
  match lookupTcb st replier with
  | none => .ok st
  | some replierTcb =>
    match replierTcb.schedContextBinding with
    | .donated scId originalOwner =>
      match SeLe4n.ThreadId.toValid? originalOwner with
      | some ownerVtid =>
          match returnDonatedSchedContextValid st replierVtid scId ownerVtid with
          | .error e => .error e
          | .ok st' =>
              .ok (removeRunnableOnCore
                    (migrateSchedContextReplenishment st' scId replierHome ownerHome)
                    replier executingCore)
      | none => .error .invalidArgument
    | _ => .ok st

/-- WS-RR RR2.8: the **destination** core of the reply path's replenishment
migration — the home core of the SchedContext's original owner, or the replier's
own home when there is nothing to return (making the migration a definitional
self-no-op on that arm).

A named function rather than an inline `match` because three readers must agree
on it: the live dispatch that passes it to `applyReplyDonationOnCore`, the SM8.B
per-core write set that mirrors the dispatch's control flow, and the RR2.9
affinity proof.  Two of those are in other modules. -/
def replyDonationOwnerHome (st : SystemState) (replier : SeLe4n.ThreadId) : CoreId :=
  match replyDonationReturn? st replier with
  | some (_, owner) => determineTargetCore st owner
  | none            => determineTargetCore st replier

/-- WS-RR RR2.8 (characterisation): the cross-core donation return *is* the
`replyDonationReturn?` case split — the return, the migration and the
deschedule on the returning arm, the identity otherwise. -/
theorem applyReplyDonationOnCore_characterisation
    (st : SystemState) (replierVtid : SeLe4n.ValidThreadId)
    (executingCore replierHome ownerHome : CoreId) :
    applyReplyDonationOnCore st replierVtid executingCore replierHome ownerHome
      = (match replyDonationReturn? st replierVtid.val with
         | some (scId, owner) =>
             match SeLe4n.ThreadId.toValid? owner with
             | some ownerVtid =>
                 (match returnDonatedSchedContextValid st replierVtid scId ownerVtid with
                  | .error e => .error e
                  | .ok st' =>
                      .ok (removeRunnableOnCore
                            (migrateSchedContextReplenishment st' scId replierHome ownerHome)
                            replierVtid.val executingCore))
             | none => .error .invalidArgument
         | none => .ok st) := by
  simp only [applyReplyDonationOnCore, replyDonationReturn?]
  cases lookupTcb st replierVtid.val with
  | none => rfl
  | some replierTcb =>
    simp only []
    cases replierTcb.schedContextBinding with
    | unbound => rfl
    | bound _ => rfl
    | donated scId owner =>
      -- Both sides are now the same match tree, so the reduction closes it.
      simp only []

/-- WS-SM SM6.C.3 (bootCore bridge) / WS-RR RR2.13: `applyReplyDonationOnCore`
on the boot core with donor and donee sharing a home core is exactly the
single-core `applyReplyDonation` — the `removeRunnableOnCore … bootCoreId =
removeRunnable` backward-compatibility bridge carried through the donation
return, composed with the migration's self-pair no-op.  Every single-core
configuration is this instance. -/
theorem applyReplyDonationOnCore_bootCoreId (st : SystemState)
    (replierVtid : SeLe4n.ValidThreadId) (c : CoreId) :
    applyReplyDonationOnCore st replierVtid bootCoreId c c
      = applyReplyDonation st replierVtid := by
  simp only [applyReplyDonationOnCore, applyReplyDonation]
  cases lookupTcb st replierVtid.val with
  | none => rfl
  | some replierTcb =>
    simp only []
    cases replierTcb.schedContextBinding with
    | unbound => rfl
    | bound _ => rfl
    | donated scId owner =>
      simp only []
      cases SeLe4n.ThreadId.toValid? owner with
      | none => rfl
      | some ownerVtid =>
        simp only []
        cases returnDonatedSchedContextValid st replierVtid scId ownerVtid with
        | error e => rfl
        | ok st' =>
          simp only [migrateSchedContextReplenishment_noop, removeRunnableOnCore_bootCoreId]

/-- WS-RR RR2.8 (decomposition): a successful cross-core donation return either
left the state alone (no donated SchedContext) or ran the return, the migration
and the deschedule, in that order. -/
theorem applyReplyDonationOnCore_ok_decompose
    (st st'' : SystemState) (replierVtid : SeLe4n.ValidThreadId)
    (executingCore replierHome ownerHome : CoreId)
    (h : applyReplyDonationOnCore st replierVtid executingCore replierHome ownerHome = .ok st'') :
    (replyDonationReturn? st replierVtid.val = none ∧ st'' = st)
    ∨ ∃ (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId) (st' : SystemState),
        replyDonationReturn? st replierVtid.val = some (scId, owner) ∧
        returnDonatedSchedContext st replierVtid.val scId owner = .ok st' ∧
        st'' = removeRunnableOnCore
          (migrateSchedContextReplenishment st' scId replierHome ownerHome)
          replierVtid.val executingCore := by
  rw [applyReplyDonationOnCore_characterisation] at h
  cases hRet : replyDonationReturn? st replierVtid.val with
  | none => rw [hRet] at h; exact Or.inl ⟨rfl, (Except.ok.inj h).symm⟩
  | some pair =>
    obtain ⟨scId, owner⟩ := pair
    rw [hRet] at h
    simp only [] at h
    cases hOV : SeLe4n.ThreadId.toValid? owner with
    | none => rw [hOV] at h; cases h
    | some ownerVtid =>
      rw [hOV] at h
      have hOEq : ownerVtid.val = owner :=
        SeLe4n.ThreadId.toValid?_some_val_eq owner ownerVtid hOV
      simp only [returnDonatedSchedContextValid, hOEq] at h
      cases hR : returnDonatedSchedContext st replierVtid.val scId owner with
      | error e => rw [hR] at h; cases h
      | ok st' =>
        rw [hR] at h
        exact Or.inr ⟨scId, owner, st', rfl, hR, (Except.ok.inj h).symm⟩

/-- WS-RR RR2.9 (frame): the cross-core donation return never advances the
machine timer — the return writes objects, the migration writes replenish-queue
slots, and the deschedule writes run-queue slots. -/
theorem applyReplyDonationOnCore_machine_eq
    (st st'' : SystemState) (replierVtid : SeLe4n.ValidThreadId)
    (executingCore replierHome ownerHome : CoreId)
    (h : applyReplyDonationOnCore st replierVtid executingCore replierHome ownerHome = .ok st'') :
    st''.machine = st.machine := by
  rcases applyReplyDonationOnCore_ok_decompose st st'' replierVtid executingCore replierHome
    ownerHome h with ⟨_, hEq⟩ | ⟨scId, owner, st', _, hRet, hEq⟩
  · rw [hEq]
  · rw [hEq]
    show (removeRunnableOnCore _ _ _).machine = _
    simp only [removeRunnableOnCore, migrateSchedContextReplenishment_machine]
    exact returnDonatedSchedContext_machine_eq st st' replierVtid.val scId owner hRet

/-- WS-RR RR2.9 (frame): the cross-core donation return commits exactly the
single-core return's object store — neither the migration nor the deschedule
writes an object. -/
theorem applyReplyDonationOnCore_objects_eq
    (st st'' : SystemState) (replierVtid : SeLe4n.ValidThreadId)
    (executingCore replierHome ownerHome : CoreId)
    (h : applyReplyDonationOnCore st replierVtid executingCore replierHome ownerHome = .ok st'') :
    (replyDonationReturn? st replierVtid.val = none ∧ st''.objects = st.objects)
    ∨ ∃ (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId) (st' : SystemState),
        returnDonatedSchedContext st replierVtid.val scId owner = .ok st' ∧
        st''.objects = st'.objects := by
  rcases applyReplyDonationOnCore_ok_decompose st st'' replierVtid executingCore replierHome
    ownerHome h with ⟨hNone, hEq⟩ | ⟨scId, owner, st', _, hRet, hEq⟩
  · exact Or.inl ⟨hNone, by rw [hEq]⟩
  · refine Or.inr ⟨scId, owner, st', hRet, ?_⟩
    rw [hEq, removeRunnableOnCore_preserves_objects,
      migrateSchedContextReplenishment_objects]

-- ============================================================================
-- §1b  WS-RR RR2.9 — the reply path preserves the SM5.H affinity invariant
-- ============================================================================

/-- WS-RR RR2.9 / WS-RR RR2.20: **the donation return plus its replenishment
migration restores replenish-queue affinity consistency on every core.**

The substance of both reply-side donation arms, factored out because two live
paths perform exactly this pair: `applyReplyDonationOnCore` (which follows it
with a deschedule) and `replyRecvReturnDonation` (which does not, because the
recorded server may immediately rendezvous with a queued `Call`).

The return rebinds exactly one SchedContext — from the replier back to the
original owner — so exactly that SchedContext's replenish entries become
mis-homed, and they are exactly the entries the migration moves.  The
confinement obligation (no *other* core holds a `scId` entry) is derived rather
than assumed: `returnDonatedSchedContext`'s success witnesses the pre-state
binding, and the pre-state invariant then forces any such entry's core to be the
replier's home. -/
theorem returnDonatedSchedContext_migrate_preserves_replenishQueueAffinityConsistent_smp
    (st st' : SystemState) (replier : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId)
    (replierHome ownerHome : CoreId)
    (hObjInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st)
    (hReplierHome : determineTargetCore st replier = replierHome)
    (hOwner : determineTargetCore st owner = ownerHome)
    (hRet : returnDonatedSchedContext st replier scId owner = .ok st') :
    replenishQueueAffinityConsistent_smp
      (migrateSchedContextReplenishment st' scId replierHome ownerHome) := by
  -- The return's readings.
  have hSched : st'.scheduler = st.scheduler :=
    returnDonatedSchedContext_scheduler_eq st st' replier scId owner hRet
  have hHomeEq : ∀ tid, determineTargetCore st' tid = determineTargetCore st tid := fun tid =>
    determineTargetCore_congr st st' tid
      (returnDonatedSchedContext_getTcb?_cpuAffinity_eq st st' replier scId owner
        hObjInv hRet tid)
  have hScNe : ∀ scId', scId' ≠ scId → st'.getSchedContext? scId' = st.getSchedContext? scId' :=
    fun scId' hne => returnDonatedSchedContext_getSchedContext?_ne st st' replier
      scId scId' owner hne hObjInv hRet
  obtain ⟨scPost, hScPost, hScPostBound⟩ :=
    returnDonatedSchedContext_post_boundThread st st' replier scId owner hObjInv hRet
  obtain ⟨scPre, hScPre, hScPreBound⟩ :=
    returnDonatedSchedContext_ok_implies_sc_bound st st' replier scId owner hRet
  have hQueue : ∀ c, st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c :=
    fun c => by rw [hSched]
  -- A `scId` entry anywhere in the pre-state forces that core to be the
  -- replier's home — the RR2.8 guard's payoff.
  have hConfined : ∀ c t, (scId, t) ∈ (st.scheduler.replenishQueueOnCore c).entries →
      c = replierHome := by
    intro c t hMem
    rw [← hReplierHome]
    exact (hCons c scId t hMem scPre hScPre replier hScPreBound).symm
  have hCons1 : ∀ c, c ≠ replierHome → replenishQueueAffinityConsistentOnCore st' c := by
    intro c hcNe scId₀ t hMem sc₀ hSc₀ tid hBound
    rw [hQueue c] at hMem
    rw [hHomeEq tid]
    by_cases hk : scId₀ = scId
    · subst hk; exact absurd (hConfined c t hMem) hcNe
    · rw [hScNe scId₀ hk] at hSc₀
      exact hCons c scId₀ t hMem sc₀ hSc₀ tid hBound
  have hConsTo : replenishQueueAffinityConsistentOnCore st' ownerHome := by
    intro scId₀ t hMem sc₀ hSc₀ tid hBound
    rw [hQueue ownerHome] at hMem
    rw [hHomeEq tid]
    by_cases hk : scId₀ = scId
    · subst hk
      rw [hScPost] at hSc₀; cases hSc₀
      rw [hScPostBound] at hBound; cases hBound
      exact hOwner
    · rw [hScNe scId₀ hk] at hSc₀
      exact hCons ownerHome scId₀ t hMem sc₀ hSc₀ tid hBound
  have hConsFrom : ∀ (scId₀ : SeLe4n.SchedContextId) (t : Nat),
      (scId₀, t) ∈ (st'.scheduler.replenishQueueOnCore replierHome).entries → scId₀ ≠ scId →
        ∀ sc₀, st'.getSchedContext? scId₀ = some sc₀ →
          ∀ tid, sc₀.boundThread = some tid → determineTargetCore st' tid = replierHome := by
    intro scId₀ t hMem hk sc₀ hSc₀ tid hBound
    rw [hQueue replierHome] at hMem
    rw [hHomeEq tid, hScNe scId₀ hk] at *
    exact hCons replierHome scId₀ t hMem sc₀ hSc₀ tid hBound
  have hHome : ∀ sc, st'.getSchedContext? scId = some sc →
      ∀ tid, sc.boundThread = some tid → determineTargetCore st' tid = ownerHome := by
    intro sc hSc tid hBound
    rw [hScPost] at hSc; cases hSc
    rw [hScPostBound] at hBound; cases hBound
    rw [hHomeEq]; exact hOwner
  exact migrateSchedContextReplenishment_preserves_affinityConsistent_smp st' scId
    replierHome ownerHome
    (fun c' hFrom _ => hCons1 c' (fun hEq' => hFrom hEq'.symm))
    hConsTo hConsFrom hHome

/-- WS-RR RR2.9: **the cross-core donation return restores replenish-queue
affinity consistency on every core** — the mirror of RR2.3's call-path theorem,
and the reason the RR2.8 migration is there.

Two facts compose.  The substance is the shared return-plus-migration lemma
above, whose confinement step is derived rather than assumed because RR2.8's
`sc.boundThread = some serverTid` guard makes success witness the pre-state
binding (`returnDonatedSchedContext_ok_implies_sc_bound`) — the same role
`donateSchedContext`'s long-standing AUD-3b guard plays on the call side, and
the reason the guards had to be symmetric before either theorem could be
unconditional.  The final deschedule is then invisible to the invariant:
`removeRunnableOnCore` writes a run queue and a current slot, never a replenish
queue and never an object. -/
theorem applyReplyDonationOnCore_preserves_replenishQueueAffinityConsistent_smp
    (st st'' : SystemState) (replierVtid : SeLe4n.ValidThreadId)
    (executingCore replierHome ownerHome : CoreId)
    (hObjInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st)
    (hReplierHome : determineTargetCore st replierVtid.val = replierHome)
    (hOwnerHome : ∀ scId owner, replyDonationReturn? st replierVtid.val = some (scId, owner) →
        determineTargetCore st owner = ownerHome)
    (h : applyReplyDonationOnCore st replierVtid executingCore replierHome ownerHome = .ok st'') :
    replenishQueueAffinityConsistent_smp st'' := by
  rcases applyReplyDonationOnCore_ok_decompose st st'' replierVtid executingCore replierHome
    ownerHome h with ⟨_, hEq⟩ | ⟨scId, owner, st', hRes, hRet, hEq⟩
  · rw [hEq]; exact hCons
  · rw [hEq]
    -- The deschedule is a frame for the invariant; the substance is the migration.
    intro c
    exact (replenishQueueAffinityConsistentOnCore_frame
        (removeRunnableOnCore_replenishQueueOnCore _ _ _ _)
        (removeRunnableOnCore_preserves_objects _ _ _)).mpr
      (returnDonatedSchedContext_migrate_preserves_replenishQueueAffinityConsistent_smp
        st st' replierVtid.val scId owner replierHome ownerHome hObjInv hCons hReplierHome
        (hOwnerHome scId owner hRes) hRet c)

-- ============================================================================
-- §2  SM6.C.3 — Donation-chain lock-set extension
-- ============================================================================

/-- WS-SM SM6.C.3 (plan §4.3): the cross-core donation-chain lock-set extension
for reply.  When the reply returns a SchedContext to its original owner, the
`endpointReply` lock-set is *exactly* the non-returning lock-set extended with the
returned SchedContext's **write** lock and the original owner's TCB **write**
lock — so the SC migration (`returnDonatedSchedContextValid` rebinding
`boundThread` across cores, SM5.H.4) and the owner's re-activation both run under
held write locks, serialised against every other core. -/
theorem lockSet_endpointReply_donation_extension
    (replier : SeLe4n.ThreadId) (cnRoot : SeLe4n.ObjId) (target : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId) :
    lockSet_endpointReply replier cnRoot target (some scId) (some originalOwner)
      = lockSetExtendOpt
          (lockSetExtendOpt
            (lockSet_endpointReply replier cnRoot target none none)
            (some (schedContextLock scId, .write)))
          (some (tcbLock originalOwner, .write)) := by
  unfold lockSet_endpointReply
  rfl

-- ============================================================================
-- §3  SM6.C — Full cross-core `.reply` dispatch (reply + donation + PIP revert)
-- ============================================================================

/-- WS-SM SM6.C (operation): the cross-core `Reply` **delivery + scheduling**
primitive — below the API layer.  The cross-core reply (`endpointReplyOnCore` —
caller woken on its home core), then the SchedContext donation **return**
(`applyReplyDonationOnCore` — the passive **recorded server** returns the donated
SC and is descheduled on its own core), then the cross-core priority-inheritance
**reversion** (`propagatePipChainCrossCore` over the recorded server's blocking
chain — re-derives each holder's boost from its remaining waiters, migrating
buckets on home cores).  The donation/PIP target is the server recorded in the
caller's `blockedOnReply` link (`recordedReplyServer? st target`), **not** the
reply-cap holder `replier` (a delegated cap holder is not the donee — PR #822
review).  Surfaces the reply-leg caller-wake SGI; the chain-walk SGIs are
re-derived from the committed diff.

**Full reply semantics — the single-use Reply-object teardown is folded into the
transition** (PR #827 review #3, superseding the PR #822 delivery-only split):
`endpointReplyOnCore` itself consumes the answered caller↔Reply link atomically
with the delivery (`consumeCallerReply` — clear `target.replyObject` *and*
`reply.caller := none`, keyed on the woken caller's own `replyObject`).  This
dispatch helper therefore adds only the SchedContext donation **return** and the
PIP **reversion** on top; the live `.reply` dispatch arm
(`API.dispatchWithCap{,Checked}`) resolves the reply *capability* to
`(rid, reply.caller = target)` and routes here with **no** separate consume step.
A direct below-API caller of `endpointReplyOnCore` now gets single-use reply
semantics by construction — the Reply object is freed the moment the reply is
delivered, so it can be re-linked or cleaned up immediately. -/
def endpointReplyCrossCoreDispatch
    (replier : SeLe4n.ThreadId) (target : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (Option (CoreId × SgiKind)) :=
  match endpointReplyOnCore replier target msg executingCore st with
  | (_, .error e) => (st, .error e)
  | (st1, .ok replySgi?) =>
      -- WS-SM SM6.D (PR #822 review): the SchedContext donation **return** and the
      -- priority-inheritance **reversion** are keyed on the **recorded server**
      -- (`target`'s `blockedOnReply` link, resolved from the pre-state `st` —
      -- `endpointReplyOnCore` succeeded, so it is `some expected`), who holds the
      -- donated SC and the PIP boost, NOT the reply-cap holder `replier` (which may
      -- be a *delegate* after the 6J-lYm gate removal).  In the non-delegated case
      -- (`replier = expected`) this is identical to the legacy `replier`-keyed path.
      match recordedReplyServer? st target with
      | some expected =>
          match SeLe4n.ThreadId.toValid? expected with
          | some expectedV =>
              -- WS-SM SM6.D (PR #822 review): deschedule the now-passive server on
              -- **its own** core, derived from the pre-state (`determineExecutingCore
              -- st expected`), not the (possibly delegated) cap holder's syscall core
              -- `executingCore`.  Reusing the delegate's core would point
              -- `removeRunnableOnCore` at the wrong run queue, leaving the recorded
              -- server current/runnable on its own core after its donated SC was
              -- returned.  In the non-delegated case the server *is* the syscall
              -- thread, so `determineExecutingCore st expected = executingCore`.
              let expectedCore := determineExecutingCore st expected
              -- WS-RR RR2.12: the live `.reply` arm now routes through the
              -- **migrating** donation return.  Both migration endpoints are
              -- resolved from the **pre**-state `st`, which is what the
              -- `withLockSet` bracket sees when it acquires the two
              -- `SchedLockId.replenishQueue` write locks
              -- (`endpointReplyCrossCoreDispatchSchedLockSet`), and which agrees
              -- with the post-reply reading because `endpointReplyOnCore` writes
              -- `ipcState` / queue links / the Reply object and never a
              -- `schedContextBinding` or a `cpuAffinity`.  When the recorded
              -- server holds no donated SchedContext there is nothing to move and
              -- the endpoints coincide, making the migration a definitional
              -- no-op.
              match applyReplyDonationOnCore st1 expectedV expectedCore
                  (determineTargetCore st expected) (replyDonationOwnerHome st expected) with
              | .error e => (st, .error e)
              | .ok st2 =>
                  ((PriorityInheritance.propagatePipChainCrossCore st2 expected executingCore).1, .ok replySgi?)
          | none => (st, .error .invalidArgument)
      | none => (st, .error .replyCapInvalid)

/-- WS-SM SM6.C (live `.reply` enforcement): the **information-flow-checked**
cross-core reply dispatch — the cross-core analogue of `endpointReplyChecked`
composed with `endpointReplyCrossCoreDispatch`.  Mirrors the single-core checked
`.reply` arm: it first applies the SM-IF security guard
(`securityFlowsTo replierLabel targetLabel`, rejecting with `.flowDenied` on a
disallowed flow — the reply may flow information from the replier's domain to the
caller's), then runs the full cross-core dispatch. -/
def endpointReplyCrossCoreDispatchChecked
    (ctx : LabelingContext) (replier : SeLe4n.ThreadId) (target : SeLe4n.ThreadId)
    (msg : IpcMessage) (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (Option (CoreId × SgiKind)) :=
  if securityFlowsTo (ctx.threadLabelOf replier) (ctx.threadLabelOf target) then
    endpointReplyCrossCoreDispatch replier target msg executingCore st
  else
    (st, .error .flowDenied)

/-- WS-SM SM6.C: a disallowed flow is rejected before any state change — the
checked cross-core reply dispatch is fail-closed (state unchanged, `.flowDenied`). -/
theorem endpointReplyCrossCoreDispatchChecked_flow_denied
    (ctx : LabelingContext) (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hDeny : securityFlowsTo (ctx.threadLabelOf replier) (ctx.threadLabelOf target) = false) :
    endpointReplyCrossCoreDispatchChecked ctx replier target msg executingCore st
      = (st, .error .flowDenied) := by
  simp [endpointReplyCrossCoreDispatchChecked, hDeny]

/-- WS-SM SM6.C: when the flow is permitted, the checked dispatch is exactly the
unchecked cross-core reply dispatch — the guard is a pure precondition. -/
theorem endpointReplyCrossCoreDispatchChecked_flow_allowed
    (ctx : LabelingContext) (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hAllow : securityFlowsTo (ctx.threadLabelOf replier) (ctx.threadLabelOf target) = true) :
    endpointReplyCrossCoreDispatchChecked ctx replier target msg executingCore st
      = endpointReplyCrossCoreDispatch replier target msg executingCore st := by
  simp [endpointReplyCrossCoreDispatchChecked, hAllow]

-- ============================================================================
-- §4  SM6.C — `.reply` checked-dispatch equivalence
-- ============================================================================
--
-- NOTE: there is deliberately no raw-thread cross-core `.replyRecv` dispatch
-- wrapper here.  The live `.replyRecv` syscall routes through `API.replyRecvBody`,
-- which resolves the reply *capability* and consumes / re-links the first-class
-- Reply object; the underlying combined transition `endpointReplyRecvOnCore`
-- (in `EndpointReply`) remains the below-API building block.  A raw `(replyTarget :
-- ThreadId)` dispatch wrapper was removed because it exposed a reply-without-the-
-- reply-cap surface that bypassed the single-use Reply object (PR #822 review).

/-- WS-SM SM6.C: when the reply leg flow is permitted, the checked reply dispatch
is exactly the unchecked cross-core dispatch — the guard is a pure precondition.
The single-gate companion of the `.replyRecv` flow-allowed lemma. -/
theorem endpointReplyCrossCoreDispatchChecked_eq_unchecked_of_flow
    (ctx : LabelingContext) (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hAllow : securityFlowsTo (ctx.threadLabelOf replier) (ctx.threadLabelOf target) = true) :
    endpointReplyCrossCoreDispatchChecked ctx replier target msg executingCore st
      = endpointReplyCrossCoreDispatch replier target msg executingCore st :=
  endpointReplyCrossCoreDispatchChecked_flow_allowed ctx replier target msg executingCore st hAllow

-- ============================================================================
-- §5  SM6.C.9 — Reply donation-chain length bound (donation k > 2)
-- ============================================================================

/-- WS-SM SM6.C.9 (reply chain length bound): the cross-core priority-inheritance
**reversion** the reply dispatch runs (`propagatePipChainCrossCore` over the
unblocked caller's blocking chain) emits **at most `fuel`** cross-core SGIs —
with the default `fuel := objectIndex.length`, at most one per kernel object.  A
deep donation chain (k > 2 nested passive servers) therefore terminates and pokes
a bounded number of remote cores: the chain walk is structurally recursive on
fuel, and the acyclicity invariant
(`propagatePipChainCrossCore_preserves_blockingAcyclic`) guarantees it never
revisits a holder, so `objectIndex.length` fuel always exhausts the chain. -/
theorem endpointReply_donation_chain_length_bounded
    (st : SystemState) (caller : SeLe4n.ThreadId) (executingCore : CoreId) (fuel : Nat) :
    (PriorityInheritance.propagatePipChainCrossCore st caller executingCore fuel).2.length ≤ fuel := by
  induction fuel generalizing st caller with
  | zero => simp [PriorityInheritance.propagatePipChainCrossCore]
  | succ n ih =>
    rw [PriorityInheritance.propagatePipChainCrossCore_step]
    cases hsgi : (PriorityInheritance.pipBoostWithWake st caller executingCore).2 with
    | none =>
      cases hbs : PriorityInheritance.blockingServer st caller with
      | none => simp [hsgi]
      | some nextServer =>
        simp only [hsgi]
        exact Nat.le_trans
          (by simpa using ih (PriorityInheritance.pipBoostWithWake st caller executingCore).1 nextServer)
          (Nat.le_succ n)
    | some s =>
      cases hbs : PriorityInheritance.blockingServer st caller with
      | none => simp only [hsgi]; exact Nat.succ_le_succ (Nat.zero_le n)
      | some nextServer =>
        simp only [hsgi, List.singleton_append, List.length_cons]
        exact Nat.succ_le_succ (ih (PriorityInheritance.pipBoostWithWake st caller executingCore).1 nextServer)

end SeLe4n.Kernel
