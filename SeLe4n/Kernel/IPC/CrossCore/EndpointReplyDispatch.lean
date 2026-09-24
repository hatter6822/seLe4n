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
3. the **deschedule** of the now-passive replier at its **placement** —
   `descheduleAtPlacement`, which resolves the core the thread is actually
   queued or current on and writes nothing when it is on neither.

   `v0.35.37`: this was `removeRunnableOnCore … executingCore` with the core
   supplied by the caller as `determineExecutingCore st expected`, which finds a
   core the thread is *current* on and otherwise answers `bootCoreId`.  A
   recorded server that is **queued rather than running** — preempted by its own
   core's timer tick — therefore had its deschedule land on the boot core, where
   it is not, so the step was a complete no-op on exactly the delegated reply the
   `expectedCore` resolution was introduced for.  The server is `.unbound` by
   then and `resolveEffectivePrioDeadline`'s `.unbound` arm returns its legacy
   TCB priority, so it would be selected on its own core and run charged to no
   reservation.  `placedCoreOf?` is the *fact*; `determineExecutingCore` was a
   proxy for it, and this project has now met that substitution at four sites.

   The core is no longer a **parameter**: a parameter is a place for a caller to
   be wrong, and the operation resolves a thread it was handed, so its placement
   is something to look up rather than to accept.

A replier that holds no donated SchedContext is a no-op (the common
non-donating reply), and self-migration — a shared home core, and in particular
every single-core configuration — is a definitional no-op, so a replier placed
on the boot core reduces to `applyReplyDonation`
(`applyReplyDonationOnCore_eq_single_of_placed_at_bootCore`).

`holderHome` / `ownerHome` are the migration's endpoints, resolved by the
caller from the **pre**-state (`holderHome` is where the context's *outgoing*
bound thread's replenishments live, `ownerHome` where the incoming one's will —
both `determineTargetCore`, which is the correct resolver for a replenish queue
because that queue is keyed by affinity rather than by placement), so the `withLockSet` bracket can declare and
acquire both `SchedLockId.replenishQueue` write locks before the transition
runs; the return itself never touches a `cpuAffinity`
(`returnDonatedSchedContext_getTcb?_cpuAffinity_eq`), so a pre-state reading is
the post-state's. -/
def applyReplyDonationOnCore (st : SystemState) (rid : SeLe4n.ReplyId)
    (targetVtid : SeLe4n.ValidThreadId)
    (holderHome ownerHome : CoreId) :
    Except KernelError SystemState :=
  let target : SeLe4n.ThreadId := targetVtid.val
  match replyFrameHeadHolder? st rid with
  | none => .ok st
  | some (scId, holder) =>
      match SeLe4n.ThreadId.toValid? holder with
      | some holderVtid =>
          -- **WS-OD OD4.4**: the resolved return, exactly as the single-core twin
          -- `applyReplyDonation` runs it — the new owner comes off the context's
          -- own reply stack, so a depth-≥ 2 return settles the context on the
          -- thread that is still owed it rather than on the intermediate donor.
          -- **WS-HP HP4.3**: the thread that loses the context is the pair's
          -- `holder` and the one that gains it is the argument, so the deschedule
          -- and the migration's source both name `holder` — where before they
          -- named the argument, because the argument *was* the server.
          -- **WS-HP HP10.7**: the recipient at the bottom of the stack is the
          -- reservation's recorded origin rather than the thread reachability
          -- names.  `ownerHome` must therefore be the *recipient's* home core and
          -- not the answered caller's, or the replenishment migration moves the
          -- queue to a core the reservation does not live on and
          -- `replenishQueueAffinityConsistentOnCore` is false from the instant it
          -- commits -- `replyDonationRecipientHome` is what the live dispatch
          -- passes, and `applyReplyDonationOnCore_ownerHome_is_recipient_home`
          -- is the tie.
          match returnDonatedSchedContextResolved st holderVtid.val scId
                  (replyDonationRecipient st scId target) with
          | .error e => .error e
          | .ok st' =>
              .ok (descheduleAtPlacement
                    (migrateSchedContextReplenishment st' scId holderHome ownerHome)
                    holder)
      | none => .error .invalidArgument

/-- **WS-HP HP4.3: the SOURCE core of the reply path's replenishment migration**
-- the home core of the thread currently holding the context the answered frame
heads, or the answered caller's own home when the frame heads nothing (which
makes the migration a definitional self-no-op on exactly the arm that pops
nothing).

The `v0.35.38` replacement for `replyDonationOwnerHome`, which answered the
*destination* question off the binding-driven trigger.  Under the head-driven
trigger the destination is the answered caller, which every caller already holds,
so only the source needs resolving -- and it must be resolved from the **same
trigger the operation runs**, or the migration moves a queue the pop did not
touch.  That is why this reads `replyFrameHeadHolder?` rather than a binding:
the retired resolver's `replyDonationReturn?` and this operation's trigger are
the two that HP6 makes disagree.

A named function rather than an inline `match` because three readers must agree
on it: the live dispatch that passes it to `applyReplyDonationOnCore`, the SM8.B
per-core write set that mirrors the dispatch's control flow, and the RR2.9
affinity proof.  Two of those are in other modules. -/
def replyDonationHolderHome (st : SystemState) (rid : SeLe4n.ReplyId)
    (target : SeLe4n.ThreadId) : CoreId :=
  match replyFrameHeadHolder? st rid with
  | some (_, holder) => determineTargetCore st holder
  | none             => determineTargetCore st target

/-- The resolver on the popping arm: the holder's own home. -/
theorem replyDonationHolderHome_of_head (st : SystemState) (rid : SeLe4n.ReplyId)
    (target : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    (h : replyFrameHeadHolder? st rid = some (scId, holder)) :
    replyDonationHolderHome st rid target = determineTargetCore st holder := by
  unfold replyDonationHolderHome; rw [h]

/-- **WS-HP HP10.7: the DESTINATION core of the reply path's replenishment
migration** — the home of the thread the pop actually hands the reservation to.

HP4.3's `replyDonationHolderHome` resolves the migration's *source*, and its
docstring recorded that the destination needed no resolver because "the
destination is the answered caller, which every caller already holds".  HP10.7 is
what makes that sentence false: at the bottom of a reply stack the recipient is
the reservation's recorded **origin**, and the origin's home core is not the
answered caller's in general.

**This is not cosmetic.**  The CBS replenishments of a scheduling context live on
its bound thread's home core (`replenishQueueAffinityConsistentOnCore`, SM5.H), so
a hand-off that migrates them to the wrong core makes that invariant false from
the instant it commits — the standing constraint every SchedContext hand-off in
this tree is held to.  Redirecting the recipient without redirecting this is
exactly the shape the project calls *a proxy is not the fact*: the answered caller
is a cheap stand-in for the recipient that stops being one precisely on the states
this phase exists for.

**It mirrors the source resolver clause for clause**, and for the same reason: the
live dispatch does not destructure the trigger — `applyReplyDonationOnCore` does
that internally — so the destination has to be resolved from `rid`, and three
readers must agree on it (the dispatch that passes it, the affinity proof that
states it, and the per-core write set that mirrors the dispatch).

**It is definitionally the pre-HP10.7 expression wherever the redirect is the
identity** (`replyDonationRecipientHome_eq_target_of_no_origin`), which is every
state before HP10.4 recorded an origin and every pop whose surviving stack still
names an outer caller. -/
def replyDonationRecipientHome (st : SystemState) (rid : SeLe4n.ReplyId)
    (target : SeLe4n.ThreadId) : CoreId :=
  match replyFrameHeadHolder? st rid with
  | some (scId, _) => determineTargetCore st (replyDonationRecipient st scId target)
  | none           => determineTargetCore st target

/-- The destination resolver on the popping arm: the redirected recipient's home. -/
theorem replyDonationRecipientHome_of_head (st : SystemState) (rid : SeLe4n.ReplyId)
    (target : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    (h : replyFrameHeadHolder? st rid = some (scId, holder)) :
    replyDonationRecipientHome st rid target
      = determineTargetCore st (replyDonationRecipient st scId target) := by
  unfold replyDonationRecipientHome; rw [h]

/-- WS-HP HP10.7: **the pre-HP10.7 destination wherever no origin is recorded.**
The definitional equality that carries every pre-flip affinity result across. -/
theorem replyDonationRecipientHome_eq_target_of_no_origin (st : SystemState)
    (rid : SeLe4n.ReplyId) (target : SeLe4n.ThreadId)
    (h : ∀ scId holder, replyFrameHeadHolder? st rid = some (scId, holder) →
        donationOriginRecipient? st scId = none) :
    replyDonationRecipientHome st rid target = determineTargetCore st target := by
  unfold replyDonationRecipientHome
  cases hTrig : replyFrameHeadHolder? st rid with
  | none => rfl
  | some pair =>
    obtain ⟨scId, holder⟩ := pair
    simp only [replyDonationRecipient_eq_of_no_origin st scId target (h scId holder hTrig)]

/-- **WS-RR RR8.12 Cut C3a: the replenish-queue cores the reply path's donation
return migrates between** — the two homes the dispatch hands
`applyReplyDonationOnCore`, keyed on the trigger the pop itself reads
(`replyFrameHeadHolder?`), and `[]` where the frame heads nothing, because there
the return is the identity.

One definition for both reply-shaped arms: the `.reply` dispatch's replenish
segment reads it at the reply leg's post-state
(`endpointReplyDispatchReplenishCores`, §6), and so does the `.replyRecv`
footprint's pop component (`replyRecvHandoffReplenishCores`, `Kernel/API.lean`),
whose pop resolves the same trigger at the same state
(`replyRecvPopDonation_holder_eq_frameHead`).  Spelled through the two named home
resolvers rather than through `determineTargetCore` directly, so the three readers
those resolvers already keep in step — the dispatch, the affinity proof, the
per-core write set — gain a fourth for free; `_of_head` is the expanded form the
`.replyRecv` coverage consumes.  Declared here, beside the resolvers and below both
askers, because a shared answer must be reachable from every asker. -/
def replyDonationReturnReplenishCores (st : SystemState) (rid : SeLe4n.ReplyId)
    (target : SeLe4n.ThreadId) : List CoreId :=
  match replyFrameHeadHolder? st rid with
  | some _ => [replyDonationHolderHome st rid target, replyDonationRecipientHome st rid target]
  | none => []

/-- A frame that heads nothing returns nothing, so there is nothing to migrate. -/
@[simp] theorem replyDonationReturnReplenishCores_of_no_head (st : SystemState)
    (rid : SeLe4n.ReplyId) (target : SeLe4n.ThreadId)
    (h : replyFrameHeadHolder? st rid = none) :
    replyDonationReturnReplenishCores st rid target = [] := by
  unfold replyDonationReturnReplenishCores; rw [h]

/-- On the popping arm: the holder's home and the redirected recipient's, expanded
through `replyDonationHolderHome_of_head` / `replyDonationRecipientHome_of_head`. -/
theorem replyDonationReturnReplenishCores_of_head (st : SystemState) (rid : SeLe4n.ReplyId)
    (target : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    (h : replyFrameHeadHolder? st rid = some (scId, holder)) :
    replyDonationReturnReplenishCores st rid target
      = [determineTargetCore st holder,
         determineTargetCore st (replyDonationRecipient st scId target)] := by
  unfold replyDonationReturnReplenishCores
  rw [h, replyDonationHolderHome_of_head st rid target scId holder h,
    replyDonationRecipientHome_of_head st rid target scId holder h]

/-- **WS-HP HP4.4: the cores the head-driven pop's deschedule may write.**

The thread the pop deschedules is the *holder* the trigger resolves, not the
operation's argument, so the core list is resolved through that same trigger.
Naming the argument's placement would typecheck and describe a different thread
entirely -- the answered caller, which this leg does not deschedule at all -- and
that is the plan's SS3.8.2 hazard reaching an information-flow claim.

Empty when the frame heads nothing, which is exact: there the step is the
identity.

Relocated to production at **WS-RR RR8.12 Cut C3a**, beside the two home resolvers
it sits with, so the production `.reply` write set can read it; its confinement
theorem `applyReplyDonationOnCore_confinedToCores` stays in
`InformationFlow/NonInterferenceCrossCore.lean`, because
`observableSlotsConfinedToCores` is that module's predicate. -/
def replyDonationDescheduleCores (st : SystemState) (rid : SeLe4n.ReplyId) : List CoreId :=
  match replyFrameHeadHolder? st rid with
  | none => []
  | some (_, holder) => descheduleAtPlacementCores st holder

/-- WS-RR RR2.8 (characterisation): the cross-core donation return *is* the
`replyDonationReturn?` case split — the return, the migration and the
deschedule on the returning arm, the identity otherwise. -/
theorem applyReplyDonationOnCore_characterisation
    (st : SystemState) (rid : SeLe4n.ReplyId) (targetVtid : SeLe4n.ValidThreadId)
    (holderHome ownerHome : CoreId) :
    applyReplyDonationOnCore st rid targetVtid holderHome ownerHome
      = (match replyFrameHeadHolder? st rid with
         | some (scId, holder) =>
             match SeLe4n.ThreadId.toValid? holder with
             | some holderVtid =>
                 -- **WS-OD OD4.4**: the model follows the operation onto the
                 -- reply-stack resolver.  **WS-HP HP4.3**: and onto the
                 -- head-driven trigger, whose pair names the thread that LOSES
                 -- the context — so the deschedule and the migration source are
                 -- `holder`, never the argument.  **WS-HP HP10.7**: and onto
                 -- the redirect, so the recipient at the bottom of the stack is
                 -- the reservation's recorded origin.
                 (match returnDonatedSchedContextResolved st holderVtid.val scId
                     (replyDonationRecipient st scId targetVtid.val) with
                  | .error e => .error e
                  | .ok st' =>
                      .ok (descheduleAtPlacement
                            (migrateSchedContextReplenishment st' scId holderHome ownerHome)
                            holder))
             | none => .error .invalidArgument
         | none => .ok st) := by
  simp only [applyReplyDonationOnCore]
  cases replyFrameHeadHolder? st rid with
  | none => rfl
  | some pair =>
    obtain ⟨_, holder⟩ := pair
    cases hHV : SeLe4n.ThreadId.toValid? holder with
    | none => rfl
    | some holderVtid => rfl

/-- `placedCoreOf?` reads the scheduler alone, so a step that writes only objects
leaves it exactly where it was.  The transport the single-core bridge below needs,
and the reason that bridge can state its hypothesis on the **pre**-state: a caller
can discharge a fact about the state it holds, not about one the operation
computes. -/
theorem placedCoreOf?_congr_of_scheduler_eq {st st' : SystemState}
    (tid : SeLe4n.ThreadId) (h : st'.scheduler = st.scheduler) :
    placedCoreOf? st' tid = placedCoreOf? st tid := by
  unfold placedCoreOf?; rw [h]

/-- WS-SM SM6.C.3 (bootCore bridge) / WS-RR RR2.13, restated at `v0.35.37`:
`applyReplyDonationOnCore` with donor and donee sharing a home core is the
single-core `applyReplyDonation` **at a replier the state places on the boot
core** — the `removeRunnableOnCore … bootCoreId = removeRunnable`
backward-compatibility bridge carried through the donation return, composed with
the migration's self-pair no-op.

The hypothesis is what the placement resolver costs, and it is not a weakening
this bridge could have avoided: the deschedule is `descheduleAtPlacement` now,
which writes the core the replier is *on*, so an unconditional equation with the
boot-pinned `removeRunnable` would be false of exactly the states the `v0.35.37`
finding is about.  It is free on the configurations the bridge exists for — in a
single-core model `allCores = [bootCoreId]`, so a placed thread is placed there
— and a thread the state places **nowhere** is not covered, because there the
single-core spelling still runs `removeRunnableOnCore … bootCoreId` while this
one is the identity; the two agree extensionally and not definitionally, and
claiming otherwise would be the kind of unproved convenience this cut is
removing.

**WS-HP HP4.3**: the hypothesis is about the **holder the trigger names**, not
about the argument, and it is quantified rather than fixed because the holder is
resolved from the state — the argument is the thread that *gains* the context
now, and its placement says nothing about the deschedule.  A hypothesis on
`targetVtid` would have been about the wrong thread while still typechecking,
which is the plan's SS3.8.2 hazard reaching a theorem statement. -/
theorem applyReplyDonationOnCore_eq_single_of_placed_at_bootCore (st : SystemState)
    (rid : SeLe4n.ReplyId) (targetVtid : SeLe4n.ValidThreadId) (c : CoreId)
    (hPlaced : ∀ (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId),
        replyFrameHeadHolder? st rid = some (scId, holder) →
        placedCoreOf? st holder = some bootCoreId) :
    applyReplyDonationOnCore st rid targetVtid c c
      = applyReplyDonation st rid targetVtid := by
  simp only [applyReplyDonationOnCore, applyReplyDonation]
  cases hTrig : replyFrameHeadHolder? st rid with
  | none => rfl
  | some pair =>
    obtain ⟨scId, holder⟩ := pair
    simp only []
    cases SeLe4n.ThreadId.toValid? holder with
    | none => rfl
    | some holderVtid =>
      simp only []
      -- **WS-HP HP10.7**: both spellings run the same redirect, so the bridge is
      -- unaffected -- the split just has to name it.
      cases hRet : returnDonatedSchedContextResolved st holderVtid.val scId
          (replyDonationRecipient st scId targetVtid.val) with
      | error e => rfl
      | ok st' =>
        obtain ⟨_, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hRet
        have hSched : st'.scheduler = st.scheduler :=
          returnDonatedSchedContext_scheduler_eq st st' _ _ _ _ hPop
        simp only [migrateSchedContextReplenishment_noop, descheduleAtPlacement, descheduleAt,
          placedCoreOf?_congr_of_scheduler_eq _ hSched, hPlaced scId holder hTrig,
          removeRunnableOnCore_bootCoreId]

/-- WS-RR RR2.8 (decomposition): a successful cross-core donation return either
left the state alone (no donated SchedContext) or ran the return, the migration
and the deschedule, in that order.

**WS-HP HP4.3**: the holder is bound as a `ValidThreadId`, for the reason the
single-core `applyReplyDonation_ok_decompose` gives — the operation's
`.invalidArgument` arm established it, so a consumer reads it back out instead of
re-deriving it. -/
theorem applyReplyDonationOnCore_ok_decompose
    (st st'' : SystemState) (rid : SeLe4n.ReplyId) (targetVtid : SeLe4n.ValidThreadId)
    (holderHome ownerHome : CoreId)
    (h : applyReplyDonationOnCore st rid targetVtid holderHome ownerHome = .ok st'') :
    (replyFrameHeadHolder? st rid = none ∧ st'' = st)
    ∨ ∃ (scId : SeLe4n.SchedContextId) (holderVtid : SeLe4n.ValidThreadId)
        (newOwner? : Option SeLe4n.ThreadId) (st' : SystemState),
        replyFrameHeadHolder? st rid = some (scId, holderVtid.val) ∧
        -- **WS-OD OD4.4**: the resolver's answer is part of the decomposition,
        -- exactly as in the single-core `applyReplyDonation_ok_decompose`.
        replyStackOuterCaller? st scId = .ok newOwner? ∧
        -- **WS-HP HP4.3**: the return's `serverTid` is the trigger's `holder` and
        -- its `originalOwner` is the argument — the two that swapped places.
        -- **WS-HP HP10.7**: and the `originalOwner` is the *redirect* of that
        -- argument, which at the bottom of the stack is the reservation's
        -- recorded origin.  A consumer that wants the pre-HP10.7 reading takes
        -- `replyDonationRecipient_eq_of_no_origin` and gets its old statement
        -- back definitionally.
        returnDonatedSchedContext st holderVtid.val scId
          (replyDonationRecipient st scId targetVtid.val) newOwner? = .ok st' ∧
        st'' = descheduleAtPlacement
          (migrateSchedContextReplenishment st' scId holderHome ownerHome)
          holderVtid.val := by
  rw [applyReplyDonationOnCore_characterisation] at h
  cases hTrig : replyFrameHeadHolder? st rid with
  | none => rw [hTrig] at h; exact Or.inl ⟨rfl, (Except.ok.inj h).symm⟩
  | some pair =>
    obtain ⟨scId, holder⟩ := pair
    rw [hTrig] at h
    simp only [] at h
    cases hHV : SeLe4n.ThreadId.toValid? holder with
    | none => rw [hHV] at h; cases h
    | some holderVtid =>
      rw [hHV] at h
      have hHEq : holderVtid.val = holder :=
        SeLe4n.ThreadId.toValid?_some_val_eq holder holderVtid hHV
      subst hHEq
      simp only [] at h
      cases hR : returnDonatedSchedContextResolved st holderVtid.val scId
          (replyDonationRecipient st scId targetVtid.val) with
      | error e => rw [hR] at h; cases h
      | ok st' =>
        rw [hR] at h
        obtain ⟨n, hRes, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hR
        exact Or.inr ⟨scId, holderVtid, n, st', rfl, hRes, hPop, (Except.ok.inj h).symm⟩

/-- **WS-RR RR8.12 Cut C3a (the licence)**: a successful return whose frame heads a
context **is** the pop, then the SM5.H migration between exactly the two cores it
was handed, then the holder's deschedule at its placement — so a footprint
declaring the pair `replyDonationReturnReplenishCores` names declares the
migration's own endpoints, not a proxy for them. -/
theorem applyReplyDonationOnCore_ok_migrates (st st'' : SystemState) (rid : SeLe4n.ReplyId)
    (targetVtid : SeLe4n.ValidThreadId) (holderHome ownerHome : CoreId)
    (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    (hHead : replyFrameHeadHolder? st rid = some (scId, holder))
    (h : applyReplyDonationOnCore st rid targetVtid holderHome ownerHome = .ok st'') :
    ∃ st', st'' = descheduleAtPlacement
      (migrateSchedContextReplenishment st' scId holderHome ownerHome) holder := by
  rcases applyReplyDonationOnCore_ok_decompose st st'' rid targetVtid holderHome ownerHome h with
    ⟨hNone, _⟩ | ⟨scId', holderVtid, _, st', hHead', _, _, hEq⟩
  · exact absurd (hHead.symm.trans hNone) (by simp)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hHead'.symm.trans hHead))
    exact ⟨st', hEq⟩

/-- **WS-RR RR8.12 Cut C3a (frame)**: and where the frame heads nothing the return
writes no replenish queue, because it writes nothing at all. -/
theorem applyReplyDonationOnCore_replenishQueueOnCore_of_no_head (st st'' : SystemState)
    (rid : SeLe4n.ReplyId) (targetVtid : SeLe4n.ValidThreadId) (holderHome ownerHome : CoreId)
    (hNone : replyFrameHeadHolder? st rid = none)
    (h : applyReplyDonationOnCore st rid targetVtid holderHome ownerHome = .ok st'')
    (c : CoreId) :
    st''.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  rcases applyReplyDonationOnCore_ok_decompose st st'' rid targetVtid holderHome ownerHome h with
    ⟨_, hEq⟩ | ⟨scId, holderVtid, _, _, hHead, _, _, _⟩
  · rw [hEq]
  · exact absurd (hNone.symm.trans hHead) (by simp)

/-- **WS-RR RR8.12 Cut C6c: the reply donation's exactness frame.**

`…_of_no_head` above says the pop moves nothing where the answered frame heads
no context; this says *where* it moves when it does, which is what the
footprint's replenish clause needs.  Three of the four steps the decomposition
names frame every replenish queue — the return writes the object store and the
bindings, the deschedule writes a run queue and a current slot — so the whole
claim rests on the SM5.H migration's own `_other` frame, at exactly the pair
`replyDonationReturnReplenishCores` declares. -/
theorem applyReplyDonationOnCore_replenishQueueOnCore_ne (st st'' : SystemState)
    (rid : SeLe4n.ReplyId) (targetVtid : SeLe4n.ValidThreadId) (holderHome ownerHome c : CoreId)
    (hFrom : c ≠ holderHome) (hTo : c ≠ ownerHome)
    (h : applyReplyDonationOnCore st rid targetVtid holderHome ownerHome = .ok st'') :
    st''.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  rcases applyReplyDonationOnCore_ok_decompose st st'' rid targetVtid holderHome ownerHome h with
    ⟨_, hEq⟩ | ⟨scId, holderVtid, newOwner?, st', _, _, hRet, hEq⟩
  · rw [hEq]
  · rw [hEq, descheduleAtPlacement_replenishQueueOnCore,
      migrateSchedContextReplenishment_replenishQueueOnCore_other st' scId holderHome ownerHome
        c (Ne.symm hFrom) (Ne.symm hTo),
      returnDonatedSchedContext_scheduler_eq st st' holderVtid.val scId _ newOwner? hRet]

/-- WS-RR RR2.9 (frame): the cross-core donation return never advances the
machine timer — the return writes objects, the migration writes replenish-queue
slots, and the deschedule writes run-queue slots.

**WS-HP HP4.3**: re-keyed on the answered frame's head context, so the return's
*source* is the holder the trigger resolves and its *destination* is the answered
caller.  The frame statement is unchanged — which of the two threads the store
names does not change what the store leaves alone. -/
theorem applyReplyDonationOnCore_machine_eq
    (st st'' : SystemState) (rid : SeLe4n.ReplyId) (targetVtid : SeLe4n.ValidThreadId)
    (holderHome ownerHome : CoreId)
    (h : applyReplyDonationOnCore st rid targetVtid holderHome ownerHome = .ok st'') :
    st''.machine = st.machine := by
  rcases applyReplyDonationOnCore_ok_decompose st st'' rid targetVtid holderHome ownerHome h with ⟨_, hEq⟩ | ⟨scId, holderVtid, n, st', _, _, hRet, hEq⟩
  · rw [hEq]
  · rw [hEq]
    show (descheduleAtPlacement _ _).machine = _
    simp only [descheduleAtPlacement_machine_eq, migrateSchedContextReplenishment_machine]
    exact returnDonatedSchedContext_machine_eq st st' holderVtid.val scId
      (replyDonationRecipient st scId targetVtid.val) n hRet

/-- WS-RR RR2.9 (frame): the cross-core donation return commits exactly the
single-core return's object store — neither the migration nor the deschedule
writes an object.

**WS-HP HP4.3**: the `none` arm names the head-driven trigger
(`answeredFrameHeadContext?`) rather than the binding-driven resolver it
replaces, and the `some` arm's return is stated at the holder-as-source,
answered-caller-as-destination argument order the trigger produces. -/
theorem applyReplyDonationOnCore_objects_eq
    (st st'' : SystemState) (rid : SeLe4n.ReplyId) (targetVtid : SeLe4n.ValidThreadId)
    (holderHome ownerHome : CoreId)
    (h : applyReplyDonationOnCore st rid targetVtid holderHome ownerHome = .ok st'') :
    (replyFrameHeadHolder? st rid = none ∧ st''.objects = st.objects)
    ∨ ∃ (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
        (newOwner? : Option SeLe4n.ThreadId) (st' : SystemState),
        returnDonatedSchedContext st holder scId
          (replyDonationRecipient st scId targetVtid.val) newOwner? = .ok st' ∧
        st''.objects = st'.objects := by
  rcases applyReplyDonationOnCore_ok_decompose st st'' rid targetVtid holderHome ownerHome h with ⟨hNone, hEq⟩ | ⟨scId, holderVtid, n, st', _, _, hRet, hEq⟩
  · exact Or.inl ⟨hNone, by rw [hEq]⟩
  · refine Or.inr ⟨scId, holderVtid.val, n, st', hRet, ?_⟩
    rw [hEq, descheduleAtPlacement_preserves_objects,
      migrateSchedContextReplenishment_objects]

-- ============================================================================
-- §1b  WS-RR RR2.9 — the reply path preserves the SM5.H affinity invariant
-- ============================================================================

/-- WS-RR RR2.9 / WS-RR RR2.20: **the donation return plus its replenishment
migration restores replenish-queue affinity consistency on every core.**

The substance of both reply-side donation arms, factored out because two live
paths perform exactly this pair: `applyReplyDonationOnCore` (which follows it
with a deschedule) and `replyRecvPopDonation` (which does not, because the
recorded server may immediately rendezvous with a queued `Call` -- the
deschedule is `replyRecvPostReceiveDonation`'s, once the receive leg has said
whether anything did).

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
    (newOwner? : Option SeLe4n.ThreadId)
    (hRet : returnDonatedSchedContext st replier scId owner newOwner? = .ok st') :
    replenishQueueAffinityConsistent_smp
      (migrateSchedContextReplenishment st' scId replierHome ownerHome) := by
  -- The return's readings.
  have hSched : st'.scheduler = st.scheduler :=
    returnDonatedSchedContext_scheduler_eq st st' replier scId owner newOwner? hRet
  have hHomeEq : ∀ tid, determineTargetCore st' tid = determineTargetCore st tid := fun tid =>
    determineTargetCore_congr st st' tid
      (returnDonatedSchedContext_getTcb?_cpuAffinity_eq st st' replier scId owner
        hObjInv newOwner? hRet tid)
  have hScNe : ∀ scId', scId' ≠ scId → st'.getSchedContext? scId' = st.getSchedContext? scId' :=
    fun scId' hne => returnDonatedSchedContext_getSchedContext?_ne st st' replier
      scId scId' owner hne hObjInv newOwner? hRet
  obtain ⟨scPost, hScPost, hScPostBound⟩ :=
    returnDonatedSchedContext_post_boundThread st st' replier scId owner hObjInv newOwner? hRet
  obtain ⟨scPre, hScPre, hScPreBound⟩ :=
    returnDonatedSchedContext_ok_implies_sc_bound st st' replier scId owner newOwner? hRet
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
`descheduleAtPlacement` writes a run queue and a current slot, never a replenish
queue and never an object — at either of its branches, which is why both frames
are proved at the step rather than per core here.

**WS-HP HP4.3 — the two home hypotheses swap conditionality, and that is the
whole content of the re-keying here.**  Under the binding-driven trigger the
*source* of the context was the operation's own argument (the recorded server),
so its home was an unconditional equation, while the *destination* came out of
the resolver and had to be stated under it.  Under the head-driven trigger the
argument is the answered caller, which is the **destination**; the source is the
holder the trigger resolves.  So `hOwnerHome` is now unconditional and
`hHolderHome` is the one quantified over the trigger's answer.  Getting this
backwards would not fail to elaborate — both shapes typecheck — it would migrate
the replenishments in the wrong direction, which is why the migration's source
and destination are threaded through the shared lemma rather than re-derived. -/
theorem applyReplyDonationOnCore_preserves_replenishQueueAffinityConsistent_smp
    (st st'' : SystemState) (rid : SeLe4n.ReplyId) (targetVtid : SeLe4n.ValidThreadId)
    (holderHome ownerHome : CoreId)
    (hObjInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st)
    (hHolderHome : ∀ scId holder,
        replyFrameHeadHolder? st rid = some (scId, holder) →
        determineTargetCore st holder = holderHome)
    -- **WS-HP HP10.7**: the destination is the REDIRECTED recipient, so this
    -- hypothesis is quantified over the trigger's answer exactly as `hHolderHome`
    -- is.  HP4.3 recorded that the two swapped conditionality; the redirect makes
    -- both conditional, because the thread that gains the reservation is no longer
    -- the operation's own argument.  Stating it at `targetVtid.val` would still
    -- typecheck and would migrate the replenishments to the answered caller's core
    -- while the reservation settled on the origin's -- the wrong direction, which
    -- is the hazard this docstring already warns about one argument over.
    (hOwnerHome : ∀ scId holder,
        replyFrameHeadHolder? st rid = some (scId, holder) →
        determineTargetCore st (replyDonationRecipient st scId targetVtid.val) = ownerHome)
    (h : applyReplyDonationOnCore st rid targetVtid holderHome ownerHome = .ok st'') :
    replenishQueueAffinityConsistent_smp st'' := by
  rcases applyReplyDonationOnCore_ok_decompose st st'' rid targetVtid holderHome ownerHome h with ⟨_, hEq⟩ | ⟨scId, holderVtid, n, st', hRes, _, hRet, hEq⟩
  · rw [hEq]; exact hCons
  · rw [hEq]
    -- The deschedule is a frame for the invariant; the substance is the migration.
    intro c
    exact (replenishQueueAffinityConsistentOnCore_frame
        (descheduleAtPlacement_replenishQueueOnCore _ _ _)
        (descheduleAtPlacement_preserves_objects _ _)).mpr
      (returnDonatedSchedContext_migrate_preserves_replenishQueueAffinityConsistent_smp
        st st' holderVtid.val scId (replyDonationRecipient st scId targetVtid.val)
        holderHome ownerHome hObjInv hCons
        (hHolderHome scId holderVtid.val hRes) (hOwnerHome scId holderVtid.val hRes) n hRet c)

-- ============================================================================
-- §2  SM6.C.3 — Donation-chain lock-set extension
-- ============================================================================

/-- WS-SM SM6.C.3 (plan §4.3): the cross-core donation-chain lock-set extension
for reply.  When the reply returns a SchedContext to its original owner, the
`endpointReply` lock-set is the non-returning lock-set extended with the returned
SchedContext's **write** lock and the original owner's TCB **write** lock — so the
SC migration (`returnDonatedSchedContextValid` rebinding `boundThread` across
cores, SM5.H.4) and the owner's re-activation both run under held write locks,
serialised against every other core.

**WS-OD OD3.5: and the state-level lock**, a third member, for the reason its
`.call` counterpart records — `returnDonatedSchedContext` ends in
`scThreadIndexAdd`/`scThreadIndexRemove` on `SystemState.scThreadIndex`, an
`RHTable` whose insert may rehash and back-shift the whole table.  The word
"exactly" left this docstring with it: the extension is three members, and the
state-level one was written by the operation and named by no lock.

**WS-OD OD3.7**: the reply object and the two below-head reads are pinned at
`none` on *both* sides, and explicitly rather than by a default.  **WS-OD
(`v0.35.4`) / WS-RM (`v0.35.6`) / WS-HP HP10.6**: so are the head the pop clears,
the frame above the answered reply and the origin a bottom-of-stack pop redirects
to, for the same reason.  This equation
characterises what the *donation* adds, and `lockSetExtendOpt` is an insertion —
it does not commute — so the donation's two members cannot be lifted over
members added after them.  Stating it on the chain-free, reply-object-free shape
is therefore the general form this equation has; the members it holds fixed were
already fixed before, silently, by `replyId`'s default. -/
theorem lockSet_endpointReply_donation_extension
    (replier : SeLe4n.ThreadId) (cnRoot : SeLe4n.ObjId) (target : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId) :
    lockSet_endpointReply replier cnRoot target (some scId) (some originalOwner)
        none none none none none none none
      = lockSetExtendOpt
          (lockSetExtendOpt
            (lockSetExtendOpt
              (lockSet_endpointReply replier cnRoot target none none none none none none none
                none none)
              (some (schedContextLock scId, .write)))
            (some (tcbLock originalOwner, .write)))
          (some (stateLevelLock, .write)) := by
  unfold lockSet_endpointReply
  rfl

-- ============================================================================
-- §3  SM6.C — Full cross-core `.reply` dispatch (reply + donation + PIP revert)
-- ============================================================================

/-- WS-SM SM6.C (operation): the cross-core `Reply` **delivery + scheduling**
primitive — below the API layer.  The cross-core reply (`endpointReplyOnCore` —
caller woken on its home core), then the SchedContext donation **return**
(`applyReplyDonationOnCore` — the passive **recorded server** returns the donated
SC and is descheduled *at its placement*), then the cross-core priority-inheritance
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
          -- **WS-HP HP4.4**: this shim no longer feeds the pop -- it is retained
          -- as the *recorded server's* validation, which is the fact the
          -- priority-inheritance reversion below walks from.  A sentinel
          -- `expected` is a malformed `blockedOnReply` link and this arm has
          -- refused it since SM6.C; dropping the shim with the pop would have
          -- widened the accepted set as a side effect of a re-keying, which is
          -- not what a refactor cut may do.
          match SeLe4n.ThreadId.toValid? expected with
          | some _expectedV =>
              -- `v0.35.37`: the deschedule's core is **not passed** — the step
              -- resolves the recorded server's own *placement*
              -- (`descheduleAtPlacement`).  SM6.D passed `determineExecutingCore
              -- st expected` here, which was already a correction (reusing the
              -- delegate's syscall core points at the wrong run queue outright)
              -- and was still a **proxy**: that resolver finds a core the thread
              -- is *current* on and otherwise answers `bootCoreId`, so a recorded
              -- server that is queued rather than running — preempted by its own
              -- core's tick — had its deschedule land on a core it is not on, and
              -- the step did nothing at all.  The server is `.unbound` by then, so
              -- it would be re-selected on its own core at its legacy TCB priority
              -- and run charged to no reservation.  `placedCoreOf?` is the fact;
              -- `determineExecutingCore` was a stand-in for it.
              --
              -- The core is not a parameter any more either, which is the point:
              -- a parameter is a place for a caller to be wrong, and this step
              -- resolves the thread it deschedules from the state already.
              -- WS-RR RR2.12: the live `.reply` arm now routes through the
              -- **migrating** donation return.  Both migration endpoints are
              -- resolved at the state the pop runs on (`st1`), which is what
              -- makes the affinity theorem's two home hypotheses hold by
              -- definition rather than by a transport lemma; the `withLockSet`
              -- bracket's pre-state reading of the same two
              -- (`endpointReplyCrossCoreDispatchSchedLockSet`) agrees, because
              -- `endpointReplyOnCore` writes `ipcState` / queue links / the Reply
              -- object and never a `schedContextBinding` or a `cpuAffinity`.
              -- When the answered frame heads no context there is nothing to move
              -- and the endpoints coincide, making the migration a definitional
              -- no-op.
              --
              -- **WS-HP HP4.4: the pop is keyed on the answered FRAME and the
              -- answered CALLER, and the frame is resolved on the pre-state.**
              -- `endpointReplyOnCore`'s `consumeCallerReply` has just cleared
              -- `target.replyObject`, so `st1` no longer knows which frame this
              -- reply answered -- `answeredReplyObject? st target` is the one
              -- expression that does, and it is the same one the arm's footprint
              -- members come from, so the declared footprint and the executed pop
              -- cannot name different frames.  Everything the pop *decides* --
              -- which context the frame heads, which thread holds it, which
              -- caller is outer -- is read from `st1`.
              --
              -- `expected` is still what the priority-inheritance reversion walks
              -- from, and deliberately: PIP keys on waiters
              -- (`TCB.blockingServer?`), not on donations, so the chain starts at
              -- the recorded server whatever the pop decided.
              match answeredReplyObject? st target with
              | none =>
                  -- No answered frame: nothing heads a context through it, so the
                  -- pop is the identity and only the reversion runs.
                  ((PriorityInheritance.propagatePipChainCrossCore st1 expected executingCore).1,
                    .ok replySgi?)
              | some rid =>
                match SeLe4n.ThreadId.toValid? target with
                | none => (st, .error .invalidArgument)
                | some targetV =>
                  -- **WS-HP HP10.7**: the migration's DESTINATION is the
                  -- redirected recipient's home, not the answered caller's --
                  -- they differ exactly on the out-of-order removal this phase
                  -- exists for, and passing the caller's there would move the
                  -- replenish queue to a core the reservation does not live on.
                  match applyReplyDonationOnCore st1 rid targetV
                      (replyDonationHolderHome st1 rid target)
                      (replyDonationRecipientHome st1 rid target) with
                  | .error e => (st, .error e)
                  | .ok st2 =>
                      ((PriorityInheritance.propagatePipChainCrossCore st2 expected executingCore).1, .ok replySgi?)
          | none => (st, .error .invalidArgument)
      | none => (st, .error .replyCapInvalid)

/-- **PR #895 review round 22: the live `.reply` spine does not depend on the
reply-cap HOLDER.**

Every use of `replier` above is the one passed to `endpointReplyOnCore`, whose
own parameter is `_replier`: the 6J-lYm gate removal made authority the presented
reply capability, so the leg reads the caller's recorded server from the state
and the cap holder's identity nowhere.  The donation return and the
priority-inheritance reversion are then keyed on that recorded server
(`recordedReplyServer? st target`), which is resolved from the pre-state and is
therefore the same thread whichever delegate invoked.

So a *delegated* reply gets exactly the non-delegated behaviour, and that is the
property that makes this dispatch — rather than the superseded single-core
`endpointReplyWithDonation` — the right live counterpart for a frozen mirror that
accepts a delegated replier.  Its pair is
`endpointReplyWithDonation_refuses_delegated_replier`
(`IPC/Operations/Donation.lean`), which has the content: the two live composites
answer one question two ways, so a coverage claim naming one is not a claim about
the other.  Neither theorem alone says that; stated together they do. -/
theorem endpointReplyCrossCoreDispatch_independent_of_replier
    (replier replier' target : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState) :
    endpointReplyCrossCoreDispatch replier target msg executingCore st =
      endpointReplyCrossCoreDispatch replier' target msg executingCore st := rfl

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

-- ============================================================================
-- §6  WS-RR RR8.12 Cut C3a — the live `.reply` dispatch's per-core write set and
--     its scheduler-domain footprint
-- ============================================================================
--
-- `lockSet_endpointReply` is an object-domain `LockSet` and cannot name a per-core
-- run-queue or replenish-queue slot at all, so
-- `UncoveredLockDomain.syscallSeamSchedulerDomain` recorded the live `.reply` arm's
-- scheduler writes as outside the footprint the RR7.12 seam acquired (that entry is
-- retired at Cut C6h, `v0.35.181`).  This
-- section declares the DISPATCH's: the arm's SM8.B write set (relocated here from
-- the staged `InformationFlow/NonInterferenceCrossCore.lean`, whose confinement
-- theorem `endpointReplyCrossCoreDispatch_confinedToCores` is stated at it and
-- stays there) as the run segment, and the donation return's own two cores as the
-- replenish segment.  The ARM the API runs is `replyTransferOnCore` — seL4's
-- `doReplyTransfer` branch, one module up in `IPC/CrossCore/Fault.lean` — and its
-- footprint is declared there, over this one at the message each branch hands the
-- dispatch.  Inert until the bracket cut wires `schedLockSetForSyscall`.

/-- SM8.B.2: **the cores the live cross-core `.reply` may write**, recovered from
the pre-state by mirroring `endpointReplyCrossCoreDispatch`'s own control flow —
same recorded-server resolution, same server-core resolution, same donation
return — so the walk is keyed where the dispatch keys it: on the *recorded
server* at the *post-donation* state.

Three legs on the success path: the answered caller's home core, the recorded
server's own core, and the reverted chain's home cores. Every arm on which the
dispatch fails closed returns `[]`, which is exact — those arms return the
pre-state unchanged.

Relocated to production at **WS-RR RR8.12 Cut C3a**, beside the dispatch it mirrors,
so the scheduler-domain footprint `schedLockSet_endpointReplyOnCore` can read it; its
confinement theorem stays in `InformationFlow/NonInterferenceCrossCore.lean`, because
`observableSlotsConfinedToCores` is that module's predicate. -/
def endpointReplyDispatchWriteSet (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState) : List CoreId :=
  match endpointReplyOnCore replier target msg executingCore st with
  | (_, .error _) => []
  | (st1, .ok _) =>
      match recordedReplyServer? st target with
      | some expected =>
          match SeLe4n.ThreadId.toValid? expected with
          | some _expectedV =>
              -- **WS-HP HP4.4**: the mirror follows the dispatch onto the answered
              -- frame and the answered caller, including the arm where there is no
              -- frame to pop and only the reply leg and the chain walk run.
              match answeredReplyObject? st target with
              | none =>
                  ([determineTargetCore st target]
                    ++ pipChainWriteSet st1 expected executingCore st1.objectIndex.length)
              | some rid =>
                match SeLe4n.ThreadId.toValid? target with
                | none => []
                | some targetV =>
                  -- **WS-HP HP10.7**: the destination home is the redirected
                  -- recipient's, as the live dispatch passes it -- the write set
                  -- mirrors the dispatch's control flow, so it has to mirror the
                  -- same resolver or the two name different cores.
                  match applyReplyDonationOnCore st1 rid targetV
                      (replyDonationHolderHome st1 rid target)
                      (replyDonationRecipientHome st1 rid target) with
                  | .error _ => []
                  | .ok st2 =>
                      -- `v0.35.37`: the donation return's leg is the descheduled
                      -- thread's **placement**, read off the same resolver the step
                      -- uses, so the write set and the transition cannot name
                      -- different cores.  It was `determineExecutingCore st
                      -- expected`, which answers `bootCoreId` for a queued server —
                      -- a core the step does not write and, worse, one it would have
                      -- written had the proxy been the fact.  It is resolved at
                      -- `st1` because that is the state the donation return runs on,
                      -- and through the trigger because the thread it deschedules is
                      -- the trigger's holder.
                      ([determineTargetCore st target]
                        ++ replyDonationDescheduleCores st1 rid
                        ++ pipChainWriteSet st2 expected executingCore
                             st2.objectIndex.length)
          | none => []
      | none => []

/-- **WS-RR RR8.12 Cut C3a**: the replenish-queue cores the live `.reply` dispatch's
donation return migrates between, recovered from the pre-state by mirroring
`endpointReplyCrossCoreDispatch`'s own control flow exactly as
`endpointReplyDispatchWriteSet` does — the same reply leg, the same recorded-server
validation, the same answered frame, the same `toValid?`, the same return — and
then the return's own pair at the reply leg's post-state
(`replyDonationReturnReplenishCores st1 rid target`), which is the state the pop
runs on and reads its trigger at.  Every arm on which the dispatch migrates nothing
returns `[]`: a failed leg, no recorded server, a server or target that does not
validate, no answered frame, a return that refuses, and a frame that heads no
context.

Why the return's own state and not the syscall's pre-state: WS-HP HP4 keys the pop
on the frame at the state the pop runs on, and the recipient it redirects to
(`replyDonationRecipient`) is decided there too — reading either at the pre-state
is the footprint/transition asymmetry WS-HP HP10.8 registered for the
object-domain origin member.  Re-running the leg is what makes this footprint's
resolution and the transition's one computation, which is the discipline Cut C2
set for `.replyRecv`. -/
def endpointReplyDispatchReplenishCores (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState) : List CoreId :=
  match endpointReplyOnCore replier target msg executingCore st with
  | (_, .error _) => []
  | (st1, .ok _) =>
      match recordedReplyServer? st target with
      | some expected =>
          match SeLe4n.ThreadId.toValid? expected with
          | some _ =>
              match answeredReplyObject? st target with
              | none => []
              | some rid =>
                match SeLe4n.ThreadId.toValid? target with
                | none => []
                | some targetV =>
                  match applyReplyDonationOnCore st1 rid targetV
                      (replyDonationHolderHome st1 rid target)
                      (replyDonationRecipientHome st1 rid target) with
                  | .error _ => []
                  | .ok _ => replyDonationReturnReplenishCores st1 rid target
          | none => []
      | none => []

/-- The segment once the dispatch has reached its return: the return's own pair at
the reply leg's post-state.  The one unfolding every consumer reads. -/
theorem endpointReplyDispatchReplenishCores_eq_of_return (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage) (executingCore : CoreId) (st st1 st2 : SystemState)
    (sgi : Option (CoreId × SgiKind)) (expected : SeLe4n.ThreadId)
    (expectedV : SeLe4n.ValidThreadId) (rid : SeLe4n.ReplyId)
    (targetV : SeLe4n.ValidThreadId)
    (hReply : endpointReplyOnCore replier target msg executingCore st = (st1, .ok sgi))
    (hSrv : recordedReplyServer? st target = some expected)
    (hEV : SeLe4n.ThreadId.toValid? expected = some expectedV)
    (hRid : answeredReplyObject? st target = some rid)
    (hTV : SeLe4n.ThreadId.toValid? target = some targetV)
    (hRet : applyReplyDonationOnCore st1 rid targetV (replyDonationHolderHome st1 rid target)
      (replyDonationRecipientHome st1 rid target) = .ok st2) :
    endpointReplyDispatchReplenishCores replier target msg executingCore st
      = replyDonationReturnReplenishCores st1 rid target := by
  unfold endpointReplyDispatchReplenishCores
  simp only [hReply, hSrv, hEV, hRid, hTV, hRet]

/-- Where the answered frame heads no context — no frame at all, or a frame with
no `.head` link at the state the pop reads it — the segment is empty on every arm,
whatever the dispatch's other readings answered. -/
theorem endpointReplyDispatchReplenishCores_of_no_head (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage) (executingCore : CoreId) (st st1 : SystemState)
    (sgi : Option (CoreId × SgiKind))
    (hReply : endpointReplyOnCore replier target msg executingCore st = (st1, .ok sgi))
    (hNoHead : ∀ rid, answeredReplyObject? st target = some rid →
      replyFrameHeadHolder? st1 rid = none) :
    endpointReplyDispatchReplenishCores replier target msg executingCore st = [] := by
  unfold endpointReplyDispatchReplenishCores
  simp only [hReply]
  cases hSrv : recordedReplyServer? st target with
  | none => rfl
  | some expected =>
    simp only []
    cases hEV : SeLe4n.ThreadId.toValid? expected with
    | none => rfl
    | some _ =>
      simp only []
      cases hRid : answeredReplyObject? st target with
      | none => rfl
      | some rid =>
        simp only []
        cases hTV : SeLe4n.ThreadId.toValid? target with
        | none => rfl
        | some targetV =>
          simp only []
          cases hRet : applyReplyDonationOnCore st1 rid targetV
              (replyDonationHolderHome st1 rid target)
              (replyDonationRecipientHome st1 rid target) with
          | error e => rfl
          | ok st2 =>
            simp only []
            exact replyDonationReturnReplenishCores_of_no_head st1 rid target (hNoHead rid hRid)

/-- **WS-RR RR8.12 Cut C3a**: the scheduler-domain footprint of the live `.reply`
dispatch — the object-store table write lock, the run-queue write locks of every
core the dispatch writes (the answered caller's home, the holder's placement when
the pop deschedules it, and the home of each priority-inheritance chain member the
reversion re-buckets), and the replenish-queue write locks of the two cores the
donation return migrates between.

**Every core is derived; nothing is a parameter.**  The run segment is
`endpointReplyDispatchWriteSet`, the arm's own SM8.B write set, which
`endpointReplyCrossCoreDispatch_confinedToCores` is stated at — so the footprint and
the confinement claim cannot name different cores (Cut 7's rule).  The replenish
segment is `endpointReplyDispatchReplenishCores`, the return's own pair by
construction.  Both mirror the dispatch's own control flow.

**The chain walk is in the run segment, not left to the dynamic extension.**
`endpointReplyDispatchWriteSet` appends `pipChainWriteSet` at the post-return state
the reversion really starts from, so every run queue it re-buckets is a static
member here; what `pipChainStart_endpointReply`'s dynamic walker still adds is the
object domain's per-member TCB write lock.  The RR2.10 parametric
`endpointReplyCrossCoreDispatchSchedLockSet` is the shape this refines, and this
footprint deliberately does **not** cover it member for member: that form declares
the executing core's run queue on a justification that is false — the reversion
re-buckets each member on its *home* core, and nothing in the dispatch writes the
replier's own core — so the parametric member is a sound over-declaration this
derived form drops.  What the parametric shape declares *correctly* — the
donation-return footprint at the resolved cores — this one covers
(`…_covers_donation`), and that is the relation the RR2.10 lemmas rest on. -/
def schedLockSet_endpointReplyOnCore (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState) :
    List (SchedLockId × Concurrency.AccessMode) :=
  schedFootprintOfCores (endpointReplyDispatchWriteSet replier target msg executingCore st)
    (endpointReplyDispatchReplenishCores replier target msg executingCore st)

-- No `_write_only` / `_pairwise_le` restatement here, and that is deliberate: both
-- are `schedFootprintOfCores_write_only` / `_pairwise_le` applied to this
-- footprint's own arguments, so a consumer reaches for the shared lemma directly.

/-- **WS-RR RR8.12 Cut C3a**: whenever the dispatch commits, the answered caller's
home core is a run-queue write member — it is the head of the arm's own write set
on both committing arms, since the reply leg wakes the caller there. -/
theorem schedLockSet_endpointReplyOnCore_contains_target_runQueue_write
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st st' : SystemState) (sgi : Option (CoreId × SgiKind))
    (hDisp : endpointReplyCrossCoreDispatch replier target msg executingCore st
      = (st', .ok sgi)) :
    (SchedLockId.runQueue ⟨determineTargetCore st target⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_endpointReplyOnCore replier target msg executingCore st := by
  refine (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr ?_
  unfold endpointReplyCrossCoreDispatch at hDisp
  unfold endpointReplyDispatchWriteSet
  cases hRep : endpointReplyOnCore replier target msg executingCore st with
  | mk st1 res =>
    rw [hRep] at hDisp
    cases res with
    | error e => simp at hDisp
    | ok replySgi? =>
      simp only [] at hDisp ⊢
      cases hSrv : recordedReplyServer? st target with
      | none => rw [hSrv] at hDisp; simp at hDisp
      | some expected =>
        rw [hSrv] at hDisp
        simp only [] at hDisp ⊢
        cases hEV : SeLe4n.ThreadId.toValid? expected with
        | none => rw [hEV] at hDisp; simp at hDisp
        | some _ =>
          rw [hEV] at hDisp
          simp only [] at hDisp ⊢
          cases hRid : answeredReplyObject? st target with
          | none => simp
          | some rid =>
            rw [hRid] at hDisp
            simp only [] at hDisp ⊢
            cases hTV : SeLe4n.ThreadId.toValid? target with
            | none => rw [hTV] at hDisp; simp at hDisp
            | some targetV =>
              rw [hTV] at hDisp
              simp only [] at hDisp ⊢
              cases hRet : applyReplyDonationOnCore st1 rid targetV
                  (replyDonationHolderHome st1 rid target)
                  (replyDonationRecipientHome st1 rid target) with
              | error e => rw [hRet] at hDisp; simp at hDisp
              | ok st2 => simp

/-- **WS-RR RR8.12 Cut C3a (coverage, the deschedule)**: on the returning arm the
footprint names the run-queue write lock of every core the pop's deschedule may
write — `replyDonationDescheduleCores`, the holder's placement at the reply leg's
post-state, read through the same trigger the step deschedules through. -/
theorem schedLockSet_endpointReplyOnCore_covers_deschedule (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage) (executingCore : CoreId) (st st1 st2 : SystemState)
    (sgi : Option (CoreId × SgiKind)) (expected : SeLe4n.ThreadId)
    (expectedV : SeLe4n.ValidThreadId) (rid : SeLe4n.ReplyId)
    (targetV : SeLe4n.ValidThreadId) (c : CoreId)
    (hReply : endpointReplyOnCore replier target msg executingCore st = (st1, .ok sgi))
    (hSrv : recordedReplyServer? st target = some expected)
    (hEV : SeLe4n.ThreadId.toValid? expected = some expectedV)
    (hRid : answeredReplyObject? st target = some rid)
    (hTV : SeLe4n.ThreadId.toValid? target = some targetV)
    (hRet : applyReplyDonationOnCore st1 rid targetV (replyDonationHolderHome st1 rid target)
      (replyDonationRecipientHome st1 rid target) = .ok st2)
    (hPlaced : c ∈ replyDonationDescheduleCores st1 rid) :
    (SchedLockId.runQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_endpointReplyOnCore replier target msg executingCore st := by
  refine (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr ?_
  unfold endpointReplyDispatchWriteSet
  simp only [hReply, hSrv, hEV, hRid, hTV, hRet]
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  exact Or.inl (Or.inr hPlaced)

/-- **WS-RR RR8.12 Cut C3a (coverage, the migration)**: on the returning arm whose
frame heads a context, the footprint covers `migrateSchedContextReplenishmentLockSet`
member for member — at the two cores the dispatch hands the return, which are the
two the segment names (`applyReplyDonationOnCore_ok_migrates` is the licence that
they are the migration's own endpoints).  Stated without a placement, because the
migration happens whether or not the holder sits on a core. -/
theorem schedLockSet_endpointReplyOnCore_covers_migration (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage) (executingCore : CoreId) (st st1 st2 : SystemState)
    (sgi : Option (CoreId × SgiKind)) (expected : SeLe4n.ThreadId)
    (expectedV : SeLe4n.ValidThreadId) (rid : SeLe4n.ReplyId)
    (targetV : SeLe4n.ValidThreadId) (scId : SeLe4n.SchedContextId)
    (holder : SeLe4n.ThreadId)
    (hReply : endpointReplyOnCore replier target msg executingCore st = (st1, .ok sgi))
    (hSrv : recordedReplyServer? st target = some expected)
    (hEV : SeLe4n.ThreadId.toValid? expected = some expectedV)
    (hRid : answeredReplyObject? st target = some rid)
    (hTV : SeLe4n.ThreadId.toValid? target = some targetV)
    (hRet : applyReplyDonationOnCore st1 rid targetV (replyDonationHolderHome st1 rid target)
      (replyDonationRecipientHome st1 rid target) = .ok st2)
    (hHead : replyFrameHeadHolder? st1 rid = some (scId, holder)) :
    ∀ p ∈ migrateSchedContextReplenishmentLockSet (replyDonationHolderHome st1 rid target)
             (replyDonationRecipientHome st1 rid target),
      p ∈ schedLockSet_endpointReplyOnCore replier target msg executingCore st := by
  intro p hp
  simp only [migrateSchedContextReplenishmentLockSet, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  have hSeg := endpointReplyDispatchReplenishCores_eq_of_return replier target msg executingCore
    st st1 st2 sgi expected expectedV rid targetV hReply hSrv hEV hRid hTV hRet
  have hPair : replyDonationReturnReplenishCores st1 rid target
      = [replyDonationHolderHome st1 rid target, replyDonationRecipientHome st1 rid target] := by
    unfold replyDonationReturnReplenishCores; rw [hHead]
  rcases hp with h | h <;> subst h <;>
  · refine (mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mpr ?_
    rw [hSeg, hPair]
    simp

/-- **WS-RR RR8.12 Cut C3a (coverage, the RR2.10 shape)**: with the holder placed
on a core, the footprint covers the RR2.10 donation-return footprint
`applyReplyDonationOnCoreSchedLockSet` at the resolved cores member for member —
the deschedule's run-queue lock and the migration's two replenish-queue locks —
which is the relation `endpointReplyCrossCoreDispatchSchedLockSet_covers_donation`
states for the parametric form. -/
theorem schedLockSet_endpointReplyOnCore_covers_donation (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage) (executingCore : CoreId) (st st1 st2 : SystemState)
    (sgi : Option (CoreId × SgiKind)) (expected : SeLe4n.ThreadId)
    (expectedV : SeLe4n.ValidThreadId) (rid : SeLe4n.ReplyId)
    (targetV : SeLe4n.ValidThreadId) (scId : SeLe4n.SchedContextId)
    (holder : SeLe4n.ThreadId) (c : CoreId)
    (hReply : endpointReplyOnCore replier target msg executingCore st = (st1, .ok sgi))
    (hSrv : recordedReplyServer? st target = some expected)
    (hEV : SeLe4n.ThreadId.toValid? expected = some expectedV)
    (hRid : answeredReplyObject? st target = some rid)
    (hTV : SeLe4n.ThreadId.toValid? target = some targetV)
    (hRet : applyReplyDonationOnCore st1 rid targetV (replyDonationHolderHome st1 rid target)
      (replyDonationRecipientHome st1 rid target) = .ok st2)
    (hHead : replyFrameHeadHolder? st1 rid = some (scId, holder))
    (hPlaced : c ∈ replyDonationDescheduleCores st1 rid) :
    ∀ p ∈ applyReplyDonationOnCoreSchedLockSet c (replyDonationHolderHome st1 rid target)
             (replyDonationRecipientHome st1 rid target),
      p ∈ schedLockSet_endpointReplyOnCore replier target msg executingCore st := by
  have hSeg := endpointReplyDispatchReplenishCores_eq_of_return replier target msg executingCore
    st st1 st2 sgi expected expectedV rid targetV hReply hSrv hEV hRid hTV hRet
  have hPair : replyDonationReturnReplenishCores st1 rid target
      = [replyDonationHolderHome st1 rid target, replyDonationRecipientHome st1 rid target] := by
    unfold replyDonationReturnReplenishCores; rw [hHead]
  unfold applyReplyDonationOnCoreSchedLockSet schedLockSet_endpointReplyOnCore
  rw [hSeg, hPair]
  refine schedFootprintOfCores_subset (fun c' hc' => ?_) (fun _ h => h)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
  subst hc'
  unfold endpointReplyDispatchWriteSet
  simp only [hReply, hSrv, hEV, hRid, hTV, hRet]
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  exact Or.inl (Or.inr hPlaced)

/-- **WS-RR RR8.12 Cut C3a (the empty segment, footprint side)**: where the
answered frame heads no context the footprint names no replenish-queue lock —
over-declaring is sound and not free (SM8.D's CC-5), and
`endpointReplyCrossCoreDispatch_replenishQueueOnCore_of_no_head` is the licence that
the transition writes none there either. -/
theorem schedLockSet_endpointReplyOnCore_no_replenishQueue_of_no_head
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st st1 : SystemState) (sgi : Option (CoreId × SgiKind))
    (hReply : endpointReplyOnCore replier target msg executingCore st = (st1, .ok sgi))
    (hNoHead : ∀ rid, answeredReplyObject? st target = some rid →
      replyFrameHeadHolder? st1 rid = none) (c : CoreId) :
    (SchedLockId.replenishQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∉ schedLockSet_endpointReplyOnCore replier target msg executingCore st := by
  intro hMem
  have := (mem_schedFootprintOfCores_replenishQueue_iff _ _ c).mp hMem
  rw [endpointReplyDispatchReplenishCores_of_no_head replier target msg executingCore st st1 sgi
    hReply hNoHead] at this
  simp at this

/-- **WS-RR RR8.12 Cut C3a (the empty segment, transition side)**: and where the
answered frame heads no context the live dispatch writes no replenish queue — the
reply leg never does (`endpointReplyOnCore_replenishQueueOnCore`), the return is
the identity there (`applyReplyDonationOnCore_replenishQueueOnCore_of_no_head`), and
the reversion re-buckets run queues alone
(`propagatePipChainCrossCore_replenishQueueOnCore`).  The refusal arms commit
nothing.  So the empty segment is exact, not merely narrow. -/
theorem endpointReplyCrossCoreDispatch_replenishQueueOnCore_of_no_head
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st st1 stDisp : SystemState) (sgi : Option (CoreId × SgiKind))
    (res : Except KernelError (Option (CoreId × SgiKind)))
    (hReply : endpointReplyOnCore replier target msg executingCore st = (st1, .ok sgi))
    (hNoHead : ∀ rid, answeredReplyObject? st target = some rid →
      replyFrameHeadHolder? st1 rid = none)
    (hDisp : endpointReplyCrossCoreDispatch replier target msg executingCore st = (stDisp, res))
    (c : CoreId) :
    stDisp.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  have hLeg : st1.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
    have h := endpointReplyOnCore_replenishQueueOnCore replier target msg executingCore st c
    rw [hReply] at h
    exact h
  unfold endpointReplyCrossCoreDispatch at hDisp
  simp only [hReply] at hDisp
  cases hSrv : recordedReplyServer? st target with
  | none =>
    rw [hSrv] at hDisp; simp only [] at hDisp
    rw [← (Prod.mk.inj hDisp).1]
  | some expected =>
    rw [hSrv] at hDisp; simp only [] at hDisp
    cases hEV : SeLe4n.ThreadId.toValid? expected with
    | none =>
      rw [hEV] at hDisp; simp only [] at hDisp
      rw [← (Prod.mk.inj hDisp).1]
    | some _ =>
      rw [hEV] at hDisp; simp only [] at hDisp
      cases hRid : answeredReplyObject? st target with
      | none =>
        rw [hRid] at hDisp; simp only [] at hDisp
        rw [← (Prod.mk.inj hDisp).1,
          PriorityInheritance.propagatePipChainCrossCore_replenishQueueOnCore]
        exact hLeg
      | some rid =>
        rw [hRid] at hDisp; simp only [] at hDisp
        cases hTV : SeLe4n.ThreadId.toValid? target with
        | none =>
          rw [hTV] at hDisp; simp only [] at hDisp
          rw [← (Prod.mk.inj hDisp).1]
        | some targetV =>
          rw [hTV] at hDisp; simp only [] at hDisp
          cases hRet : applyReplyDonationOnCore st1 rid targetV
              (replyDonationHolderHome st1 rid target)
              (replyDonationRecipientHome st1 rid target) with
          | error e =>
            rw [hRet] at hDisp; simp only [] at hDisp
            rw [← (Prod.mk.inj hDisp).1]
          | ok st2 =>
            rw [hRet] at hDisp; simp only [] at hDisp
            rw [← (Prod.mk.inj hDisp).1,
              PriorityInheritance.propagatePipChainCrossCore_replenishQueueOnCore,
              applyReplyDonationOnCore_replenishQueueOnCore_of_no_head st1 st2 rid targetV _ _
                (hNoHead rid hRid) hRet c]
            exact hLeg

/-- **WS-RR RR8.12 Cut C6c: the `.reply` dispatch's exactness frame.**

Keyed on the footprint's own replenish segment.  The dispatch's branch structure
and `endpointReplyDispatchReplenishCores`' are the same structure by construction
(Cut C3a), so one case split visits both: every arm short of a resolving donation
return leaves the segment empty and the reply leg's own frame applies, and the
resolving arm is the pop's `_ne` frame at exactly the pair the segment names. -/
theorem endpointReplyCrossCoreDispatch_replenishQueueOnCore_ne
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (c : CoreId)
    (hne : c ∉ endpointReplyDispatchReplenishCores replier target msg executingCore st) :
    (endpointReplyCrossCoreDispatch replier target msg executingCore
          st).1.scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
  unfold endpointReplyCrossCoreDispatch endpointReplyDispatchReplenishCores at *
  cases hLeg : endpointReplyOnCore replier target msg executingCore st with
  | mk st1 res =>
    rw [hLeg] at hne
    have hFrame : st1.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
      have h0 := endpointReplyOnCore_replenishQueueOnCore replier target msg executingCore st c
      rw [hLeg] at h0
      exact h0
    cases res with
    | error e => rfl
    | ok replySgi? =>
      simp only at hne ⊢
      split
      · rename_i expected hExp
        rw [hExp] at hne
        simp only at hne
        split
        · rename_i expectedV hEv
          rw [hEv] at hne
          simp only at hne
          split
          · simp only [PriorityInheritance.propagatePipChainCrossCore_replenishQueueOnCore]
            exact hFrame
          · rename_i rid hRid
            rw [hRid] at hne
            simp only at hne
            split
            · rfl
            · rename_i targetV hTv
              rw [hTv] at hne
              simp only at hne
              split
              · rfl
              · rename_i st2 hDon
                rw [hDon] at hne
                simp only at hne
                simp only [PriorityInheritance.propagatePipChainCrossCore_replenishQueueOnCore]
                unfold replyDonationReturnReplenishCores at hne
                cases hHead : replyFrameHeadHolder? st1 rid with
                | none =>
                    rw [applyReplyDonationOnCore_replenishQueueOnCore_of_no_head st1 st2 rid
                      targetV (replyDonationHolderHome st1 rid target)
                      (replyDonationRecipientHome st1 rid target) hHead hDon c]
                    exact hFrame
                | some pair =>
                    rw [hHead] at hne
                    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hne
                    rw [applyReplyDonationOnCore_replenishQueueOnCore_ne st1 st2 rid targetV
                      (replyDonationHolderHome st1 rid target)
                      (replyDonationRecipientHome st1 rid target) c hne.1 hne.2 hDon]
                    exact hFrame
        · rfl
      · rfl

end SeLe4n.Kernel
