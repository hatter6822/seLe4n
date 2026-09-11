-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.DualQueue.Transport
import SeLe4n.Kernel.Scheduler.PriorityInheritance.Propagate
import SeLe4n.Kernel.IPC.Operations.Donation.Primitives
import SeLe4n.Kernel.SchedContext.ReplenishAffinity

/-! # Z7: Donation Transport-Dependent Wrappers

SchedContext donation enables passive servers - threads that consume zero CPU
when idle by borrowing the client's SchedContext during IPC Call/Reply.

## Donation Protocol

1. Client calls server via `endpointCall`. If the server is passive (unbound),
   the client's SchedContext is temporarily donated to the server.
2. Server receives `.donated(clientScId, clientTid)` binding. The SchedContext's
   `boundThread` is updated to point to the server.
3. Server runs on the client's CPU budget.
4. Server replies via `endpointReply` or `endpointReplyRecv`. The SchedContext
   is returned to the original client.
5. Server becomes passive again (unbound, not in RunQueue).

## Architecture (post-AN3-A / H-01)

The donation logic is split across two sibling modules:

* `SeLe4n.Kernel.IPC.Operations.Donation.Primitives` - transport-independent
  helpers (`applyCallDonation`, `applyReplyDonation`, all `*_scheduler_eq` /
  `*_machine_eq` / `*_atomicRegion` preservation theorems, server binding
  witnesses). Re-exported by `SeLe4n.Kernel.IPC.Operations` (the IPC operations
  hub).
* This file - donation-aware wrappers around the core transport-layer IPC
  entry points (`endpointCallWithDonation`, `endpointReplyWithDonation`,
  `endpointReplyRecvWithDonation`). These unavoidably depend on
  `SeLe4n.Kernel.IPC.DualQueue.Transport`, so re-exporting this file from
  the operations hub would reintroduce the `Operations -> Donation ->
  Transport -> Core -> Operations` import cycle closed by AI4-A.

Legacy consumers that `import SeLe4n.Kernel.IPC.Operations.Donation` continue
to see the full donation API, because this file re-exports the primitives via
its `import SeLe4n.Kernel.IPC.Operations.Donation.Primitives` line.

This design preserves all existing IPC invariant proofs unchanged - the core
IPC functions are not modified. Donation is applied after the core operation
completes, modifying only `schedContextBinding` fields and RunQueue membership.

## Cross-cutting: Timeout + Donation

When a client's SchedContext is donated to a server and the budget expires:
- The server is preempted (budget exhaustion via `timerTickBudget`)
- The client is timed out (budget-bounded IPC via `timeoutBlockedThreads`)
- The SchedContext returns to the client via timeout cleanup, not reply
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

-- ============================================================================
-- Z7: Donation-aware IPC operation wrappers (transport-dependent subset)
-- ============================================================================

/-- Z7: Donation-aware endpointCall. Composes the standard `endpointCall` with
post-call SchedContext donation to passive servers.

Before calling `endpointCall`, checks if the endpoint has a waiting receiver
(handshake path). If so, records the receiver's ThreadId. After `endpointCall`
completes, applies donation from the caller to the receiver if the receiver
was passive (unbound). -/
def endpointCallWithDonation
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) : Kernel Unit :=
  fun st =>
    -- Pre-check: determine receiver before endpointCall pops it.
    -- AJ1-C (M-02): `endpointQueuePopHead_returns_head` proves the pre-inspected
    -- receiver matches the thread actually dequeued by endpointCall, ensuring
    -- donation targets the correct thread.
    -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration.
    let maybeReceiver := match st.getEndpoint? endpointId with
      | some ep => ep.receiveQ.head
      | none    => none
    match endpointCall endpointId caller msg st with
    | .error e => .error e
    | .ok ((), st') =>
      match maybeReceiver with
      | some receiverTid =>
        -- Handshake path: a receiver was woken — apply donation.
        -- AH2-C: Propagate donation errors.
        -- AN10-residual-1 deep-audit: `applyCallDonation` now requires
        -- `ValidThreadId` for both caller and receiver.  Promote the raw
        -- tids via `toValid?` with `.error .invalidArgument` rejection;
        -- under the AL7 dispatch-gate validators on `caller` and the
        -- `endpointQueuePopHead_returns_head`-witnessed `receiverTid`
        -- (which came from a previously-stored TCB), the rejection
        -- arm is structurally unreachable.
        match SeLe4n.ThreadId.toValid? caller, SeLe4n.ThreadId.toValid? receiverTid with
        | some callerVtid, some receiverVtid =>
          match applyCallDonation st' callerVtid receiverVtid with
          | .error e => .error e
          | .ok st'' =>
            -- D4-L: Apply PIP — propagate priority inheritance from the server
            -- upward through the blocking chain. The server may itself be blocked
            -- on another server, requiring transitive propagation.
            .ok ((), PriorityInheritance.propagatePriorityInheritance st'' receiverTid)
        | _, _ => .error .invalidArgument
      | none =>
        -- Blocking path: no receiver was available, caller blocked
        .ok ((), st')

/-- Z7: Donation-aware endpointReply. Composes the standard `endpointReply`
with post-reply SchedContext return from the server. -/
def endpointReplyWithDonation
    (replier : SeLe4n.ThreadId) (target : SeLe4n.ThreadId)
    (msg : IpcMessage) : Kernel Unit :=
  fun st =>
    match endpointReply replier target msg st with
    | .error e => .error e
    | .ok ((), st') =>
      -- Apply donation return: if replier has donated SC, return it
      -- AH2-C: Propagate donation return errors.
      -- AN10-residual-1 deep-audit: `applyReplyDonation` now requires
      -- `ValidThreadId`.  Promote `replier` via `toValid?` with
      -- `.error .invalidArgument` rejection (unreachable under AL7).
      match SeLe4n.ThreadId.toValid? replier with
      | some replierVtid =>
        match applyReplyDonation st' replierVtid with
        | .error e => .error e
        | .ok st'' =>
          -- D4-M: Revert PIP — the client (target) is unblocked, so the replier's
          -- pipBoost must be recomputed from remaining waiters. Propagate reversion
          -- upward through the chain.
          .ok ((), PriorityInheritance.revertPriorityInheritance st'' replier)
      | none => .error .invalidArgument

/-- Z7: Donation-aware endpointReplyRecv. Composes:
1. Standard endpointReplyRecv (reply + receive) — server still holds donated SC during reply
2. Return old donation from replier AFTER the reply completes
3. (New donation from incoming caller is handled by the Call path)

**Ordering rationale (AUD-3)**: The donation return happens AFTER `endpointReplyRecv`
completes, not before. The server needs the donated SchedContext while replying
(it's the currently running thread with that SC's budget). After the reply delivers
the message and the server enters the receive path, the SC is returned. -/
def endpointReplyRecvWithDonation
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (replyTarget : SeLe4n.ThreadId)
    (msg : IpcMessage)
    -- WS-SM SM6.D (#7.1 fold): the reply object the server supplies for the next
    -- caller on the receive leg, threaded into the folded `endpointReplyRecv`.
    (replyId : Option SeLe4n.ReplyId) : Kernel Unit :=
  fun st =>
    match endpointReplyRecv endpointId receiver replyTarget msg replyId st with
    | .error e => .error e
    | .ok ((), st') =>
      -- Z7-D1: Return old donation AFTER reply+receive completes
      -- AH2-C: Propagate donation return errors.
      -- AN10-residual-1 deep-audit: `applyReplyDonation` now requires
      -- `ValidThreadId`.  Promote `receiver` via `toValid?` with
      -- `.error .invalidArgument` rejection (unreachable under AL7).
      match SeLe4n.ThreadId.toValid? receiver with
      | some receiverVtid =>
        match applyReplyDonation st' receiverVtid with
        | .error e => .error e
        | .ok st'' =>
          -- D4-M: Revert PIP for the reply portion
          .ok ((), PriorityInheritance.revertPriorityInheritance st'' receiver)
      | none => .error .invalidArgument

-- ============================================================================
-- AJ1-D (M-01): Decomposition lemmas for donation-aware wrappers
-- ============================================================================

/-- AJ1-D (M-01): `endpointReplyWithDonation` decomposes into the three-step
sequence: `endpointReply` → `applyReplyDonation` → `revertPriorityInheritance`,
gated by a `replier.toValid?` shim that AN10-residual-1 deep-audit added to
satisfy the `applyReplyDonation` typed signature.  The `none` arm is
structurally unreachable under the AL7 dispatch-gate validators on
`replier`. -/
theorem endpointReplyWithDonation_unfold
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (st : SystemState) :
    endpointReplyWithDonation replier target msg st =
    (match endpointReply replier target msg st with
     | .error e => .error e
     | .ok ((), st') =>
       match SeLe4n.ThreadId.toValid? replier with
       | some replierVtid =>
         match applyReplyDonation st' replierVtid with
         | .error e => .error e
         | .ok st'' =>
           .ok ((), PriorityInheritance.revertPriorityInheritance st'' replier)
       | none => .error .invalidArgument) := by
  rfl

/-- AJ1-D (M-01): `endpointReplyRecvWithDonation` decomposes into:
`endpointReplyRecv` → `applyReplyDonation` → `revertPriorityInheritance`,
gated by a `receiver.toValid?` shim. -/
theorem endpointReplyRecvWithDonation_unfold
    (endpointId : SeLe4n.ObjId) (receiver replyTarget : SeLe4n.ThreadId)
    (msg : IpcMessage) (replyId : Option SeLe4n.ReplyId) (st : SystemState) :
    endpointReplyRecvWithDonation endpointId receiver replyTarget msg replyId st =
    (match endpointReplyRecv endpointId receiver replyTarget msg replyId st with
     | .error e => .error e
     | .ok ((), st') =>
       match SeLe4n.ThreadId.toValid? receiver with
       | some receiverVtid =>
         match applyReplyDonation st' receiverVtid with
         | .error e => .error e
         | .ok st'' =>
           .ok ((), PriorityInheritance.revertPriorityInheritance st'' receiver)
       | none => .error .invalidArgument) := by
  rfl

-- ============================================================================
-- WS-RR RR2.1 / RR2.2 — the cross-core call donation
-- ============================================================================
--
-- `applyCallDonation` rebinds the caller's SchedContext to the receiver with
-- **object writes only**.  On one core that is the whole story; across cores it
-- is not.  Under the SM5.H affinity discipline
-- (`replenishQueueAffinityConsistentOnCore`) a SchedContext's pending CBS
-- replenishments live on its **bound thread's home core's** queue — that is the
-- only core whose timer tick drains them — so a donation to a server homed on
-- another core leaves the budget-refill schedule stranded on the donor's core,
-- where nothing will ever act on it for a SchedContext that is now the donee's.
--
-- `docs/planning/SMP_CROSS_CORE_IPC_PLAN.md` §4.3 already said the migration
-- happens ("if the receiver inherits the SC and is on a different core, the
-- SC's CBS replenish queue migrates per SM5.H.4"); until WS-RR RR2 no donation
-- path did it.  `applyCallDonationOnCore` is that path, built exactly like the
-- cancellation arm that already migrates
-- (`cancelDonatedDonationOnCore`, `IPC/CrossCore/Cancellation.lean`): the
-- unchanged single-core donation, then `migrateSchedContextReplenishment` from
-- the donor's home core to the donee's.

/-- WS-RR RR2.1: the SchedContext a `.call` donation would actually transfer —
`some scId` exactly when `applyCallDonation` takes its donating arm (the
receiver is passive and the caller holds a bound SchedContext), `none` on every
no-op arm.

Single-sourced here because three consumers need the same answer and a second
copy would drift: `applyCallDonationOnCore` names the SchedContext whose
replenishments migrate, the cross-core `.call` dispatch pre-resolves the
`lockSet_endpointCall` donation footprint from it, and the affinity proof below
case-splits on it.  Reading the same function is what keeps the declared lock
footprint and the executed write the same set. -/
def callDonationSchedContext? (st : SystemState) (caller receiver : SeLe4n.ThreadId) :
    Option SeLe4n.SchedContextId :=
  match lookupTcb st receiver with
  | some receiverTcb =>
      match receiverTcb.schedContextBinding with
      | .unbound =>
          match lookupTcb st caller with
          -- **WS-OD OD4.2**: the caller's *effective* context, bound or donated
          -- (`SchedContextBinding.scId?`), so the resolver and the transition
          -- widen in the same cut and cannot disagree about whether a call
          -- donates.
          | some callerTcb => callerTcb.schedContextBinding.scId?
          | none => none
      | _ => none
  | none => none

/-- **WS-OD OD4.2/OD4.6: the guard fires at call depth ≥ 2.**

The resolver reads the caller's *effective* context, so a caller that is itself
holding a donation (`.donated scId owner` -- the intermediate server of a chain)
names `scId` exactly as a `.bound` caller names its own.  This is the fact that
makes the chain transitive at the resolver, stated rather than read off the
definition at each of its three consumers.

The receiver's `.unbound` premise is the other half of the guard and is what a
passive server *is*; without it the call is a no-op at any depth. -/
theorem callDonationSchedContext?_of_donated_caller
    (st : SystemState) (caller receiver : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId)
    (cTcb rTcb : TCB)
    (hR : lookupTcb st receiver = some rTcb)
    (hRB : rTcb.schedContextBinding = .unbound)
    (hC : lookupTcb st caller = some cTcb)
    (hCB : cTcb.schedContextBinding = .donated scId owner) :
    callDonationSchedContext? st caller receiver = some scId := by
  unfold callDonationSchedContext?
  rw [hR]
  simp only []
  rw [hRB]
  simp only []
  rw [hC]
  simp only []
  rw [hCB]
  rfl

/-- WS-RR RR2.1 (characterisation): the single-core call donation *is* the
`callDonationSchedContext?` case split — `donateSchedContext` on the resolved
SchedContext when there is one, the identity otherwise.  Everything the
cross-core form needs about the single-core one factors through this. -/
theorem applyCallDonation_characterisation
    (st : SystemState) (callerVtid receiverVtid : SeLe4n.ValidThreadId) :
    applyCallDonation st callerVtid receiverVtid
      = (match callDonationSchedContext? st callerVtid.val receiverVtid.val with
         | some scId => donateSchedContext st callerVtid.val receiverVtid.val scId
         | none      => .ok st) := by
  simp only [applyCallDonation, callDonationSchedContext?]
  cases lookupTcb st receiverVtid.val with
  | none => rfl
  | some receiverTcb =>
    simp only []
    cases receiverTcb.schedContextBinding with
    | bound _ => rfl
    | donated _ _ => rfl
    | unbound =>
      simp only []
      cases lookupTcb st callerVtid.val with
      | none => rfl
      | some callerTcb =>
        simp only []
        cases callerTcb.schedContextBinding.scId? with
        | none => rfl
        | some scId =>
          simp only [donateSchedContextValid]
          cases donateSchedContext st callerVtid.val receiverVtid.val scId <;> rfl

/-- WS-RR RR2.1: on every arm where no SchedContext changes hands, the
single-core donation is the identity. -/
theorem applyCallDonation_eq_ok_self_of_no_donation
    (st : SystemState) (callerVtid receiverVtid : SeLe4n.ValidThreadId)
    (h : callDonationSchedContext? st callerVtid.val receiverVtid.val = none) :
    applyCallDonation st callerVtid receiverVtid = .ok st := by
  rw [applyCallDonation_characterisation, h]

/-- WS-RR RR2.1: on the donating arm, the single-core donation is exactly
`donateSchedContext` for the resolved SchedContext. -/
theorem applyCallDonation_eq_donate_of_donation
    (st : SystemState) (callerVtid receiverVtid : SeLe4n.ValidThreadId)
    (scId : SeLe4n.SchedContextId)
    (h : callDonationSchedContext? st callerVtid.val receiverVtid.val = some scId) :
    applyCallDonation st callerVtid receiverVtid
      = donateSchedContext st callerVtid.val receiverVtid.val scId := by
  rw [applyCallDonation_characterisation, h]

/-- WS-RR RR2.8: the SchedContext a `.reply` donation return would actually hand
back, with its original owner — `some (scId, owner)` exactly when
`applyReplyDonation{,OnCore}` takes its returning arm, `none` on every no-op
arm.

Single-sourced here, beside `callDonationSchedContext?`, for the same reason:
the transition names the SchedContext whose replenishments migrate,
the cross-core `.reply` lock-set pre-resolves `lockSet_endpointReply`'s
`(donatedScId, donatedOriginalOwnerTid)` pair from it, and the affinity proof
case-splits on it.  One function, so the declared footprint and the executed
write cannot disagree. -/
def replyDonationReturn? (st : SystemState) (replier : SeLe4n.ThreadId) :
    Option (SeLe4n.SchedContextId × SeLe4n.ThreadId) :=
  match lookupTcb st replier with
  | some replierTcb =>
      match replierTcb.schedContextBinding with
      | .donated scId owner => some (scId, owner)
      | _ => none
  | none => none

/-- WS-RR RR2.5 (characterisation): the single-core donation return *is* the
`replyDonationReturn?` case split — the mirror of
`applyCallDonation_characterisation`, and the shape every reply-side invariant
proof runs on.  Without it each such proof re-derives the same four-deep match
by hand, and each derivation is a place the operation and its model can drift
apart. -/
theorem applyReplyDonation_characterisation
    (st : SystemState) (replierVtid : SeLe4n.ValidThreadId) :
    applyReplyDonation st replierVtid
      = (match replyDonationReturn? st replierVtid.val with
         | some (scId, owner) =>
             (match SeLe4n.ThreadId.toValid? owner with
              | some ownerVtid =>
                  -- WS-OD OD4.4: the resolved return — the model follows the
                  -- operation onto the reply-stack resolver, or it is a model of
                  -- a different program.
                  (match returnDonatedSchedContextResolved st replierVtid.val scId
                      ownerVtid.val with
                   | .error e => .error e
                   | .ok st' => .ok (removeRunnable st' replierVtid.val))
              | none => .error .invalidArgument)
         | none => .ok st) := by
  simp only [applyReplyDonation, replyDonationReturn?]
  cases lookupTcb st replierVtid.val with
  | none => rfl
  | some replierTcb =>
    simp only []
    cases replierTcb.schedContextBinding with
    | unbound => rfl
    | bound _ => rfl
    | donated _ _ =>
        simp only []
        cases SeLe4n.ThreadId.toValid? _ with
        | none => rfl
        | some ownerVtid =>
            simp only []
            cases returnDonatedSchedContextResolved st replierVtid.val _ ownerVtid.val <;> rfl

/-- WS-RR RR2.1 / RR2.2 (operation): the cross-core `.call` SchedContext
donation — the single-core `applyCallDonation` **plus** the SM5.H.4
replenishment migration from the donor's home core to the donee's.

`donorHome` / `doneeHome` are the migration's endpoints, resolved by the caller
from the **pre**-state (`determineTargetCore st caller` /
`determineTargetCore st receiver`).  Resolving them outside is what lets the
`withLockSet` bracket declare and acquire the two `SchedLockId.replenishQueue`
write locks *before* the transition runs — the SM3.B discipline the cross-core
lock-set follows for every donation-carrying syscall — and the rebinding itself
never touches a `cpuAffinity`, so a pre-state reading is the same reading the
post-state would give (`donateSchedContext_getTcb?_cpuAffinity_eq`).

Self-migration — a shared home core, and in particular every single-core
configuration — is a definitional no-op
(`migrateSchedContextReplenishment_noop`), so this is exactly the single-core
donation there (`applyCallDonationOnCore_eq_of_sharedHome`). -/
def applyCallDonationOnCore
    (st : SystemState)
    (callerVtid receiverVtid : SeLe4n.ValidThreadId)
    (donorHome doneeHome : CoreId) : Except KernelError SystemState :=
  match applyCallDonation st callerVtid receiverVtid with
  | .error e => .error e
  | .ok st' =>
      match callDonationSchedContext? st callerVtid.val receiverVtid.val with
      | some scId => .ok (migrateSchedContextReplenishment st' scId donorHome doneeHome)
      | none      => .ok st'

/-- WS-RR RR2.13 (bridge): when donor and donee share a home core — in
particular in every single-core configuration — the cross-core call donation is
**exactly** the single-core `applyCallDonation`. -/
theorem applyCallDonationOnCore_eq_of_sharedHome
    (st : SystemState) (callerVtid receiverVtid : SeLe4n.ValidThreadId) (c : CoreId) :
    applyCallDonationOnCore st callerVtid receiverVtid c c
      = applyCallDonation st callerVtid receiverVtid := by
  unfold applyCallDonationOnCore
  cases hDon : applyCallDonation st callerVtid receiverVtid with
  | error e => rfl
  | ok st' =>
    cases hSc : callDonationSchedContext? st callerVtid.val receiverVtid.val with
    | none => rfl
    | some scId => simp only [migrateSchedContextReplenishment_noop]

/-- WS-RR RR2.1 (decomposition): a successful cross-core call donation is the
successful single-core donation, optionally followed by the migration. -/
theorem applyCallDonationOnCore_ok_decompose
    (st st'' : SystemState) (callerVtid receiverVtid : SeLe4n.ValidThreadId)
    (donorHome doneeHome : CoreId)
    (h : applyCallDonationOnCore st callerVtid receiverVtid donorHome doneeHome = .ok st'') :
    ∃ st', applyCallDonation st callerVtid receiverVtid = .ok st' ∧
      ((callDonationSchedContext? st callerVtid.val receiverVtid.val = none ∧ st'' = st')
        ∨ ∃ scId, callDonationSchedContext? st callerVtid.val receiverVtid.val = some scId ∧
            st'' = migrateSchedContextReplenishment st' scId donorHome doneeHome) := by
  unfold applyCallDonationOnCore at h
  cases hDon : applyCallDonation st callerVtid receiverVtid with
  | error e => rw [hDon] at h; cases h
  | ok st' =>
    rw [hDon] at h
    simp only [] at h
    cases hSc : callDonationSchedContext? st callerVtid.val receiverVtid.val with
    | none =>
      rw [hSc] at h
      exact ⟨st', rfl, Or.inl ⟨rfl, (Except.ok.inj h).symm⟩⟩
    | some scId =>
      rw [hSc] at h
      exact ⟨st', rfl, Or.inr ⟨scId, rfl, (Except.ok.inj h).symm⟩⟩

/-- WS-RR RR2.1 (frame): the cross-core call donation never advances the machine
timer — the rebinding writes objects and the migration writes replenish-queue
slots. -/
theorem applyCallDonationOnCore_machine_eq
    (st st'' : SystemState) (callerVtid receiverVtid : SeLe4n.ValidThreadId)
    (donorHome doneeHome : CoreId)
    (h : applyCallDonationOnCore st callerVtid receiverVtid donorHome doneeHome = .ok st'') :
    st''.machine = st.machine := by
  obtain ⟨st', hDon, harm⟩ := applyCallDonationOnCore_ok_decompose st st'' callerVtid receiverVtid
    donorHome doneeHome h
  have hM := applyCallDonation_machine_eq st callerVtid receiverVtid st' hDon
  rcases harm with ⟨_, hEq⟩ | ⟨scId, _, hEq⟩ <;> subst hEq
  · exact hM
  · rw [migrateSchedContextReplenishment_machine]; exact hM

/-- WS-RR RR2.1 (frame): the cross-core call donation never disturbs any core's
run queue or current slot.  The rebinding preserves the whole scheduler
(`applyCallDonation_scheduler_eq`) and the migration writes only replenish-queue
slots, so nothing schedulable moves — a donation is a budget transfer, not a
scheduling decision. -/
theorem applyCallDonationOnCore_runQueue_current_eq
    (st st'' : SystemState) (callerVtid receiverVtid : SeLe4n.ValidThreadId)
    (donorHome doneeHome : CoreId) (c : CoreId)
    (h : applyCallDonationOnCore st callerVtid receiverVtid donorHome doneeHome = .ok st'') :
    st''.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c
    ∧ st''.scheduler.currentOnCore c = st.scheduler.currentOnCore c := by
  obtain ⟨st', hDon, harm⟩ := applyCallDonationOnCore_ok_decompose st st'' callerVtid receiverVtid
    donorHome doneeHome h
  have hS := applyCallDonation_scheduler_eq st callerVtid receiverVtid st' hDon
  rcases harm with ⟨_, hEq⟩ | ⟨scId, _, hEq⟩ <;> subst hEq
  · exact ⟨by rw [hS], by rw [hS]⟩
  · obtain ⟨hRQ, hCur⟩ :=
      migrateSchedContextReplenishment_runQueue_current_eq st' scId donorHome doneeHome c
    exact ⟨by rw [hRQ, hS], by rw [hCur, hS]⟩

/-- WS-RR RR2.1 (frame): the cross-core call donation commits exactly the
single-core donation's object store — the migration writes no object. -/
theorem applyCallDonationOnCore_objects_eq
    (st st' st'' : SystemState) (callerVtid receiverVtid : SeLe4n.ValidThreadId)
    (donorHome doneeHome : CoreId)
    (hDon : applyCallDonation st callerVtid receiverVtid = .ok st')
    (h : applyCallDonationOnCore st callerVtid receiverVtid donorHome doneeHome = .ok st'') :
    st''.objects = st'.objects := by
  obtain ⟨st1, hDon1, harm⟩ := applyCallDonationOnCore_ok_decompose st st'' callerVtid receiverVtid
    donorHome doneeHome h
  have hSame : st1 = st' := Except.ok.inj (hDon1.symm.trans hDon)
  subst hSame
  rcases harm with ⟨_, hEq⟩ | ⟨scId, _, hEq⟩ <;> subst hEq
  · rfl
  · exact migrateSchedContextReplenishment_objects _ _ _ _

-- ============================================================================
-- WS-RR RR2.3 — the call path preserves the SM5.H affinity invariant
-- ============================================================================

/-- WS-RR RR2.3: **the cross-core call donation restores replenish-queue
affinity consistency on every core.**

This is the theorem the migration exists for.  The donation rebinds exactly one
SchedContext — from the caller to the receiver — so exactly that SchedContext's
replenish entries become mis-homed, and they are exactly the entries the
migration moves.  The four obligations of
`migrateSchedContextReplenishment_preserves_affinityConsistent_smp` land as
follows:

* **the destination** carries the migrated entries, whose SchedContext is now
  bound to the receiver, homed on `doneeHome` by hypothesis;
* **the source** keeps only its other SchedContexts' entries, which the
  pre-state invariant already places there;
* **every other core** holds no entry for the donated SchedContext at all —
  under the pre-state invariant such an entry would force the *donor's* home to
  be that core, and the donor's home is `donorHome`.  This is where
  `donateSchedContext`'s own `sc.boundThread = some clientTid` guard pays for
  itself: success witnesses the pre-state binding
  (`donateSchedContext_ok_implies_sc_bound`), so the confinement is derived, not
  assumed;
* and the rebinding moves no thread's `cpuAffinity` and no other SchedContext,
  so every reading the invariant makes is the pre-state's
  (`donateSchedContext_getTcb?_cpuAffinity_eq`,
  `donateSchedContext_getSchedContext?_ne`).

The two home-core hypotheses are discharged by `rfl` at the live call site,
which resolves both from the pre-state. -/
theorem applyCallDonationOnCore_preserves_replenishQueueAffinityConsistent_smp
    (st st'' : SystemState) (callerVtid receiverVtid : SeLe4n.ValidThreadId)
    (donorHome doneeHome : CoreId)
    (hObjInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st)
    (hDonorHome : determineTargetCore st callerVtid.val = donorHome)
    (hDoneeHome : determineTargetCore st receiverVtid.val = doneeHome)
    (h : applyCallDonationOnCore st callerVtid receiverVtid donorHome doneeHome = .ok st'') :
    replenishQueueAffinityConsistent_smp st'' := by
  obtain ⟨st1, hDon, harm⟩ := applyCallDonationOnCore_ok_decompose st st'' callerVtid receiverVtid
    donorHome doneeHome h
  rcases harm with ⟨hNone, hEq⟩ | ⟨scId, hSome, hEq⟩ <;> rw [hEq]
  · -- No SchedContext changed hands: the donation is the identity.
    have hSelf : applyCallDonation st callerVtid receiverVtid = .ok st :=
      applyCallDonation_eq_ok_self_of_no_donation st callerVtid receiverVtid hNone
    have hIdent : st1 = st := Except.ok.inj (hDon.symm.trans hSelf)
    rw [hIdent]; exact hCons
  · -- The donating arm: `st1` is `donateSchedContext`'s post-state.
    have hDonate : donateSchedContext st callerVtid.val receiverVtid.val scId = .ok st1 :=
      (applyCallDonation_eq_donate_of_donation st callerVtid receiverVtid scId hSome).symm.trans hDon
    -- The rebinding's readings.
    have hSched : st1.scheduler = st.scheduler :=
      applyCallDonation_scheduler_eq st callerVtid receiverVtid st1 hDon
    have hHomeEq : ∀ tid, determineTargetCore st1 tid = determineTargetCore st tid := fun tid =>
      determineTargetCore_congr st st1 tid
        (donateSchedContext_getTcb?_cpuAffinity_eq st st1 callerVtid.val receiverVtid.val scId
          hObjInv hDonate tid)
    have hScNe : ∀ scId', scId' ≠ scId → st1.getSchedContext? scId' = st.getSchedContext? scId' :=
      fun scId' hne => donateSchedContext_getSchedContext?_ne st st1 callerVtid.val receiverVtid.val
        scId scId' hne hObjInv hDonate
    obtain ⟨scPost, hScPost, hScPostBound⟩ :=
      donateSchedContext_post_boundThread st st1 callerVtid.val receiverVtid.val scId hObjInv hDonate
    obtain ⟨scPre, hScPreRaw, hScPreBound⟩ :=
      donateSchedContext_ok_implies_sc_bound st st1 callerVtid.val receiverVtid.val scId hDonate
    have hScPre : st.getSchedContext? scId = some scPre := by
      unfold SystemState.getSchedContext?; rw [hScPreRaw]
    -- Reading an entry of `st1`'s queue is reading the same entry of `st`'s.
    have hQueue : ∀ c, st1.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c :=
      fun c => by rw [hSched]
    -- A `scId` entry anywhere in the pre-state forces that core to be `donorHome`.
    have hConfined : ∀ c t, (scId, t) ∈ (st.scheduler.replenishQueueOnCore c).entries →
        c = donorHome := by
      intro c t hMem
      rw [← hDonorHome]
      exact (hCons c scId t hMem scPre hScPre callerVtid.val hScPreBound).symm
    -- Post-donation consistency of `st1`, core by core.
    have hCons1 : ∀ c, c ≠ donorHome →
        replenishQueueAffinityConsistentOnCore st1 c := by
      intro c hcNe scId₀ t hMem sc₀ hSc₀ tid hBound
      rw [hQueue c] at hMem
      rw [hHomeEq tid]
      by_cases hk : scId₀ = scId
      · subst hk; exact absurd (hConfined c t hMem) hcNe
      · rw [hScNe scId₀ hk] at hSc₀
        exact hCons c scId₀ t hMem sc₀ hSc₀ tid hBound
    -- The destination core: pre-existing entries are consistent because a `scId`
    -- entry there would force `doneeHome = donorHome`, and the rest carry over.
    have hConsTo : replenishQueueAffinityConsistentOnCore st1 doneeHome := by
      intro scId₀ t hMem sc₀ hSc₀ tid hBound
      rw [hQueue doneeHome] at hMem
      rw [hHomeEq tid]
      by_cases hk : scId₀ = scId
      · subst hk
        rw [hScPost] at hSc₀
        cases hSc₀
        rw [hScPostBound] at hBound
        cases hBound
        exact hDoneeHome
      · rw [hScNe scId₀ hk] at hSc₀
        exact hCons doneeHome scId₀ t hMem sc₀ hSc₀ tid hBound
    have hConsFrom : ∀ (scId₀ : SeLe4n.SchedContextId) (t : Nat),
        (scId₀, t) ∈ (st1.scheduler.replenishQueueOnCore donorHome).entries → scId₀ ≠ scId →
          ∀ sc₀, st1.getSchedContext? scId₀ = some sc₀ →
            ∀ tid, sc₀.boundThread = some tid → determineTargetCore st1 tid = donorHome := by
      intro scId₀ t hMem hk sc₀ hSc₀ tid hBound
      rw [hQueue donorHome] at hMem
      rw [hHomeEq tid, hScNe scId₀ hk] at *
      exact hCons donorHome scId₀ t hMem sc₀ hSc₀ tid hBound
    have hHome : ∀ sc, st1.getSchedContext? scId = some sc →
        ∀ tid, sc.boundThread = some tid → determineTargetCore st1 tid = doneeHome := by
      intro sc hSc tid hBound
      rw [hScPost] at hSc
      cases hSc
      rw [hScPostBound] at hBound
      cases hBound
      rw [hHomeEq]; exact hDoneeHome
    exact migrateSchedContextReplenishment_preserves_affinityConsistent_smp st1 scId
      donorHome doneeHome
      (fun c' hFrom _ => hCons1 c' (fun hEq => hFrom hEq.symm))
      hConsTo hConsFrom hHome

-- ============================================================================
-- WS-RR RR2.20 — the PIP chain walk preserves the SM5.H affinity invariant
-- ============================================================================

/-- WS-RR RR2.20: **the cross-core priority-inheritance chain walk preserves
replenish-queue affinity consistency.**

Not because it re-establishes anything, but because it is a *frame*: the walk
writes `pipBoost` on the chain's TCBs and re-keys their run-queue buckets, and
the affinity invariant reads none of that — it reads core `c`'s replenish queue,
`getSchedContext?` and `determineTargetCore`, all three of which
`propagatePipChainCrossCore_replenish_readings` shows the walk leaves alone.

This module is the composite's home because it is the only place in the tree
that imports both `PriorityInheritance.Propagate` and
`SchedContext.ReplenishAffinity`; adding either import to the other module
closes a cycle through `IPC.Operations.Timeout`. -/
theorem propagatePipChainCrossCore_preserves_replenishQueueAffinityConsistent_smp
    (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId) (fuel : Nat)
    (hObjInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st) :
    replenishQueueAffinityConsistent_smp
      (PriorityInheritance.propagatePipChainCrossCore st tid ec fuel).1 := by
  obtain ⟨hRepl, hSc, hTgt⟩ :=
    PriorityInheritance.propagatePipChainCrossCore_replenish_readings st tid ec fuel hObjInv
  intro c
  exact (replenishQueueAffinityConsistentOnCore_congr (hRepl c) hSc hTgt).mpr (hCons c)

/-- **WS-OD OD3.6: seL4-MCS's `maybeDonateSchedContext`, asked once.**

A receive that rendezvouses with a queued `Call` hands the caller's scheduling
context to the receiver — seL4-MCS's `receiveIPC` reaches it through
`reply_push` → `schedContext_donate`, so the server runs the request on the
client's own reservation and the work is charged where it belongs.

This is the step `replyRecvReturnDonation`'s third stage performs, lifted out of
it so that `.receive` performs *the same one*.  It did not: the `.receive`
dispatch arm ran `endpointReceiveDualWithCapsOnCore` and staged frames, with no
donation anywhere on the path, so a passive server taking its **first** request
with `seL4_Recv` received no budget while the same server taking its second and
later requests with `seL4_ReplyRecv` was charged correctly — two API paths
handling one condition asymmetrically, and the asymmetric one silently defeating
the budget enforcement the whole CBS surface exists to provide.

Both home cores are read from the state the donation runs on, which is the
reading the two `*OnCore` donation primitives take at every other call site:
neither primitive writes a `cpuAffinity`
(`donateSchedContext_getTcb?_cpuAffinity_eq`), so a pre-resolution and a
post-resolution agree.

Total, and the identity wherever it must not fire: `applyCallDonation` no-ops
(`.ok st`) unless the receiver is `.unbound` **and** the donor is `.bound`, so
this is definitionally a no-op on every state where there is nothing to donate —
which is what lets every result taken before OD3.6 survive on the states it held
for.  `.invalidArgument` is reserved for a reserved (idle) thread id, which
`ThreadId.toValid?` refuses and which no rendezvous can produce. -/
def applyRendezvousCallDonation (st : SystemState)
    (receiver donor : SeLe4n.ThreadId) : Except KernelError SystemState :=
  match donor.toValid?, receiver.toValid? with
  | some donorV, some receiverV =>
      applyCallDonationOnCore st donorV receiverV
        (determineTargetCore st donor) (determineTargetCore st receiver)
  | _, _ => .error .invalidArgument

/-- **WS-OD OD5.5: `.replyRecv`'s (and `.receive`'s) re-donation is a PUSH at
every chain depth.**

The rendezvous hand-off is the third live site that writes a reply-stack frame,
after `.call` and the receive rendezvous.  Its donor is the thread the receive
leg just dequeued, and OD4.2's widened guard makes it donate whether that thread
holds its context `.bound` or `.donated` -- so a client that is itself an
intermediate server of a longer chain passes the context on rather than stopping
it, which is the whole point of the workstream.

The statement exhibits the push: on a `.donated` donor and an `.unbound`
receiver, the hand-off *is* `donateSchedContext` on the donor's effective context,
followed by the SM5.H replenishment migration between the two threads' homes. -/
theorem applyRendezvousCallDonation_donated_donor_pushes
    (st st' : SystemState) (receiver donor : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId)
    (rTcb dTcb : TCB)
    (hR : lookupTcb st receiver = some rTcb)
    (hRB : rTcb.schedContextBinding = .unbound)
    (hD : lookupTcb st donor = some dTcb)
    (hDB : dTcb.schedContextBinding = .donated scId owner)
    (h : applyRendezvousCallDonation st receiver donor = .ok st') :
    ∃ st1 : SystemState,
      donateSchedContext st donor receiver scId = .ok st1 ∧
      st' = migrateSchedContextReplenishment st1 scId
        (determineTargetCore st donor) (determineTargetCore st receiver) := by
  have hSc : callDonationSchedContext? st donor receiver = some scId :=
    callDonationSchedContext?_of_donated_caller st donor receiver scId owner dTcb rTcb hR hRB
      hD hDB
  unfold applyRendezvousCallDonation at h
  cases hDV : donor.toValid? with
  | none => rw [hDV] at h; simp only [] at h; cases h
  | some donorV =>
    cases hRV : receiver.toValid? with
    | none => rw [hDV, hRV] at h; simp only [] at h; cases h
    | some receiverV =>
      rw [hDV, hRV] at h
      simp only [] at h
      have hDEq : donorV.val = donor := SeLe4n.ThreadId.toValid?_some_val_eq donor donorV hDV
      have hREq : receiverV.val = receiver :=
        SeLe4n.ThreadId.toValid?_some_val_eq receiver receiverV hRV
      obtain ⟨st1, hDon, harm⟩ := applyCallDonationOnCore_ok_decompose st st' donorV receiverV
        (determineTargetCore st donor) (determineTargetCore st receiver) h
      have hScV : callDonationSchedContext? st donorV.val receiverV.val = some scId := by
        rw [hDEq, hREq]; exact hSc
      have hPush : donateSchedContext st donor receiver scId = .ok st1 := by
        rw [← hDEq, ← hREq]
        exact (applyCallDonation_eq_donate_of_donation st donorV receiverV scId hScV).symm.trans
          hDon
      rcases harm with ⟨hNone, _⟩ | ⟨scId', hSome, hEq⟩
      · exact absurd (hScV.symm.trans hNone) (by simp)
      · obtain rfl : scId' = scId := Option.some.inj (hSome.symm.trans hScV)
        exact ⟨st1, hPush, hEq⟩

/-- **WS-OD OD3.6: did the receive leg dequeue a `Call`?**

The post-state question the donation is gated on: a `Call` sender lands
`.blockedOnReply` at the rendezvous, a plain `Send` sender lands `.ready`, and a
receive that dequeued nothing returns the receiver's own id — which is
`.blockedOnReceive`, so the guard is false without a separate rendezvous test.

Reads through `lookupTcb`, not `getTcb?`, because `lookupTcb` refuses a reserved
(idle) thread id and the donation must never fire on one. -/
def rendezvousDequeuedCall (st : SystemState) (dequeued : SeLe4n.ThreadId) : Bool :=
  match lookupTcb st dequeued with
  | some tcb =>
      match tcb.ipcState with
      | .blockedOnReply _ _ => true
      | _                   => false
  | none => false

/-- **WS-OD OD3.6**: the guarded step — donate when the rendezvous dequeued a
`Call`, and otherwise change nothing.  This is what a receiving arm calls. -/
def applyReceiveRendezvousDonation (st : SystemState)
    (receiver dequeued : SeLe4n.ThreadId) : Except KernelError SystemState :=
  if rendezvousDequeuedCall st dequeued then
    applyRendezvousCallDonation st receiver dequeued
  else
    .ok st

/-- WS-OD OD3.6: a receive that dequeued no `Call` commits nothing at all. -/
@[simp] theorem applyReceiveRendezvousDonation_of_no_call (st : SystemState)
    (receiver dequeued : SeLe4n.ThreadId)
    (h : rendezvousDequeuedCall st dequeued = false) :
    applyReceiveRendezvousDonation st receiver dequeued = .ok st := by
  unfold applyReceiveRendezvousDonation
  rw [h]
  rfl

/-- WS-OD OD3.6: and on a `Call` rendezvous it is exactly the donation. -/
@[simp] theorem applyReceiveRendezvousDonation_of_call (st : SystemState)
    (receiver dequeued : SeLe4n.ThreadId)
    (h : rendezvousDequeuedCall st dequeued = true) :
    applyReceiveRendezvousDonation st receiver dequeued
      = applyRendezvousCallDonation st receiver dequeued := by
  unfold applyReceiveRendezvousDonation
  rw [h]
  rfl

/-- **WS-OD OD3.6**: the rendezvous hand-off decomposes to the cross-core
donation at the two validated thread ids, with both home cores read off the
state it runs on.

Every consumer's frame and preservation obligation goes through this, so a
receiving arm never re-derives the `toValid?` case split; the `.error` arm is
`.invalidArgument` on a reserved id, which no rendezvous produces. -/
theorem applyRendezvousCallDonation_ok_decompose
    (st st'' : SystemState) (receiver donor : SeLe4n.ThreadId)
    (h : applyRendezvousCallDonation st receiver donor = .ok st'') :
    ∃ donorV receiverV : SeLe4n.ValidThreadId,
      donorV.val = donor ∧ receiverV.val = receiver ∧
      applyCallDonationOnCore st donorV receiverV
        (determineTargetCore st donor) (determineTargetCore st receiver) = .ok st'' := by
  unfold applyRendezvousCallDonation at h
  cases hD : donor.toValid? with
  | none => rw [hD] at h; simp only [] at h; cases h
  | some donorV =>
    cases hR : receiver.toValid? with
    | none => rw [hD, hR] at h; simp only [] at h; cases h
    | some receiverV =>
      rw [hD, hR] at h
      exact ⟨donorV, receiverV,
        SeLe4n.ThreadId.toValid?_some_val_eq donor donorV hD,
        SeLe4n.ThreadId.toValid?_some_val_eq receiver receiverV hR, h⟩

/-- WS-OD OD3.6: the rendezvous hand-off keeps the SM5.H replenish-queue
affinity, because the primitive it composes does and both home cores are read
off the very state the donation runs on — the `rfl` instantiation of the
primitive's two hypotheses. -/
theorem applyRendezvousCallDonation_preserves_replenishQueueAffinityConsistent_smp
    (st st'' : SystemState) (receiver donor : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st)
    (h : applyRendezvousCallDonation st receiver donor = .ok st'') :
    replenishQueueAffinityConsistent_smp st'' := by
  obtain ⟨donorV, receiverV, hDv, hRv, hDon⟩ :=
    applyRendezvousCallDonation_ok_decompose st st'' receiver donor h
  exact applyCallDonationOnCore_preserves_replenishQueueAffinityConsistent_smp
    st st'' donorV receiverV _ _ hObjInv hCons (by rw [hDv]) (by rw [hRv]) hDon

/-- WS-OD OD3.6: and so does the guarded form, whose other arm changes nothing. -/
theorem applyReceiveRendezvousDonation_preserves_replenishQueueAffinityConsistent_smp
    (st st'' : SystemState) (receiver dequeued : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st)
    (h : applyReceiveRendezvousDonation st receiver dequeued = .ok st'') :
    replenishQueueAffinityConsistent_smp st'' := by
  unfold applyReceiveRendezvousDonation at h
  cases hCall : rendezvousDequeuedCall st dequeued with
  | false => rw [hCall] at h; simp only [Bool.false_eq_true, if_false] at h; cases h; exact hCons
  | true =>
    rw [hCall] at h
    simp only [if_true] at h
    exact applyRendezvousCallDonation_preserves_replenishQueueAffinityConsistent_smp
      st st'' receiver dequeued hObjInv hCons h

/-- **WS-OD OD3.6**: the guard *is* the donation's caller-blocked obligation.

`applyCallDonation`'s invariant surface asks that the donor be `.blockedOnReply`
at the donation site, and `rendezvousDequeuedCall` is exactly that fact read off
the state the donation runs on — so a receiving arm discharges the hypothesis
from its own guard rather than re-establishing it, and the two cannot disagree
about which states the donation fires on.

Stated over `getTcb?` because that is what the invariant surface reads;
`lookupTcb`'s extra sentinel guard is a success the true branch has passed
(`getTcb?_of_lookupTcb`). -/
theorem rendezvousDequeuedCall_blockedOnReply (st : SystemState)
    (dequeued : SeLe4n.ThreadId) (h : rendezvousDequeuedCall st dequeued = true) :
    ∀ tcb, st.getTcb? dequeued = some tcb →
      ∃ ep rt, tcb.ipcState = .blockedOnReply ep rt := by
  unfold rendezvousDequeuedCall at h
  intro tcb hG
  cases hL : lookupTcb st dequeued with
  | none => rw [hL] at h; exact absurd h (by simp)
  | some tcb0 =>
    have hEq : tcb = tcb0 := by
      have hGet := getTcb?_of_lookupTcb st dequeued tcb0 hL
      rw [hGet] at hG
      exact (Option.some.inj hG).symm
    subst hEq
    rw [hL] at h
    revert h
    cases hIpc : tcb.ipcState <;> simp_all

-- ============================================================================
-- WS-OD OD3.14 — the receive rendezvous' PRIORITY hand-off
-- ============================================================================

/-- **WS-OD OD3.14: the receive-side priority hand-off.**

A rendezvous that dequeued a `Call` leaves that caller `.blockedOnReply _ (some
receiver)`, and `computeMaxWaiterPriority` — the value `updatePipBoostOnCore`
installs — is a maximum over exactly the threads in that state.  So the
receiver's `pipBoost` is the **only** channel by which a blocked caller's
priority reaches the scheduler: `resolveEffectivePrioDeadline` takes the base
priority from the SchedContext for `.bound` and `.donated` alike and then
applies `max basePrio pipBoost`, so OD3.6's donation carries the caller's *base*
priority to the receiver and carries no boost at all.  Without this walk a chain
`D → C → S` — `D` blocked on `C`, `C` dequeued into `.blockedOnReply` on the
passive server `S` — leaves `D`'s inherited priority stopping dead at `C`, which
is unbounded priority inversion for `D`.  It bites with **no** donation too:
`applyCallDonation` is the identity when the receiver is already `.bound`, and
that receiver still gains the waiter.

The walk starts **at the receiver** and runs upward, which is the same start
point `.call` uses from its own receiver (`endpointCallCrossCoreDispatch`) and
the same one `.replyRecv` reaches when its reply is not delegated.  Stating it as
the chain walk rather than a single boost is what keeps it correct where the
receiver is itself blocked deeper in a chain; where it is not, `blockingServer`
terminates the walk after the receiver's own link.

The SGI list is discarded, as at every other propagation site: the syscall seam
derives its cross-core pokes from the `(pre, post)` diff
(`computeCrossCoreSgis`), so a run-queue bucket this walk migrates on a remote
core surfaces there.  The walk's **state** does not depend on `executingCore` at
all — that argument decides only which SGIs the discarded list carries. -/
def applyReceiverPipHandoff (st : SystemState) (receiver : SeLe4n.ThreadId)
    (executingCore : CoreId) : SystemState :=
  (PriorityInheritance.propagatePipChainCrossCore st receiver executingCore).1

/-- **WS-OD OD3.14**: both halves of a receive rendezvous' hand-off — the
scheduling context (OD3.6) and the priority — under **one** reading of the
guard.

The guard is read from the *pre*-state `st`, once, and governs both halves, so
the donation and the boost provably fire on exactly the same states.  A second
reading on the post-donation state would be a second answer to a question this
one already asks, and would owe an `ipcState` frame lemma for the donation
before it could be trusted to agree.

Total, and inert where it must be: on a receive that blocked, and on a plain
`Send` rendezvous, `rendezvousDequeuedCall` is false and this is `.ok st` — so
every result taken before OD3.14 survives on the states it held for, exactly as
OD3.6's donation did. -/
def applyReceiveRendezvousHandoff (st : SystemState)
    (receiver dequeued : SeLe4n.ThreadId) (executingCore : CoreId) :
    Except KernelError SystemState :=
  match applyReceiveRendezvousDonation st receiver dequeued with
  | .error e => .error e
  | .ok stDon =>
      .ok (if rendezvousDequeuedCall st dequeued then
             applyReceiverPipHandoff stDon receiver executingCore
           else stDon)

/-- WS-OD OD3.14: a receive that dequeued no `Call` commits nothing at all —
neither a donation nor a boost. -/
@[simp] theorem applyReceiveRendezvousHandoff_of_no_call (st : SystemState)
    (receiver dequeued : SeLe4n.ThreadId) (executingCore : CoreId)
    (h : rendezvousDequeuedCall st dequeued = false) :
    applyReceiveRendezvousHandoff st receiver dequeued executingCore = .ok st := by
  unfold applyReceiveRendezvousHandoff
  rw [applyReceiveRendezvousDonation_of_no_call st receiver dequeued h]
  simp only [h, Bool.false_eq_true, if_false]

/-- WS-OD OD3.14: and on a `Call` rendezvous it is OD3.6's donation followed by
the chain walk from the receiver. -/
theorem applyReceiveRendezvousHandoff_of_call (st stDon : SystemState)
    (receiver dequeued : SeLe4n.ThreadId) (executingCore : CoreId)
    (hCall : rendezvousDequeuedCall st dequeued = true)
    (hDon : applyRendezvousCallDonation st receiver dequeued = .ok stDon) :
    applyReceiveRendezvousHandoff st receiver dequeued executingCore =
      .ok (applyReceiverPipHandoff stDon receiver executingCore) := by
  unfold applyReceiveRendezvousHandoff
  rw [applyReceiveRendezvousDonation_of_call st receiver dequeued hCall, hDon]
  simp only [hCall, if_true]

/-- **WS-OD OD3.14**: the hand-off decomposes into OD3.6's donation and the
chain walk, so every consumer composes the two existing obligation sets rather
than re-deriving either.

The `if` in the conclusion is the *pre*-state guard, which is what makes this a
decomposition rather than a restatement: a consumer that has already branched on
`rendezvousDequeuedCall` rewrites it away. -/
theorem applyReceiveRendezvousHandoff_ok_decompose (st st'' : SystemState)
    (receiver dequeued : SeLe4n.ThreadId) (executingCore : CoreId)
    (h : applyReceiveRendezvousHandoff st receiver dequeued executingCore = .ok st'') :
    ∃ stDon, applyReceiveRendezvousDonation st receiver dequeued = .ok stDon ∧
      st'' = (if rendezvousDequeuedCall st dequeued then
                applyReceiverPipHandoff stDon receiver executingCore
              else stDon) := by
  unfold applyReceiveRendezvousHandoff at h
  cases hDon : applyReceiveRendezvousDonation st receiver dequeued with
  | error e => rw [hDon] at h; simp only [] at h; cases h
  | ok stDon =>
      rw [hDon] at h
      simp only [Except.ok.injEq] at h
      exact ⟨stDon, rfl, h.symm⟩

/-- WS-OD OD3.14: the hand-off keeps the SM5.H replenish-queue affinity — the
donation does (OD3.6) and the chain walk is a frame over it (RR2.20).

`hObjInvDon` is the object-store invariant *after* the donation; the walk's frame
argument reads it, and `Donation.lean` sits below the module that proves the
donation preserves it, so it is a hypothesis here and discharged at the composite
in `IPC/Invariant/DonationPreservation.lean`. -/
theorem applyReceiveRendezvousHandoff_preserves_replenishQueueAffinityConsistent_smp
    (st st'' : SystemState) (receiver dequeued : SeLe4n.ThreadId) (executingCore : CoreId)
    (hObjInv : st.objects.invExt)
    (hObjInvDon : ∀ stDon, applyReceiveRendezvousDonation st receiver dequeued = .ok stDon →
      stDon.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st)
    (h : applyReceiveRendezvousHandoff st receiver dequeued executingCore = .ok st'') :
    replenishQueueAffinityConsistent_smp st'' := by
  obtain ⟨stDon, hDon, hEq⟩ :=
    applyReceiveRendezvousHandoff_ok_decompose st st'' receiver dequeued executingCore h
  have hConsDon : replenishQueueAffinityConsistent_smp stDon :=
    applyReceiveRendezvousDonation_preserves_replenishQueueAffinityConsistent_smp
      st stDon receiver dequeued hObjInv hCons hDon
  subst hEq
  split
  · exact propagatePipChainCrossCore_preserves_replenishQueueAffinityConsistent_smp
      stDon receiver executingCore _ (hObjInvDon stDon hDon) hConsDon
  · exact hConsDon

/-- **WS-OD OD3.14: the receive leg's priority hand-off on an arm that has
already walked from another thread.**

`.replyRecv` runs two legs and each changes a waiter set: the reply leg removes
the answered caller from the *recorded server*'s, and the receive leg adds the
newly dequeued caller to the *receiver*'s.  A single walk from the recorded
server covers both **exactly when the two threads coincide** — which is every
non-delegated reply, since `recordedReplyServer?` then answers `tid` (and so does
its `.getD tid` default when the reply records no server at all).

On a **delegated** reply they differ, and `blockingServer` does not relate them:
the receiver has just completed a rendezvous, so it is not `.blockedOnReply` on
anything, and the reply leg's upward walk therefore never reaches it.  The newly
dequeued caller's priority is then lost exactly as it was on `.receive` before
OD3.14 — the same defect at a sibling site, which is why it is closed in the same
cut rather than left to read as covered.

`alreadyWalked` is the thread the arm's earlier walk started from, so the gate is
the equality that makes that walk **be** this one, not an enumeration of cases.
The rendezvous guard is read at the state this step runs on, which needs no frame
lemma about the steps between: the question it asks is "is there a caller blocked
on the receiver *here*", and that is the state whose boost is being recomputed. -/
def applyReceiveLegPipHandoff (st : SystemState) (receiver dequeued : SeLe4n.ThreadId)
    (alreadyWalked : SeLe4n.ThreadId) (executingCore : CoreId) : SystemState :=
  if alreadyWalked == receiver then st
  else if rendezvousDequeuedCall st dequeued then
    applyReceiverPipHandoff st receiver executingCore
  else st

/-- WS-OD OD3.14: a **non-delegated** reply changes nothing — the arm's earlier
walk started at the receiver, so this step is the identity and every result taken
before OD3.14 survives verbatim on the states it held for. -/
@[simp] theorem applyReceiveLegPipHandoff_of_not_delegated (st : SystemState)
    (receiver dequeued : SeLe4n.ThreadId) (executingCore : CoreId) :
    applyReceiveLegPipHandoff st receiver dequeued receiver executingCore = st := by
  unfold applyReceiveLegPipHandoff
  simp

/-- WS-OD OD3.14: and so does a delegated reply whose receive leg dequeued no
`Call` — there is no new waiter to carry. -/
@[simp] theorem applyReceiveLegPipHandoff_of_no_call (st : SystemState)
    (receiver dequeued alreadyWalked : SeLe4n.ThreadId) (executingCore : CoreId)
    (h : rendezvousDequeuedCall st dequeued = false) :
    applyReceiveLegPipHandoff st receiver dequeued alreadyWalked executingCore = st := by
  unfold applyReceiveLegPipHandoff
  split
  · rfl
  · simp only [h, Bool.false_eq_true, if_false]

/-- WS-OD OD3.14: the step is either the identity or the chain walk from the
receiver — the disjunction every consumer's frame argument splits on. -/
theorem applyReceiveLegPipHandoff_cases (st : SystemState)
    (receiver dequeued alreadyWalked : SeLe4n.ThreadId) (executingCore : CoreId) :
    applyReceiveLegPipHandoff st receiver dequeued alreadyWalked executingCore = st ∨
    applyReceiveLegPipHandoff st receiver dequeued alreadyWalked executingCore =
      applyReceiverPipHandoff st receiver executingCore := by
  unfold applyReceiveLegPipHandoff
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- WS-OD OD3.14: the receive leg's hand-off keeps SM5.H's replenish-queue
affinity — the identity arm trivially, the walk arm by RR2.20's frame. -/
theorem applyReceiveLegPipHandoff_preserves_replenishQueueAffinityConsistent_smp
    (st : SystemState) (receiver dequeued alreadyWalked : SeLe4n.ThreadId)
    (executingCore : CoreId)
    (hObjInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st) :
    replenishQueueAffinityConsistent_smp
      (applyReceiveLegPipHandoff st receiver dequeued alreadyWalked executingCore) := by
  rcases applyReceiveLegPipHandoff_cases st receiver dequeued alreadyWalked executingCore with
    hEq | hEq <;> rw [hEq]
  · exact hCons
  · exact propagatePipChainCrossCore_preserves_replenishQueueAffinityConsistent_smp
      st receiver executingCore _ hObjInv hCons

end SeLe4n.Kernel
