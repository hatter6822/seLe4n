-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecv
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyDispatchInvariant
import SeLe4n.Kernel.IPC.Invariant
import SeLe4n.Kernel.IPC.Invariant.DonationPreservation
import SeLe4n.Kernel.IPC.Invariant.DispatchArmPreservation
import SeLe4n.Kernel.Scheduler.Invariant
import SeLe4n.Kernel.SchedContext.BindingAffinity

/-!
# Frames and preservation for `endpointReplyRecvOnCore`

The theorems about the live ReplyRecv transition and its two donation halves
(`IPC/CrossCore/EndpointReplyRecv.lean`): the pop's and the post-receive half's
decompositions, object-store and replenish-queue frames, their `ipcInvariantFull`
preservation, the SchedContext hand-off catalogue (`PerCoreDonationStep`,
`donation_perCore_consistent`) and the scheduler-footprint coverage of
`schedLockSet_endpointReplyRecvOnCore`.  The composed transition's
`ipcInvariantFull` preservation is `endpointReplyRecvOnCore_preserves_ipcInvariantFull`
(`IPC/Invariant/DispatchPayoff.lean`), and its per-core confinement and
non-interference are `endpointReplyRecvOnCore_confinedToCores` /
`endpointReplyRecvOnCore_crossCoreNonInterference`
(`InformationFlow/NonInterferenceCrossCore.lean`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (bootCoreId)

/-- The step is the identity when the holder *is* the receiver: the receive leg's
new donation goes to `tid`, so a holder that is the receiver regains a
reservation immediately and must stay runnable. -/
@[simp] theorem replyRecvHolderDeschedule_eq_self_of_receiver (tid holder : SeLe4n.ThreadId)
    (st : SystemState) (h : holder = tid) :
    replyRecvHolderDeschedule tid holder st = st := by
  unfold replyRecvHolderDeschedule; rw [if_pos h]

/-- ...and otherwise it is the placement-resolved deschedule, at the holder. -/
theorem replyRecvHolderDeschedule_eq_deschedule_of_ne (tid holder : SeLe4n.ThreadId)
    (st : SystemState) (h : holder ≠ tid) :
    replyRecvHolderDeschedule tid holder st = descheduleAtPlacement st holder := by
  unfold replyRecvHolderDeschedule; rw [if_neg h]

/-- **WS-RR RR8.12 Cut C6e (frame)**: the deschedule writes run-queue and current
slots, never a replenish queue — which is what lets the post-receive half's
replenish segment be read at the *descheduled* state and still equal the one the
donation migrates between. -/
@[simp] theorem replyRecvHolderDeschedule_replenishQueueOnCore (tid holder : SeLe4n.ThreadId)
    (st : SystemState) (c : Concurrency.CoreId) :
    (replyRecvHolderDeschedule tid holder st).scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
  unfold replyRecvHolderDeschedule
  split
  · rfl
  · exact descheduleAtPlacement_replenishQueueOnCore st holder c

/-- **PR #897 review: the thread the post-receive half deschedules is the one the
pop unbound.**

The pop's result carries `replyFrameHeadHolder?`'s own second component -- the
`boundThread` of the context the answered frame heads -- so the deschedule and the
rebinding are two halves of one resolution rather than two readings that happen to
agree.  That is the relation `recordedReplyServer?` was a proxy for, and the one
HP6.8's splice falsifies: on an orphan head the context's bound thread is not the
server the answered caller recorded, and descheduling the latter strands a
bystander that still holds its own reservation while leaving the former runnable
and unbudgeted. -/
theorem replyRecvPopDonation_holder_eq_frameHead (rid : SeLe4n.ReplyId)
    (target : SeLe4n.ThreadId) (st st' : SystemState)
    (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    (h : replyRecvPopDonation rid target st = .ok (some (scId, holder), st')) :
    replyFrameHeadHolder? st rid = some (scId, holder) := by
  unfold replyRecvPopDonation at h
  cases hHead : replyFrameHeadHolder? st rid with
  | none => rw [hHead] at h; simp at h
  | some pair =>
    obtain ⟨scId0, holder0⟩ := pair
    rw [hHead] at h
    simp only [] at h
    cases hHV : holder0.toValid? with
    | none => rw [hHV] at h; simp only [] at h; cases h
    | some holderV =>
      cases hTV : target.toValid? with
      | none => rw [hHV, hTV] at h; simp only [] at h; cases h
      | some targetV =>
        rw [hHV, hTV] at h
        simp only [] at h
        cases hRet : returnDonatedSchedContextResolved st holder0 scId0
            (replyDonationRecipient st scId0 target) with
        | error e => rw [hRet] at h; simp only [] at h; cases h
        | ok st1' =>
          rw [hRet] at h
          have hPair : some (scId0, holder0) = some (scId, holder) :=
            (by simpa using h : some (scId0, holder0) = some (scId, holder) ∧ _).1
          -- `cases hHead : …` has already rewritten the goal's left-hand side,
          -- so what remains is the pair equality the pop's result carries.
          exact hPair

/-- **WS-RR RR8.12 Cut C2 (`v0.35.162`)**: a pop that hands a context back **is** the
resolved return followed by the SM5.H migration between the holder's home and the
recipient's, both read off the pop's own pre-state — the decomposition the
scheduler-domain footprint's coverage theorem
(`schedLockSet_endpointReplyRecvOnCore_covers_pop`) consumes.  The recipient is
`replyDonationRecipient` (WS-HP HP10.7), the one answer to which thread receives the
context, so the migration's destination and the footprint's cannot differ. -/
theorem replyRecvPopDonation_ok_some_decompose (rid : SeLe4n.ReplyId)
    (target : SeLe4n.ThreadId) (st st' : SystemState)
    (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    (h : replyRecvPopDonation rid target st = .ok (some (scId, holder), st')) :
    ∃ st1', returnDonatedSchedContextResolved st holder scId
        (replyDonationRecipient st scId target) = .ok st1' ∧
      st' = migrateSchedContextReplenishment st1' scId (determineTargetCore st holder)
        (determineTargetCore st (replyDonationRecipient st scId target)) := by
  have hHead := replyRecvPopDonation_holder_eq_frameHead rid target st st' scId holder h
  unfold replyRecvPopDonation at h
  rw [hHead] at h
  simp only [] at h
  cases hHV : holder.toValid? with
  | none => rw [hHV] at h; simp only [] at h; cases h
  | some holderV =>
    cases hTV : target.toValid? with
    | none => rw [hHV, hTV] at h; simp only [] at h; cases h
    | some targetV =>
      rw [hHV, hTV] at h
      simp only [] at h
      cases hRet : returnDonatedSchedContextResolved st holder scId
          (replyDonationRecipient st scId target) with
      | error e => rw [hRet] at h; simp only [] at h; cases h
      | ok st1' =>
        rw [hRet] at h
        simp only [] at h
        exact ⟨st1', rfl, ((Prod.mk.inj (Except.ok.inj h)).2).symm⟩

/-- **WS-RR RR8.12 Cut C2**: and a pop that hands nothing back commits nothing —
the only `none` arm is the identity, so a `.replyRecv` whose answered frame heads no
context runs its receive leg on the reply leg's own post-state.  What licenses the
footprint's empty pop pair. -/
theorem replyRecvPopDonation_ok_none_eq (rid : SeLe4n.ReplyId) (target : SeLe4n.ThreadId)
    (st st' : SystemState)
    (h : replyRecvPopDonation rid target st = .ok (none, st')) : st' = st := by
  unfold replyRecvPopDonation at h
  cases hHead : replyFrameHeadHolder? st rid with
  | none =>
      rw [hHead] at h
      simp only [] at h
      exact ((Prod.mk.inj (Except.ok.inj h)).2).symm
  | some pair =>
    obtain ⟨oldScId, holder⟩ := pair
    rw [hHead] at h
    simp only [] at h
    cases hHV : holder.toValid? with
    | none => rw [hHV] at h; simp only [] at h; cases h
    | some holderV =>
      cases hTV : target.toValid? with
      | none => rw [hHV, hTV] at h; simp only [] at h; cases h
      | some targetV =>
        rw [hHV, hTV] at h
        simp only [] at h
        cases hRet : returnDonatedSchedContextResolved st holder oldScId
            (replyDonationRecipient st oldScId target) with
        | error e => rw [hRet] at h; simp only [] at h; cases h
        | ok st1' =>
          rw [hRet] at h
          simp only [] at h
          exact absurd (Prod.mk.inj (Except.ok.inj h)).1 (by simp)

/-- **WS-RR RR8.12 Cut C6e (the exactness frame)**: the pop writes no replenish
queue outside `replyDonationReturnReplenishCores` — the FOOTPRINT's own first
segment, and the one the `.reply` spine's pop reads too (Cut C3a gave that pair one
owner).

Two branches, both the pop's own.  A frame that heads no context returns nothing,
so the pop is the identity; one that does is the resolved return — a store chain,
so scheduler-silent — followed by the SM5.H migration between exactly the two cores
`replyDonationReturnReplenishCores_of_head` names. -/
theorem replyRecvPopDonation_replenishQueueOnCore_ne (rid : SeLe4n.ReplyId)
    (target : SeLe4n.ThreadId) (st st' : SystemState)
    (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)) (c : Concurrency.CoreId)
    (hne : c ∉ replyDonationReturnReplenishCores st rid target)
    (h : replyRecvPopDonation rid target st = .ok (returned?, st')) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  cases hRet : returned? with
  | none =>
    subst hRet
    rw [replyRecvPopDonation_ok_none_eq rid target st st' h]
  | some pair =>
    obtain ⟨scId, holder⟩ := pair
    subst hRet
    have hHead := replyRecvPopDonation_holder_eq_frameHead rid target st st' scId holder h
    rw [replyDonationReturnReplenishCores_of_head st rid target scId holder hHead] at hne
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hne
    obtain ⟨hFrom, hTo⟩ := hne
    obtain ⟨st1', hResolved, hEq⟩ :=
      replyRecvPopDonation_ok_some_decompose rid target st st' scId holder h
    obtain ⟨newOwner?, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hResolved
    rw [hEq, migrateSchedContextReplenishment_replenishQueueOnCore_other st1' scId
      (determineTargetCore st holder)
      (determineTargetCore st (replyDonationRecipient st scId target)) c
      (Ne.symm hFrom) (Ne.symm hTo),
      returnDonatedSchedContext_scheduler_eq st st1' holder scId
        (replyDonationRecipient st scId target) newOwner? hPop]

/-- **WS-RR RR8.12 Cut C3a**: and it hands nothing back exactly when the answered
frame heads nothing — the `none` result is the trigger's own `none`, which is what
lets the `.replyRecv` footprint's pop component be the frame-keyed
`replyDonationReturnReplenishCores` rather than a second pair keyed on the result.
The other direction is `replyRecvPopDonation_holder_eq_frameHead`. -/
theorem replyRecvPopDonation_ok_none_frameHead (rid : SeLe4n.ReplyId) (target : SeLe4n.ThreadId)
    (st st' : SystemState)
    (h : replyRecvPopDonation rid target st = .ok (none, st')) :
    replyFrameHeadHolder? st rid = none := by
  unfold replyRecvPopDonation at h
  cases hHead : replyFrameHeadHolder? st rid with
  | none => rfl
  | some pair =>
    obtain ⟨oldScId, holder⟩ := pair
    rw [hHead] at h
    simp only [] at h
    cases hHV : holder.toValid? with
    | none => rw [hHV] at h; simp only [] at h; cases h
    | some holderV =>
      cases hTV : target.toValid? with
      | none => rw [hHV, hTV] at h; simp only [] at h; cases h
      | some targetV =>
        rw [hHV, hTV] at h
        simp only [] at h
        cases hRet : returnDonatedSchedContextResolved st holder oldScId
            (replyDonationRecipient st oldScId target) with
        | error e => rw [hRet] at h; simp only [] at h; cases h
        | ok st1' =>
          rw [hRet] at h
          simp only [] at h
          exact absurd (Prod.mk.inj (Except.ok.inj h)).1 (by simp)

/-- **WS-RM (`v0.35.6`)**: the pop preserves object-store integrity — the return
is a store chain over existing keys and the replenishment migration writes no
object at all. -/
theorem replyRecvPopDonation_preserves_objects_invExt (rid : SeLe4n.ReplyId)
    (target : SeLe4n.ThreadId)
    (st st' : SystemState) (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId))
    (hObjInv : st.objects.invExt)
    (hStep : replyRecvPopDonation rid target st = .ok (returned?, st')) :
    st'.objects.invExt := by
  unfold replyRecvPopDonation at hStep
  cases hHead : replyFrameHeadHolder? st rid with
  | none =>
      rw [hHead] at hStep
      exact (by simpa using hStep : none = returned? ∧ st = st').2 ▸ hObjInv
  | some pair =>
    obtain ⟨oldScId, holder⟩ := pair
    rw [hHead] at hStep
    simp only [] at hStep
    cases hHV : holder.toValid? with
    | none => rw [hHV] at hStep; simp only [] at hStep; cases hStep
    | some holderV =>
      cases hTV : target.toValid? with
      | none => rw [hHV, hTV] at hStep; simp only [] at hStep; cases hStep
      | some targetV =>
        rw [hHV, hTV] at hStep
        simp only [] at hStep
        cases hRet : returnDonatedSchedContextResolved st holder oldScId
              (replyDonationRecipient st oldScId target) with
        | error e => rw [hRet] at hStep; simp only [] at hStep; cases hStep
        | ok st1' =>
          rw [hRet] at hStep
          obtain ⟨n, _, hPopN⟩ := returnDonatedSchedContextResolved_ok_decompose hRet
          have hEq : migrateSchedContextReplenishment st1' oldScId
              (determineTargetCore st holder)
                (determineTargetCore st (replyDonationRecipient st oldScId target)) = st' :=
            (by simpa using hStep : some (oldScId, holder) = returned? ∧ _).2
          rw [← hEq, migrateSchedContextReplenishment_objects]
          exact returnDonatedSchedContext_preserves_objects_invExt st st1' _ _ _ hObjInv n hPopN

/-- **WS-RR RR2.20 / WS-RM (`v0.35.6`): the pop restores replenish-queue affinity
consistency on every core.**

The return rebinds the SchedContext from the recorded server to its original
owner, and the SM5.H invariant `replenishQueueAffinityConsistentOnCore` says a
context's CBS replenishments sit on its bound thread's home core — so the return
falsifies it from the instant it commits unless the replenishment migrates with
the binding, which is exactly what this step's second half does.  A same-core
hand-off costs nothing (`migrateSchedContextReplenishment_noop`). -/
theorem replyRecvPopDonation_preserves_replenishQueueAffinityConsistent_smp
    (rid : SeLe4n.ReplyId) (target : SeLe4n.ThreadId) (st st' : SystemState)
    (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId))
    (hObjInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st)
    (h : replyRecvPopDonation rid target st = .ok (returned?, st')) :
    replenishQueueAffinityConsistent_smp st' := by
  unfold replyRecvPopDonation at h
  cases hHead : replyFrameHeadHolder? st rid with
  | none =>
      rw [hHead] at h
      exact (by simpa using h : none = returned? ∧ st = st').2 ▸ hCons
  | some pair =>
    obtain ⟨oldScId, holder⟩ := pair
    rw [hHead] at h
    simp only [] at h
    cases hHV : holder.toValid? with
    | none => rw [hHV] at h; simp only [] at h; cases h
    | some holderV =>
      cases hTV : target.toValid? with
      | none => rw [hHV, hTV] at h; simp only [] at h; cases h
      | some targetV =>
        rw [hHV, hTV] at h
        simp only [] at h
        cases hRet : returnDonatedSchedContextResolved st holder oldScId
            (replyDonationRecipient st oldScId target) with
        | error e =>
            rw [hRet] at h
            simp only [] at h
            cases h
        | ok st1' =>
            rw [hRet] at h
            simp only [] at h
            obtain ⟨n, _, hPopN⟩ := returnDonatedSchedContextResolved_ok_decompose hRet
            have hEq : migrateSchedContextReplenishment st1' oldScId
                (determineTargetCore st holder)
                (determineTargetCore st (replyDonationRecipient st oldScId target)) = st' :=
              (by simpa using h : some (oldScId, holder) = returned? ∧ _).2
            rw [← hEq]
            exact returnDonatedSchedContext_migrate_preserves_replenishQueueAffinityConsistent_smp
              st st1' holder oldScId (replyDonationRecipient st oldScId target) _ _
              hObjInv hCons rfl rfl n hPopN

/-- **WS-RR RR2.20 / WS-RM (`v0.35.6`): the post-receive half restores it too.**
Its re-donation is the third live hand-off, and it migrates its own
replenishments for the same reason; the deschedule and the chain walk write no
replenish queue at all. -/
theorem replyRecvPostReceiveDonation_preserves_replenishQueueAffinityConsistent_smp
    (tid recordedServer nextThread : SeLe4n.ThreadId) (serverCore : Concurrency.CoreId)
    (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)) (st st' : SystemState) (u : Unit)
    (hObjInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st)
    (h : replyRecvPostReceiveDonation tid recordedServer nextThread serverCore returned? st
      = .ok (u, st')) :
    replenishQueueAffinityConsistent_smp st' := by
  have hPip : ∀ (s : SystemState), s.objects.invExt → replenishQueueAffinityConsistent_smp s →
      replenishQueueAffinityConsistent_smp
        (PriorityInheritance.propagatePipChainCrossCore s recordedServer serverCore).1 :=
    fun s hInv hc =>
      propagatePipChainCrossCore_preserves_replenishQueueAffinityConsistent_smp s recordedServer
        serverCore _ hInv hc
  -- ...and the same two facts for the step BOTH arms now run, proved once at
  -- the step itself rather than per core at each consumer (round 11).
  -- **Quantified over the thread** (PR #897 review): both arms deschedule the
  -- HOLDER the pop returned, not `recordedServer`, so a helper fixed at the
  -- latter would not apply to the step either arm runs.
  have hDAInv : ∀ (s : SystemState) (t : SeLe4n.ThreadId), s.objects.invExt →
      (descheduleAtPlacement s t).objects.invExt :=
    fun s t hInv => descheduleAtPlacement_preserves_objects_invExt s t hInv
  have hDA : ∀ (s : SystemState) (t : SeLe4n.ThreadId),
      replenishQueueAffinityConsistent_smp s →
      replenishQueueAffinityConsistent_smp (descheduleAtPlacement s t) :=
    fun s t hc c => (replenishQueueAffinityConsistentOnCore_frame
      (descheduleAtPlacement_replenishQueueOnCore _ _ _)
      (descheduleAtPlacement_preserves_objects _ _)).mpr (hc c)
  unfold replyRecvPostReceiveDonation at h
  cases returned? with
  | none => simp only [] at h; cases h; exact hPip st hObjInv hCons
  | some pair =>
    obtain ⟨_scId, holder⟩ := pair
    simp only [] at h
    cases hCall : rendezvousDequeuedCall st nextThread with
    | false =>
        rw [hCall] at h; simp only [Bool.false_eq_true, if_false] at h; cases h
        exact hPip _ (hDAInv _ _ hObjInv) (hDA _ _ hCons)
    | true =>
        rw [hCall] at h; simp only [if_true] at h
        -- The deschedule runs first on this arm, so the donation's own
        -- hypotheses are discharged at the descheduled state.  Both transport
        -- because `removeRunnableOnCore` writes no object and no replenish queue.
        -- Three branches now, not two: the identity on a non-delegated reply,
        -- the deschedule at the core `placedCoreOf?` resolves, and the identity
        -- again when the server is placed nowhere.  Both facts transport across
        -- all three because `removeRunnableOnCore` writes no object and no
        -- replenish queue whatever core it is given.
        have hSObj : (replyRecvHolderDeschedule tid holder st).objects.invExt := by
          unfold replyRecvHolderDeschedule
          split
          · exact hObjInv
          · exact hDAInv _ _ hObjInv
        have hSCons : replenishQueueAffinityConsistent_smp
            (replyRecvHolderDeschedule tid holder st) := by
          unfold replyRecvHolderDeschedule
          split
          · exact hCons
          · exact hDA _ _ hCons
        cases hDon : applyRendezvousCallDonation
            (replyRecvHolderDeschedule tid holder st) tid nextThread with
        | error e => rw [hDon] at h; simp only [] at h; cases h
        | ok st2 =>
            rw [hDon] at h; simp only [] at h; cases h
            exact hPip _
              (applyRendezvousCallDonation_preserves_objects_invExt _ st2 tid nextThread
                hSObj hDon)
              (applyRendezvousCallDonation_preserves_replenishQueueAffinityConsistent_smp
                _ st2 tid nextThread hSObj hSCons hDon)

/-- **WS-RR RR7.34**: the live SchedContext hand-offs, as one relation.

WS-SM SM6 §4.3 and §10 and WS-SM SM5 §PIP
all name an SM5 theorem `donation_perCore_consistent` — "if the receiver
inherits the SC and is on a different core, the SC's CBS replenish queue
migrates per SM5.H.4" — that existed nowhere.  The *content* did, once per
donation path; what was missing is the statement the catalogue names, over all
of them at once.

Derived rather than listed: a constructor per live hand-off, each carrying that
path's own home-core resolutions, so a further donation path added without a
migration proof cannot be introduced here without extending this relation and
answering `donation_perCore_consistent` for it.  The pre-state affinity
resolutions are hypotheses because each live call site discharges them by `rfl`
from its own pre-state — which is the shape the underlying theorems were stated
in, and the reason they compose.

**WS-RM (`v0.35.6`)**: `.replyRecv`'s resolution is two constructors rather than
one, because the kernel now runs its two halves on either side of the receive
leg (seL4-MCS's own order — see `replyRecvPopDonation`).

**`v0.35.161`**: and "a constructor per live hand-off" was itself a recognised
set standing in for a derived one.  The pre-receive donation return —
`cleanupPreReceiveDonationChecked`, run by the cross-core receive leg's block
path on a `.donated` receiver — rebinds `boundThread` exactly as the four
constructors' pops do, and it was in none of them, so the catalogue said every
hand-off migrates while one live hand-off migrated nothing
(`docs/REGISTERED_DEBT.md` row 57).  The fifth constructor is
`preReceiveReturn`.  The set is still written by hand; what found the fifth was
asking who runs `returnDonatedSchedContext` rather than who is listed here, and a
sixth caller of that pop is a sixth constructor — or, as the cancellation reclaim
has (`cancelIpcBlockingMigrated_establishes_replenishQueueAffinityConsistent_smp`,
stated over the teardown composite rather than here), its own migration theorem,
named where a reader of this relation will find it.

**`v0.35.164`**: the suspend pipeline's G3 donated arm is the other one of that
shape — `cancelDonatedDonationOnCore` (`Lifecycle/Operations/Cleanup.lean`), a
return then a migration, run by the destroy path too since this version — and
it had been migrating since WS-SM SM6.E.3 with neither a constructor here nor a
theorem anywhere.  Its theorem is beside the arm
(`cancelDonatedDonationOnCore_preserves_replenishQueueAffinityConsistent_smp`,
`Lifecycle/Operations/CleanupPreservation.lean`), composed from the general
`migrateSchedContextReplenishment_to_home_preserves_affinityConsistent_smp` as
`preReceiveReturn`'s is. -/
inductive PerCoreDonationStep (st st' : SystemState) : Prop
  /-- The call rendezvous donates the caller's SchedContext to the receiver. -/
  | call (callerVtid receiverVtid : SeLe4n.ValidThreadId)
      (donorHome doneeHome : Concurrency.CoreId)
      (hDonorHome : determineTargetCore st callerVtid.val = donorHome)
      (hDoneeHome : determineTargetCore st receiverVtid.val = doneeHome)
      (hStep : applyCallDonationOnCore st callerVtid receiverVtid donorHome doneeHome = .ok st')
  /-- The reply returns a donated SchedContext to the caller it answers.

  **WS-HP HP4.4**: the two home hypotheses swap conditionality with the trigger
  flip -- the answered caller is the operation's own argument and so the
  *destination*, while the *source* is the holder the head-driven trigger
  resolves.  See `applyReplyDonationOnCore_preserves_replenishQueueAffinityConsistent_smp`
  for why getting this backwards typechecks and migrates the wrong queue. -/
  | reply (rid : SeLe4n.ReplyId) (targetVtid : SeLe4n.ValidThreadId)
      (holderHome ownerHome : Concurrency.CoreId)
      (hHolderHome : ∀ scId holder, replyFrameHeadHolder? st rid = some (scId, holder) →
          determineTargetCore st holder = holderHome)
      -- **WS-HP HP10.7**: the destination is the REDIRECTED recipient, so this is
      -- quantified over the trigger's answer exactly as `hHolderHome` is.  HP4.3
      -- made the two swap conditionality; the redirect makes both conditional,
      -- because the thread that gains the reservation is no longer the argument.
      (hOwnerHome : ∀ scId holder, replyFrameHeadHolder? st rid = some (scId, holder) →
          determineTargetCore st (replyDonationRecipient st scId targetVtid.val) = ownerHome)
      (hStep : applyReplyDonationOnCore st rid targetVtid holderHome ownerHome
          = .ok st')
  /-- `.replyRecv` returns the answered client's context before its receive leg.

  **WS-HP HP4.5**: keyed on the answered frame and the answered caller, like the
  `.reply` arm above -- here the frame needs no resolving, because `rid` is the
  reply capability the arm was invoked with. -/
  | replyRecvPop (rid : SeLe4n.ReplyId) (target : SeLe4n.ThreadId)
      (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId))
      (hStep : replyRecvPopDonation rid target st = .ok (returned?, st'))
  /-- …and donates the next request's context after it. -/
  | replyRecvPostReceive (tid recordedServer nextThread : SeLe4n.ThreadId)
      (serverCore : Concurrency.CoreId) (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)) (u : Unit)
      (hStep : replyRecvPostReceiveDonation tid recordedServer nextThread serverCore returned? st
          = .ok (u, st'))
  /-- **`v0.35.161`**: the cross-core receive leg's block path returns the
  receiver's own donated context to its owner before it parks
  (`cleanupPreReceiveDonationMigrated`) — a hand-off like the four above, since
  the pop rebinds `boundThread`, and one that migrated nothing until this cut.
  It carries no home hypotheses because the migration's destination is read off
  the post-pop state (`replenishHomeOfSchedContext`, WS-RR RR8.11's rule), so a
  refused pop self-migrates to the identity. -/
  | preReceiveReturn (receiver : SeLe4n.ThreadId)
      (hStep : cleanupPreReceiveDonationMigrated st receiver = .ok st')

/-- **WS-RR RR7.34** (WS-SM SM6 §10's SM5 catalogue entry,
authored): **every SchedContext hand-off leaves the replenish queues where the
bound threads are.**

`replenishQueueAffinityConsistent_smp` says a SchedContext's CBS replenishments
sit on its bound thread's home core.  A donation rebinds `boundThread`, so a
cross-core hand-off falsifies it from the instant it commits unless the
replenishment migrates with the binding — which is why every live path calls
`migrateSchedContextReplenishment`, and why a same-core hand-off costs nothing
(`migrateSchedContextReplenishment_noop`).

This is the catalogued statement over every path.  Its proof is the per-path
theorems and nothing else: the aggregation is the content, since a reader
looking for "the donation theorem" found several names and no claim about the
family. -/
theorem donation_perCore_consistent (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st)
    (hStep : PerCoreDonationStep st st') :
    replenishQueueAffinityConsistent_smp st' := by
  cases hStep with
  | call callerVtid receiverVtid donorHome doneeHome hDonorHome hDoneeHome h =>
      exact applyCallDonationOnCore_preserves_replenishQueueAffinityConsistent_smp
        st st' callerVtid receiverVtid donorHome doneeHome hObjInv hCons hDonorHome hDoneeHome h
  | reply rid targetVtid holderHome ownerHome hHolderHome hOwnerHome h =>
      exact applyReplyDonationOnCore_preserves_replenishQueueAffinityConsistent_smp
        st st' rid targetVtid holderHome ownerHome hObjInv hCons hHolderHome
        hOwnerHome h
  | replyRecvPop rid target returned? h =>
      exact replyRecvPopDonation_preserves_replenishQueueAffinityConsistent_smp
        rid target st st' returned? hObjInv hCons h
  | replyRecvPostReceive tid recordedServer nextThread serverCore returned? u h =>
      exact replyRecvPostReceiveDonation_preserves_replenishQueueAffinityConsistent_smp
        tid recordedServer nextThread serverCore returned? st st' u hObjInv hCons h
  | preReceiveReturn receiver h =>
      exact cleanupPreReceiveDonationMigrated_preserves_replenishQueueAffinityConsistent_smp
        st st' receiver hObjInv hCons h

/-- **WS-RM RM5.2**: the pop preserves the IPC invariant bundle.

The first half of what the fused donation resolution used to prove in one piece.
Splitting the fused step (WS-RM) moved the pop *between* the two legs, so the
bundle obligation splits with it, and each half is now stated over the state its
own step runs at rather than over a state two legs away.

`.unbound` and `.bound` are the identity, so the bundle carries through
unchanged.  On `.donated` the step is WS-OD OD3's four-store pop followed by the
SM5.H replenishment migration:

* the pop is `returnDonatedSchedContext_preserves_ipcInvariantFull`, under the
  resolved outer-caller obligation `donationReturnOuterValid` that
  `hStackValid` supplies through `donationReturnOuterValid_of_stackValid`
  (WS-OD OD3.4 -- the pop validates what it hands out, and OD4.3 removed the
  `hBottom` condition that used to confine it to depth 1);
* `passiveServerIdle` needs the holder's own `ipcState` to be one the predicate
  permits, which is `hHolderIdleAllowed`;
* the migration writes only `schedContexts` and the replenishment queue, so it
  is a `descheduleFrame` over an unchanged object store.

**WS-HP HP4.5**: both pre-state conditions are quantified over the head-driven
trigger, exactly as the `.reply` arm's are -- the thread the pop unbinds is read
off `SchedContext.boundThread` rather than supplied, so an unconditional fact
about the operation's argument would be a fact about the wrong thread.
`hHolderDonation` is the binding half, and HP7 (`v0.35.46`) did **not** retire it:
the trigger answers `(context, holder)` off a `.head` link and says nothing about
`holder`'s binding, so this is the one stated fact the head-driven reading still
needs.  What HP7 retired were the binding-driven readings, whose content the trigger
does witness. -/
theorem replyRecvPopDonation_preserves_ipcInvariantFull
    (rid : SeLe4n.ReplyId) (target : SeLe4n.ThreadId) (st st' : SystemState)
    (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId))
    (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st)
    (hHolderDonation : replyFrameHeadHolderDonation st rid target)
    (hHolderIdleAllowed : ∀ scId holder,
        replyFrameHeadHolder? st rid = some (scId, holder) →
        ∀ tcb, st.getTcb? holder = some tcb → passiveServerIdleAllowed tcb.ipcState)
    -- **WS-OD OD4.4**: the return resolves its new owner from the context's reply
    -- stack; this is the obligation that resolution carries.
    (hStackValid : ∀ scId serverTid originalOwner,
        replyStackOuterCallerValid st scId serverTid originalOwner)
    -- **`v0.35.157`**: the origin redirect's coherence obligation -- see
    -- `applyReplyDonation_preserves_ipcInvariantFull`.
    (hOriginCoherent : redirectedOriginFrameCoherent st rid target)
    (h : replyRecvPopDonation rid target st = .ok (returned?, st')) :
    ipcInvariantFull st' := by
  unfold replyRecvPopDonation at h
  cases hHead : replyFrameHeadHolder? st rid with
  | none =>
      rw [hHead] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact h.2 ▸ hInv
  | some pair =>
    obtain ⟨oldScId, holder⟩ := pair
    rw [hHead] at h
    simp only [] at h
    cases hHV : holder.toValid? with
    | none => rw [hHV] at h; simp only [] at h; cases h
    | some holderV =>
      cases hTV : target.toValid? with
      | none => rw [hHV, hTV] at h; simp only [] at h; cases h
      | some targetV =>
        rw [hHV, hTV] at h
        simp only [] at h
        have hHEq : holderV.val = holder :=
          SeLe4n.ThreadId.toValid?_some_val_eq holder holderV hHV
        cases hRet : returnDonatedSchedContextResolved st holder oldScId
            (replyDonationRecipient st oldScId target) with
        | error e =>
            rw [hRet] at h
            simp only [] at h
            cases h
        | ok st1' =>
            rw [hRet] at h
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨n, hResN, hPopN⟩ := returnDonatedSchedContextResolved_ok_decompose hRet
            have hRetW : replyDonationReturn? st holder = some (oldScId, target) :=
              hHolderDonation oldScId holder hHead
            have hRetV : returnDonatedSchedContext st holderV.val oldScId
                (replyDonationRecipient st oldScId target) n = .ok st1' := by
              rw [hHEq]; exact hPopN
            have hRetWV : replyDonationReturn? st holderV.val = some (oldScId, target) := by
              rw [hHEq]; exact hRetW
            have hIdleV : ∀ tcb, st.getTcb? holderV.val = some tcb →
                passiveServerIdleAllowed tcb.ipcState := by
              intro tcb hTcb
              rw [hHEq] at hTcb
              exact hHolderIdleAllowed oldScId holder hHead tcb hTcb
            -- **WS-HP HP10.7**: three cases, as in the `.reply` spine — no origin,
            -- an origin that *is* the answered caller, and a distinct origin, the
            -- last taking the generalised bundle under the redirect's own guard.
            have hInv1' : ipcInvariantFull st1' := by
              by_cases hNoOrigin : donationOriginRecipient? st oldScId = none
              · rw [replyDonationRecipient_eq_of_no_origin st oldScId target hNoOrigin] at hRetV
                exact returnDonatedSchedContext_preserves_ipcInvariantFull st st1' holderV oldScId
                  target hObjInv hInv hRetWV hIdleV n
                  (donationReturnOuterValid_of_stackValid
                    (hStackValid oldScId holderV.val target) hResN) hRetV
              · obtain ⟨o, hOrigin⟩ : ∃ o, donationOriginRecipient? st oldScId = some o := by
                  cases hc : donationOriginRecipient? st oldScId with
                  | none => exact absurd hc hNoOrigin
                  | some o => exact ⟨o, rfl⟩
                have hRecipEq : replyDonationRecipient st oldScId target = o :=
                  replyDonationRecipient_eq_origin st hOrigin
                by_cases hSame : o = target
                · rw [hRecipEq, hSame] at hRetV
                  exact returnDonatedSchedContext_preserves_ipcInvariantFull st st1' holderV oldScId
                    target hObjInv hInv hRetWV hIdleV n
                    (donationReturnOuterValid_of_stackValid
                      (hStackValid oldScId holderV.val target) hResN) hRetV
                · rw [hRecipEq] at hRetV
                  exact returnDonatedSchedContext_establishes_ipcInvariantFull_of_except_redirected
                    st st1' holderV oldScId target o hObjInv
                    (ipcInvariantFullExceptDonationOwner_of_full target hInv) hRetWV
                    (donationOriginRebindable_no_owner
                      (hOriginCoherent oldScId holder o hHead hOrigin hSame)
                      (donationOriginRecipient?_resolves st hOrigin)
                      (donationOriginRecipient?_rebindable st hOrigin))
                    hIdleV n
                    (donationReturnOuterValid_of_stackValid
                      (hStackValid oldScId holderV.val o) hResN) hRetV
            -- The migration is invisible to every bundle reading.
            have hObjsM : (migrateSchedContextReplenishment st1' oldScId
                (determineTargetCore st holder)
                (determineTargetCore st (replyDonationRecipient st oldScId target))).objects
                  = st1'.objects :=
              migrateSchedContextReplenishment_objects st1' oldScId _ _
            have hRqM := migrateSchedContextReplenishment_runQueue_current_eq st1' oldScId
              (determineTargetCore st holder)
                (determineTargetCore st (replyDonationRecipient st oldScId target))
              Concurrency.bootCoreId
            have hInvM : ipcInvariantFull (migrateSchedContextReplenishment st1' oldScId
                (determineTargetCore st holder)
                (determineTargetCore st (replyDonationRecipient st oldScId target))) :=
              ipcInvariantFull_of_descheduleFrame st1' _ hInv1' hObjsM
                (passiveServerIdleFrame.of_objects_scheduler_eq hObjsM hRqM.1 hRqM.2)
            exact h.2 ▸ hInvM

@[simp] theorem replyRecvPostPopState_eq_of_ok (rid : SeLe4n.ReplyId)
    (target : SeLe4n.ThreadId)
    (st1 st1p : SystemState) (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId))
    (h : replyRecvPopDonation rid target st1 = .ok (returned?, st1p)) :
    replyRecvPostPopState rid target st1 = st1p := by
  unfold replyRecvPostPopState; rw [h]

@[simp] theorem replyRecvPoppedDonation_eq_of_ok (rid : SeLe4n.ReplyId)
    (target : SeLe4n.ThreadId)
    (st1 st1p : SystemState) (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId))
    (h : replyRecvPopDonation rid target st1 = .ok (returned?, st1p)) :
    replyRecvPoppedDonation rid target st1 = returned? := by
  unfold replyRecvPoppedDonation; rw [h]

theorem replyRecvPostPopState_eq_of_error (rid : SeLe4n.ReplyId)
    (target : SeLe4n.ThreadId)
    (st1 : SystemState) (e : KernelError)
    (h : replyRecvPopDonation rid target st1 = .error e) :
    replyRecvPostPopState rid target st1 = st1 := by
  unfold replyRecvPostPopState; rw [h]

/-- **WS-RM RM5.2**: the post-receive donation step preserves the IPC invariant
bundle.

The second half of the split.  Three arms, each a result that already exists:

* no context was returned -- the step is the recorded server's
  priority-inheritance chain reversion alone, which
  `propagatePipChainCrossCore_preserves_ipcInvariantFull` covers;
* a context was returned and the receive leg dequeued a `Call` -- the shared
  rendezvous donation (WS-OD OD3.6) re-donates the new client's context, and its
  own bundle lemma discharges the donor-blocked obligation *from* the guard the
  arm branches on (`rendezvousDequeuedCall_blockedOnReply`), so the six-way
  `ipcState` case split collapses to the `Bool` the operation reads;
* a context was returned and nothing rendezvoused -- the **holder** is
  descheduled and then the recorded server is walked, and the deschedule is a
  `descheduleFrame` whose `passiveServerIdle` side condition is exactly
  `hHolderIdleAllowed`.

`hReceiverNotOwner` is stated at *this* step's pre-state (the receive leg's
committed state), not at the reply leg's: the pop no longer runs between them,
so there is nothing to transport it across, and the fused statement's
`hReceiverNotAwaitingReply` -- which existed only to carry it through the pop's
binding trichotomy -- has no subject here.

**`hHolderIdleAllowed` is conditioned on the arm selector** (PR #897 review).  It
was `hServerIdleAllowed`, stated unconditionally at `recordedServer` -- the thread
the step used to deschedule.  Both arms deschedule the holder now, and the holder
exists only on the `some` arm, so the obligation is stated exactly where it
arises: given the pair the pop returned, the thread it names is in a state
`passiveServerIdle` permits.  On the `none` arm nothing is descheduled and the
hypothesis has no premise to discharge. -/
theorem replyRecvPostReceiveDonation_preserves_ipcInvariantFull
    (tid recordedServer nextThread : SeLe4n.ThreadId) (serverCore : Concurrency.CoreId)
    (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId))
    (st st' : SystemState) (u : Unit)
    (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st)
    (hHolderIdleAllowed : ∀ (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId),
        returned? = some (scId, holder) →
        ∀ tcb, st.getTcb? holder = some tcb → passiveServerIdleAllowed tcb.ipcState)
    (hReceiverNotOwner : ∀ (tid' : SeLe4n.ThreadId) (tcb : TCB)
        (scId : SeLe4n.SchedContextId),
        st.getTcb? tid' = some tcb → tcb.schedContextBinding ≠ .donated scId tid)
    (h : replyRecvPostReceiveDonation tid recordedServer nextThread serverCore returned? st
        = .ok (u, st')) :
    ipcInvariantFull st' := by
  unfold replyRecvPostReceiveDonation at h
  cases returned? with
  | none =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact h.2 ▸ propagatePipChainCrossCore_preserves_ipcInvariantFull st recordedServer
        serverCore _ hObjInv hInv
  | some pair =>
    obtain ⟨scIdP, holder⟩ := pair
    have hIdle : ∀ tcb, st.getTcb? holder = some tcb →
        passiveServerIdleAllowed tcb.ipcState := hHolderIdleAllowed scIdP holder rfl
    simp only [] at h
    cases hCall : rendezvousDequeuedCall st nextThread with
    | false =>
        rw [hCall] at h; simp only [Bool.false_eq_true, if_false, Except.ok.injEq,
          Prod.mk.injEq] at h
        -- Both arms run `descheduleAtPlacement` now, so this branch splits on
        -- the resolver exactly as the Call arm below does (round 11) -- and on
        -- the HOLDER, which is the thread the pop unbound (PR #897 review).
        have hDesched : ipcInvariantFull (descheduleAtPlacement st holder) := by
          unfold descheduleAtPlacement descheduleAt
          split
          · rename_i c _
            refine ipcInvariantFull_of_descheduleFrame _ _ hInv
              (removeRunnableOnCore_preserves_objects _ _ _)
              (removeRunnableOnCore_passiveServerIdleFrame _ holder c ?_)
            intro tcb hTcb
            right
            exact hIdle tcb
              ((SystemState.getTcb?_eq_some_iff _ holder tcb).mpr hTcb)
          · exact hInv
        have hDeschedInvExt : (descheduleAtPlacement st holder).objects.invExt :=
          descheduleAtPlacement_preserves_objects_invExt st holder hObjInv
        exact h.2 ▸ propagatePipChainCrossCore_preserves_ipcInvariantFull _ recordedServer
          serverCore _ hDeschedInvExt hDesched
    | true =>
        rw [hCall] at h; simp only [if_true] at h
        -- The deschedule runs first on this arm.  It writes no object, so the
        -- donation's object-level hypotheses transport verbatim; what it does
        -- write is the run queue, which is the `descheduleFrame` the false arm
        -- below already discharges from `hServerIdleAllowed`.
        have hObjEq : (replyRecvHolderDeschedule tid holder st).objects
            = st.objects := by
          unfold replyRecvHolderDeschedule
          split
          · rfl
          · exact descheduleAtPlacement_preserves_objects _ _
        have hSObj : (replyRecvHolderDeschedule tid holder st).objects.invExt := by
          rw [hObjEq]; exact hObjInv
        have hSInv : ipcInvariantFull
            (replyRecvHolderDeschedule tid holder st) := by
          unfold replyRecvHolderDeschedule descheduleAtPlacement descheduleAt
          split
          · exact hInv
          · split
            · rename_i c _
              refine ipcInvariantFull_of_descheduleFrame _ _ hInv
                (removeRunnableOnCore_preserves_objects _ _ _)
                (removeRunnableOnCore_passiveServerIdleFrame _ holder c ?_)
              intro tcb hTcb
              right
              exact hIdle tcb
                ((SystemState.getTcb?_eq_some_iff _ holder tcb).mpr hTcb)
            · exact hInv
        have hSNotOwner : ∀ (tid' : SeLe4n.ThreadId) (tcb : TCB)
            (scId : SeLe4n.SchedContextId),
            (replyRecvHolderDeschedule tid holder st).getTcb? tid'
              = some tcb → tcb.schedContextBinding ≠ .donated scId tid := by
          intro tid' tcb scId hTcb
          refine hReceiverNotOwner tid' tcb scId ?_
          rw [SystemState.getTcb?_eq_some_iff] at hTcb ⊢
          rw [hObjEq] at hTcb
          exact hTcb
        cases hDon : applyRendezvousCallDonation
            (replyRecvHolderDeschedule tid holder st) tid nextThread with
        | error e => rw [hDon] at h; simp only [] at h; cases h
        | ok st2 =>
            rw [hDon] at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h
            -- The guard reads a TCB, and the deschedule writes no object, so the
            -- arm the donation takes is the arm the guard selected.
            have hCallD : rendezvousDequeuedCall
                (replyRecvHolderDeschedule tid holder st) nextThread = true := by
              unfold rendezvousDequeuedCall at hCall ⊢
              rw [lookupTcb_congr_getElem (s1 := st)
                (s2 := replyRecvHolderDeschedule tid holder st)
                (fun k => by rw [hObjEq]) nextThread]
              exact hCall
            have hStep : applyReceiveRendezvousDonation
                (replyRecvHolderDeschedule tid holder st)
                tid nextThread = .ok st2 := by
              unfold applyReceiveRendezvousDonation
              rw [hCallD]
              simpa using hDon
            have hInv2 : ipcInvariantFull st2 :=
              applyReceiveRendezvousDonation_preserves_ipcInvariantFull _ st2
                tid nextThread hSObj hSInv hSNotOwner hStep
            have hObjInv2 : st2.objects.invExt :=
              applyReceiveRendezvousDonation_preserves_objects_invExt _ st2 tid
                nextThread hSObj hStep
            exact h.2 ▸ propagatePipChainCrossCore_preserves_ipcInvariantFull st2
              recordedServer serverCore _ hObjInv2 hInv2

@[simp] theorem replyRecvPostReceiveReplenishCores_none (tid nextThread : SeLe4n.ThreadId)
    (st : SystemState) :
    replyRecvPostReceiveReplenishCores tid nextThread none st = [] := rfl

theorem replyRecvPostReceiveReplenishCores_of_no_call (tid nextThread : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId) (st : SystemState)
    (h : rendezvousDequeuedCall st nextThread = false) :
    replyRecvPostReceiveReplenishCores tid nextThread (some (scId, holder)) st = [] := by
  unfold replyRecvPostReceiveReplenishCores
  simp [h]

theorem replyRecvPostReceiveReplenishCores_of_call (tid nextThread : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId) (st : SystemState)
    (h : rendezvousDequeuedCall st nextThread = true) :
    replyRecvPostReceiveReplenishCores tid nextThread (some (scId, holder)) st
      = rendezvousCallDonationReplenishCores (replyRecvHolderDeschedule tid holder st)
          tid nextThread := by
  unfold replyRecvPostReceiveReplenishCores
  simp [h]

/-- The segment once the reply leg and the pop have run: the pop's pair, the
block-path pair at the pop's post-state, and the post-receive pair under the receive
leg's own match.  The one unfolding every consumer reads. -/
theorem replyRecvHandoffReplenishCores_eq_of_pop (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId)
    (msg : IpcMessage) (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : Concurrency.CoreId) (st st1 st1p : SystemState)
    (sgi : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId))
    (hReply : endpointReplyOnCore receiver prevCaller msg executingCore st = (st1, .ok sgi))
    (hPop : replyRecvPopDonation replyId prevCaller st1 = .ok (returned?, st1p)) :
    replyRecvHandoffReplenishCores endpointId receiver replyId prevCaller msg receiverCspaceRoot
        receiverSlotBase executingCore st
      = replyDonationReturnReplenishCores st1 replyId prevCaller ++
          (receivePreReturnReplenishCores st1p endpointId receiver ++
            (match endpointReceiveDualWithCapsOnCore endpointId receiver (some replyId)
                receiverCspaceRoot receiverSlotBase executingCore st1p with
             | (_, .error _) => []
             | (st2, .ok (nextThread, _, _)) =>
                replyRecvPostReceiveReplenishCores receiver nextThread returned? st2)) := by
  unfold replyRecvHandoffReplenishCores
  simp only [hReply, hPop]
  rfl

/-- ...and once the receive leg has run too, the third component is the post-receive
pair at that leg's post-state. -/
theorem replyRecvHandoffReplenishCores_eq_of_legs (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId)
    (msg : IpcMessage) (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : Concurrency.CoreId) (st st1 st1p st2 : SystemState)
    (sgi sgi2 : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId))
    (nextThread : SeLe4n.ThreadId) (summary : CapTransferSummary)
    (hReply : endpointReplyOnCore receiver prevCaller msg executingCore st = (st1, .ok sgi))
    (hPop : replyRecvPopDonation replyId prevCaller st1 = .ok (returned?, st1p))
    (hRecv : endpointReceiveDualWithCapsOnCore endpointId receiver (some replyId)
        receiverCspaceRoot receiverSlotBase executingCore st1p
      = (st2, .ok (nextThread, summary, sgi2))) :
    replyRecvHandoffReplenishCores endpointId receiver replyId prevCaller msg receiverCspaceRoot
        receiverSlotBase executingCore st
      = replyDonationReturnReplenishCores st1 replyId prevCaller ++
          (receivePreReturnReplenishCores st1p endpointId receiver ++
            replyRecvPostReceiveReplenishCores receiver nextThread returned? st2) := by
  rw [replyRecvHandoffReplenishCores_eq_of_pop endpointId receiver replyId prevCaller msg
    receiverCspaceRoot receiverSlotBase executingCore st st1 st1p sgi returned? hReply hPop]
  simp only [hRecv]

/-- **WS-RR RR8.12 Cut C2**: the reply leg's wake — the answered caller's home
core — is a run-queue write member, unconditionally: it is the head of the arm's
own write set. -/
theorem schedLockSet_endpointReplyRecvOnCore_contains_prevCaller_runQueue_write
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId)
    (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage) (receiverCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : Concurrency.CoreId) (st : SystemState) :
    (SchedLockId.runQueue ⟨determineTargetCore st prevCaller⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_endpointReplyRecvOnCore endpointId receiver replyId prevCaller msg
          receiverCspaceRoot receiverSlotBase executingCore st := by
  refine (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr ?_
  unfold endpointReplyRecvWriteSet
  exact List.mem_cons_self ..

/-- **WS-RR RR8.12 Cut C2**: every core the receive leg writes — resolved at the
pop's post-state, the state that leg runs on — is a run-queue write member. -/
theorem schedLockSet_endpointReplyRecvOnCore_covers_receiveLeg
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId)
    (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage) (receiverCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : Concurrency.CoreId)
    (st st1 st1p : SystemState) (sgi : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId))
    (hReply : endpointReplyOnCore receiver prevCaller msg executingCore st = (st1, .ok sgi))
    (hPop : replyRecvPopDonation replyId prevCaller st1 = .ok (returned?, st1p)) :
    ∀ c ∈ endpointReceiveDualWriteSet st1p endpointId executingCore,
      (SchedLockId.runQueue ⟨c⟩, Concurrency.AccessMode.write)
        ∈ schedLockSet_endpointReplyRecvOnCore endpointId receiver replyId prevCaller msg
            receiverCspaceRoot receiverSlotBase executingCore st := by
  intro c hc
  refine (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr ?_
  unfold endpointReplyRecvWriteSet
  simp only [hReply, hPop, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inl hc)

/-- **WS-RR RR8.12 Cut C2 (coverage, the pop)**: the `.replyRecv` footprint covers the
pop's migration footprint member for member — at the two cores the pop's migration
is actually stated at (`replyRecvPopDonation_ok_some_decompose`, read through the
frame the pop resolves, `replyRecvPopDonation_holder_eq_frameHead`), on the reply
leg's post-state, which is the state the pop runs on.  A `withLockSet` bracket over this
footprint therefore holds both slots the pop migrates between.  Conditioned on the
pop having handed a context back, because that is the only shape on which there is
a migration to cover. -/
theorem schedLockSet_endpointReplyRecvOnCore_covers_pop
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId)
    (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage) (receiverCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : Concurrency.CoreId)
    (st st1 st1p : SystemState) (sgi : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    (hReply : endpointReplyOnCore receiver prevCaller msg executingCore st = (st1, .ok sgi))
    (hPop : replyRecvPopDonation replyId prevCaller st1 = .ok (some (scId, holder), st1p)) :
    ∀ p ∈ migrateSchedContextReplenishmentLockSet (determineTargetCore st1 holder)
             (determineTargetCore st1 (replyDonationRecipient st1 scId prevCaller)),
      p ∈ schedLockSet_endpointReplyRecvOnCore endpointId receiver replyId prevCaller msg
            receiverCspaceRoot receiverSlotBase executingCore st := by
  intro p hp
  simp only [migrateSchedContextReplenishmentLockSet, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  have hSeg := replyRecvHandoffReplenishCores_eq_of_pop endpointId receiver replyId prevCaller msg
    receiverCspaceRoot receiverSlotBase executingCore st st1 st1p sgi _ hReply hPop
  have hPair := replyDonationReturnReplenishCores_of_head st1 replyId prevCaller scId holder
    (replyRecvPopDonation_holder_eq_frameHead replyId prevCaller st1 st1p scId holder hPop)
  rcases hp with h | h <;> subst h <;>
  · refine (mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mpr ?_
    rw [hSeg, hPair]
    simp

/-- **WS-RR RR8.12 Cut C2 (coverage, the block path)**: on a receive leg that blocks
holding a loan, the footprint covers the pre-receive return's migration footprint
member for member — at the cores the migration actually resolves on the post-pop
state it runs on (`receivePreReturnReplenishCores_eq_migration`).  The `.replyRecv`
sibling of `schedLockSet_endpointReceiveOnCore_covers_preReturnMigration`, read at
the state the arm's receive leg runs on rather than at the syscall's pre-state,
because that is where this arm's leg runs.  Conditioned on the pop's OWN guard and
on the pop having committed, as its sibling is. -/
theorem schedLockSet_endpointReplyRecvOnCore_covers_preReturnMigration
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId)
    (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage) (receiverCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : Concurrency.CoreId)
    (st st1 st1p stClean : SystemState) (sgi : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId))
    (ep : Endpoint) (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId)
    (hReply : endpointReplyOnCore receiver prevCaller msg executingCore st = (st1, .ok sgi))
    (hPop : replyRecvPopDonation replyId prevCaller st1 = .ok (returned?, st1p))
    (hObjInv : st1p.objects.invExt)
    (hEp : st1p.getEndpoint? endpointId = some ep) (hHead : ep.sendQ.head = none)
    (hDon : preReceiveDonation? st1p receiver = some (scId, owner))
    (hClean : cleanupPreReceiveDonationChecked st1p receiver = .ok stClean) :
    ∀ p ∈ migrateSchedContextReplenishmentLockSet (determineTargetCore st1p receiver)
             (replenishHomeOfSchedContext stClean scId (determineTargetCore st1p receiver)),
      p ∈ schedLockSet_endpointReplyRecvOnCore endpointId receiver replyId prevCaller msg
            receiverCspaceRoot receiverSlotBase executingCore st := by
  intro p hp
  simp only [migrateSchedContextReplenishmentLockSet, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  have hSeg := replyRecvHandoffReplenishCores_eq_of_pop endpointId receiver replyId prevCaller msg
    receiverCspaceRoot receiverSlotBase executingCore st st1 st1p sgi returned? hReply hPop
  have hPre := receivePreReturnReplenishCores_eq_migration st1p stClean endpointId receiver scId
    owner hObjInv (receiveRendezvousSender?_of_blocked st1p endpointId ep hEp hHead) hDon hClean
  rcases hp with h | h <;> subst h <;>
  · refine (mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mpr ?_
    rw [hSeg, hPre]
    simp

/-- **WS-RR RR8.12 Cut C2 (coverage, the re-donation)**: on a receive leg that
dequeues a `Call` after the pop handed a context back, the footprint covers WS-OD
OD3.6's donation footprint member for member — hence, by
`applyCallDonationOnCoreSchedLockSet_covers_migration`, the SM5.H migration's two
replenish-queue write locks — at the cores the donation **actually** resolves, on the
post-deschedule state it runs on, under the donation's OWN resolver
(`applyRendezvousCallDonation_ok_migrates` is the licence that those are the
migration's endpoints).  Conditioned on all three of the arm's own gates, because
those are the only shapes on which there is a migration to cover; a coverage claim
elsewhere would be covering nothing while reading like coverage. -/
theorem schedLockSet_endpointReplyRecvOnCore_covers_postReceiveDonation
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId)
    (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage) (receiverCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : Concurrency.CoreId)
    (st st1 st1p st2 : SystemState) (sgi sgi2 : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (scId0 scId : SeLe4n.SchedContextId) (holder nextThread : SeLe4n.ThreadId)
    (summary : CapTransferSummary)
    (hReply : endpointReplyOnCore receiver prevCaller msg executingCore st = (st1, .ok sgi))
    (hPop : replyRecvPopDonation replyId prevCaller st1 = .ok (some (scId0, holder), st1p))
    (hRecv : endpointReceiveDualWithCapsOnCore endpointId receiver (some replyId)
        receiverCspaceRoot receiverSlotBase executingCore st1p
      = (st2, .ok (nextThread, summary, sgi2)))
    (hCall : rendezvousDequeuedCall st2 nextThread = true)
    (hDon : callDonationSchedContext? (replyRecvHolderDeschedule receiver holder st2)
        nextThread receiver = some scId) :
    ∀ p ∈ applyCallDonationOnCoreSchedLockSet
             (determineTargetCore (replyRecvHolderDeschedule receiver holder st2) nextThread)
             (determineTargetCore (replyRecvHolderDeschedule receiver holder st2) receiver),
      p ∈ schedLockSet_endpointReplyRecvOnCore endpointId receiver replyId prevCaller msg
            receiverCspaceRoot receiverSlotBase executingCore st := by
  have hSeg := replyRecvHandoffReplenishCores_eq_of_legs endpointId receiver replyId prevCaller
    msg receiverCspaceRoot receiverSlotBase executingCore st st1 st1p st2 sgi sgi2 _ nextThread
    summary hReply hPop hRecv
  refine schedFootprintOfCores_subset (fun _ h => absurd h (by simp)) (fun c hc => ?_)
  rw [hSeg, replyRecvPostReceiveReplenishCores_of_call receiver nextThread scId0 holder st2 hCall,
    rendezvousCallDonationReplenishCores_of_donation _ receiver nextThread scId hDon]
  simp only [List.mem_append]
  exact Or.inr (Or.inr hc)

/-- **WS-RR RR8.12 Cut C2**: where no hand-off fires — the pop handed nothing back
and the receive leg's block path returns no loan — the segment is empty, so the
footprint is the table lock and the run queues alone.  The post-receive half needs
no hypothesis: with nothing handed back it walks and never donates. -/
theorem replyRecvHandoffReplenishCores_of_no_donation (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId)
    (msg : IpcMessage) (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : Concurrency.CoreId) (st st1 st1p : SystemState)
    (sgi : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (hReply : endpointReplyOnCore receiver prevCaller msg executingCore st = (st1, .ok sgi))
    (hPop : replyRecvPopDonation replyId prevCaller st1 = .ok (none, st1p))
    (hPre : receivePreReturn? st1p endpointId receiver = none) :
    replyRecvHandoffReplenishCores endpointId receiver replyId prevCaller msg receiverCspaceRoot
      receiverSlotBase executingCore st = [] := by
  rw [replyRecvHandoffReplenishCores_eq_of_pop endpointId receiver replyId prevCaller msg
    receiverCspaceRoot receiverSlotBase executingCore st st1 st1p sgi none hReply hPop,
    replyDonationReturnReplenishCores_of_no_head st1 replyId prevCaller
      (replyRecvPopDonation_ok_none_frameHead replyId prevCaller st1 st1p hPop),
    receivePreReturnReplenishCores_of_none st1p endpointId
    receiver hPre, List.nil_append, List.nil_append]
  split <;> rfl

/-- **WS-RR RR8.12 Cut C2 (the empty segment)**: a `.replyRecv` that hands nothing
back and returns no loan declares **no** replenish-queue lock — over-declaring is
sound and not free (SM8.D's CC-5), and
`endpointReplyRecvOnCore_replenishQueueOnCore_of_no_donation` is the licence that the
transition writes none there either. -/
theorem schedLockSet_endpointReplyRecvOnCore_no_replenishQueue_of_no_donation
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId)
    (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage) (receiverCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : Concurrency.CoreId)
    (st st1 st1p : SystemState) (sgi : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (hReply : endpointReplyOnCore receiver prevCaller msg executingCore st = (st1, .ok sgi))
    (hPop : replyRecvPopDonation replyId prevCaller st1 = .ok (none, st1p))
    (hPre : receivePreReturn? st1p endpointId receiver = none) (c : Concurrency.CoreId) :
    (SchedLockId.replenishQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∉ schedLockSet_endpointReplyRecvOnCore endpointId receiver replyId prevCaller msg
          receiverCspaceRoot receiverSlotBase executingCore st := by
  intro hMem
  have := (mem_schedFootprintOfCores_replenishQueue_iff _ _ c).mp hMem
  rw [replyRecvHandoffReplenishCores_of_no_donation endpointId receiver replyId prevCaller msg
    receiverCspaceRoot receiverSlotBase executingCore st st1 st1p sgi hReply hPop hPre] at this
  simp at this

/-- **WS-RR RR8.12 Cut C2 (frame)**: the receive leg writes no replenish queue where
`receivePreReturn?` answers `none` — on a rendezvous (the leg itself donates
nothing; the arm's donation is a later step), on a block by a receiver holding no
loan, and on an endpoint the store does not resolve (the leg commits nothing).  The
resolver's `none` is exactly the disjunction of the frames the leg already has. -/
theorem endpointReceiveDualWithCapsOnCore_replenishQueueOnCore_of_no_preReturn
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (hPre : receivePreReturn? st endpointId receiver = none) (c : Concurrency.CoreId) :
    (endpointReceiveDualWithCapsOnCore endpointId receiver replyId receiverCspaceRoot
        receiverSlotBase executingCore st).1.scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
  unfold receivePreReturn? at hPre
  cases hEp : st.getEndpoint? endpointId with
  | none =>
      rw [endpointReceiveDualWithCapsOnCore_scheduler_eq,
        endpointReceiveDualOnCore_state_of_no_endpoint endpointId receiver replyId executingCore
          st hEp]
  | some ep =>
      cases hHead : ep.sendQ.head with
      | some sender =>
          exact endpointReceiveDualWithCapsOnCore_replenishQueueOnCore_of_rendezvous endpointId
            receiver replyId receiverCspaceRoot receiverSlotBase executingCore st ep sender hEp
            hHead c
      | none =>
          have hSender : receiveRendezvousSender? st endpointId = none := by
            unfold receiveRendezvousSender?; rw [hEp]; exact hHead
          rw [hSender] at hPre
          simp only [] at hPre
          have hNoDon : preReceiveDonation? st receiver = none := by
            cases hP : preReceiveDonation? st receiver with
            | none => rfl
            | some pr =>
                obtain ⟨scId, owner⟩ := pr
                have h := endpointReplyDonation?_of_preReceiveDonation? st receiver scId owner hP
                rw [hPre] at h
                cases h
          exact endpointReceiveDualWithCapsOnCore_replenishQueueOnCore_of_no_donation endpointId
            receiver replyId receiverCspaceRoot receiverSlotBase executingCore st ep hEp hHead
            hNoDon c

/-- The post-receive half's never-donated arm is the chain walk from the recorded
server, and nothing else. -/
theorem replyRecvPostReceiveDonation_ok_none_eq (tid recordedServer nextThread : SeLe4n.ThreadId)
    (serverCore : Concurrency.CoreId) (st st' : SystemState) (u : Unit)
    (h : replyRecvPostReceiveDonation tid recordedServer nextThread serverCore none st
      = .ok (u, st')) :
    st' = (PriorityInheritance.propagatePipChainCrossCore st recordedServer serverCore).1 := by
  unfold replyRecvPostReceiveDonation at h
  simp only [] at h
  exact ((Prod.mk.inj (Except.ok.inj h)).2).symm

/-- ...so it writes no replenish queue (WS-RR RR2.20's frame over the walk)... -/
theorem replyRecvPostReceiveDonation_replenishQueueOnCore_of_none
    (tid recordedServer nextThread : SeLe4n.ThreadId) (serverCore : Concurrency.CoreId)
    (st st' : SystemState) (u : Unit) (hObjInv : st.objects.invExt)
    (h : replyRecvPostReceiveDonation tid recordedServer nextThread serverCore none st
      = .ok (u, st')) (c : Concurrency.CoreId) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  rw [replyRecvPostReceiveDonation_ok_none_eq tid recordedServer nextThread serverCore st st' u h]
  exact (PriorityInheritance.propagatePipChainCrossCore_replenish_readings st recordedServer
    serverCore _ hObjInv).1 c

/-- **WS-RR RR8.12 Cut C6e (the exactness frame)**: the post-receive half writes no
replenish queue outside `replyRecvPostReceiveReplenishCores` — the FOOTPRINT's own
third segment, keyed on it rather than on which arm the half took.

Three branches, each the definition's own.  The never-donated arm is the chain walk,
which writes run queues and no replenish queue.  The donated-but-no-new-Call arm is
the holder's deschedule and the walk, which write neither.  And the re-donation arm
is the deschedule, then `applyRendezvousCallDonation` at exactly the cores the
segment names — read at the *descheduled* state, as the segment reads them, which is
sound because the deschedule writes no replenish queue
(`replyRecvHolderDeschedule_replenishQueueOnCore`) — then the walk. -/
theorem replyRecvPostReceiveDonation_replenishQueueOnCore_ne
    (tid recordedServer nextThread : SeLe4n.ThreadId) (serverCore : Concurrency.CoreId)
    (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId))
    (st st' : SystemState) (u : Unit) (c : Concurrency.CoreId) (hObjInv : st.objects.invExt)
    (hne : c ∉ replyRecvPostReceiveReplenishCores tid nextThread returned? st)
    (h : replyRecvPostReceiveDonation tid recordedServer nextThread serverCore returned? st
      = .ok (u, st')) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  cases hRet : returned? with
  | none =>
    subst hRet
    exact replyRecvPostReceiveDonation_replenishQueueOnCore_of_none tid recordedServer nextThread
      serverCore st st' u hObjInv h c
  | some pair =>
    obtain ⟨scId, holder⟩ := pair
    subst hRet
    have hDesch : ∀ d, (replyRecvHolderDeschedule tid holder st).scheduler.replenishQueueOnCore d
        = st.scheduler.replenishQueueOnCore d := fun d =>
      replyRecvHolderDeschedule_replenishQueueOnCore tid holder st d
    unfold replyRecvPostReceiveDonation at h
    simp only [] at h
    by_cases hCall : rendezvousDequeuedCall st nextThread
    · rw [if_pos hCall] at h
      have hSeg : replyRecvPostReceiveReplenishCores tid nextThread (some (scId, holder)) st
          = rendezvousCallDonationReplenishCores (replyRecvHolderDeschedule tid holder st) tid
              nextThread := by
        simp only [replyRecvPostReceiveReplenishCores, if_pos hCall]
      rw [hSeg] at hne
      cases hDon : applyRendezvousCallDonation (replyRecvHolderDeschedule tid holder st) tid
          nextThread with
      | error e => rw [hDon] at h; simp only [] at h; cases h
      | ok st2 =>
        rw [hDon] at h
        simp only [] at h
        have hEq : (PriorityInheritance.propagatePipChainCrossCore st2 recordedServer
            serverCore).1 = st' := ((Prod.mk.inj (Except.ok.inj h)).2)
        rw [← hEq]
        have hInv2 : st2.objects.invExt := by
          have hI1 : (replyRecvHolderDeschedule tid holder st).objects.invExt := by
            unfold replyRecvHolderDeschedule
            split
            · exact hObjInv
            · exact descheduleAtPlacement_preserves_objects_invExt st holder hObjInv
          exact applyRendezvousCallDonation_preserves_objects_invExt _ st2 tid nextThread hI1 hDon
        rw [(PriorityInheritance.propagatePipChainCrossCore_replenish_readings st2 recordedServer
          serverCore _ hInv2).1 c,
          applyRendezvousCallDonation_replenishQueueOnCore_ne _ st2 tid nextThread c hne hDon,
          hDesch c]
    · rw [if_neg hCall] at h
      have hEq : (PriorityInheritance.propagatePipChainCrossCore
          (descheduleAtPlacement st holder) recordedServer serverCore).1 = st' :=
        ((Prod.mk.inj (Except.ok.inj h)).2)
      rw [← hEq,
        (PriorityInheritance.propagatePipChainCrossCore_replenish_readings _ recordedServer
          serverCore _ (descheduleAtPlacement_preserves_objects_invExt st holder hObjInv)).1 c,
        descheduleAtPlacement_replenishQueueOnCore]


/-- ...and keeps object-store integrity, which the walk after it reads. -/
theorem replyRecvPostReceiveDonation_preserves_objects_invExt_of_none
    (tid recordedServer nextThread : SeLe4n.ThreadId) (serverCore : Concurrency.CoreId)
    (st st' : SystemState) (u : Unit) (hObjInv : st.objects.invExt)
    (h : replyRecvPostReceiveDonation tid recordedServer nextThread serverCore none st
      = .ok (u, st')) :
    st'.objects.invExt := by
  rw [replyRecvPostReceiveDonation_ok_none_eq tid recordedServer nextThread serverCore st st' u h]
  exact PriorityInheritance.propagatePipChainCrossCore_preserves_objects_invExt st recordedServer
    serverCore _ hObjInv

/-- **WS-RR RR8.12 Cut C6e**: the post-receive half keeps object-store integrity on
**every** arm, which is what the walk after it and the `.replyRecv` composite's own
frames read.  The `_of_none` sibling below is this at `returned? = none`; it was the
only form the tree had, so a composite that did not know which arm the half took
could not carry `invExt` past it at all. -/
theorem replyRecvPostReceiveDonation_preserves_objects_invExt
    (tid recordedServer nextThread : SeLe4n.ThreadId) (serverCore : Concurrency.CoreId)
    (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId))
    (st st' : SystemState) (u : Unit) (hObjInv : st.objects.invExt)
    (h : replyRecvPostReceiveDonation tid recordedServer nextThread serverCore returned? st
      = .ok (u, st')) :
    st'.objects.invExt := by
  cases hRet : returned? with
  | none =>
    subst hRet
    exact replyRecvPostReceiveDonation_preserves_objects_invExt_of_none tid recordedServer
      nextThread serverCore st st' u hObjInv h
  | some pair =>
    obtain ⟨scId, holder⟩ := pair
    subst hRet
    have hDeschInv : (replyRecvHolderDeschedule tid holder st).objects.invExt := by
      unfold replyRecvHolderDeschedule
      split
      · exact hObjInv
      · exact descheduleAtPlacement_preserves_objects_invExt st holder hObjInv
    unfold replyRecvPostReceiveDonation at h
    simp only [] at h
    by_cases hCall : rendezvousDequeuedCall st nextThread
    · rw [if_pos hCall] at h
      cases hDon : applyRendezvousCallDonation (replyRecvHolderDeschedule tid holder st) tid
          nextThread with
      | error e => rw [hDon] at h; simp only [] at h; cases h
      | ok st2 =>
        rw [hDon] at h
        simp only [] at h
        have hEq : (PriorityInheritance.propagatePipChainCrossCore st2 recordedServer
            serverCore).1 = st' := ((Prod.mk.inj (Except.ok.inj h)).2)
        rw [← hEq]
        exact PriorityInheritance.propagatePipChainCrossCore_preserves_objects_invExt st2
          recordedServer serverCore _
          (applyRendezvousCallDonation_preserves_objects_invExt _ st2 tid nextThread hDeschInv hDon)
    · rw [if_neg hCall] at h
      have hEq : (PriorityInheritance.propagatePipChainCrossCore
          (descheduleAtPlacement st holder) recordedServer serverCore).1 = st' :=
        ((Prod.mk.inj (Except.ok.inj h)).2)
      rw [← hEq]
      exact PriorityInheritance.propagatePipChainCrossCore_preserves_objects_invExt _
        recordedServer serverCore _
        (descheduleAtPlacement_preserves_objects_invExt st holder hObjInv)


/-- **WS-RR RR8.12 Cut C2 (the exactness licence)**: where the segment is empty —
the pop handed nothing back and the receive leg's block path returns no loan — the
live `.replyRecv` writes **no** replenish queue on any core.  The composition a
bracket consumer cites: the reply leg's wake is a run-queue insert
(`endpointReplyOnCore_replenishQueueOnCore`), a pop that returns nothing is the
identity (`replyRecvPopDonation_ok_none_eq`), the receive leg is a frame on both its
paths (`endpointReceiveDualWithCapsOnCore_replenishQueueOnCore_of_no_preReturn`), the
post-receive half's never-donated arm is the chain walk, which is a frame
(`propagatePipChainCrossCore_replenish_readings`), the receive leg's hand-off is the
identity or another walk (`applyReceiveLegPipHandoff_cases`), and the two stagers
write registers only.

**This theorem also pins a divergence the register records** (the WS-CB
passive/legacy row): on a `.replyRecv` whose pop returned nothing, a dequeued `Call`
caller's context is NOT donated to an `.unbound` receiver — the never-donated arm
walks only — where seL4-MCS's `receiveIPC` and this kernel's own `.receive` arm
would donate.  A cut that makes that arm donate widens the segment
(`replyRecvPostReceiveReplenishCores`'s `none` arm) and breaks this theorem, which is
the intended coupling: the footprint and the transition move together or not at
all. -/
theorem endpointReplyRecvOnCore_replenishQueueOnCore_of_no_donation
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId)
    (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage) (receiverCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : Concurrency.CoreId)
    (st st1 st1p st2 st3 stOut : SystemState) (sgi sgi2 : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (nextThread : SeLe4n.ThreadId) (summary summary' : CapTransferSummary)
    (hObjInv : st.objects.invExt)
    (hReply : endpointReplyOnCore receiver prevCaller msg executingCore st = (st1, .ok sgi))
    (hPop : replyRecvPopDonation replyId prevCaller st1 = .ok (none, st1p))
    (hRecv : endpointReceiveDualWithCapsOnCore endpointId receiver (some replyId)
        receiverCspaceRoot receiverSlotBase executingCore st1p
      = (st2, .ok (nextThread, summary, sgi2)))
    (hPre : receivePreReturn? st1p endpointId receiver = none)
    (hPost : replyRecvPostReceiveDonation receiver ((recordedReplyServer? st prevCaller).getD receiver)
        nextThread executingCore
        none st2 = .ok ((), st3))
    (hBody : endpointReplyRecvOnCore endpointId receiver replyId prevCaller msg receiverCspaceRoot
        receiverSlotBase executingCore st = .ok (summary', stOut))
    (c : Concurrency.CoreId) :
    stOut.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  -- the pop hands nothing back, so it commits nothing
  have hPopEq : st1p = st1 := replyRecvPopDonation_ok_none_eq replyId prevCaller st1 st1p hPop
  rw [hPopEq] at hPop hRecv hPre
  -- object-store integrity along the spine, for the two walks' frames
  have hInv1 : st1.objects.invExt := by
    have h := endpointReplyOnCore_preserves_objects_invExt receiver prevCaller msg executingCore
      st hObjInv
    rw [hReply] at h; exact h
  have hInv2 : st2.objects.invExt := by
    have h := endpointReceiveDualWithCapsOnCore_preserves_objects_invExt endpointId receiver
      (some replyId) receiverCspaceRoot receiverSlotBase executingCore st1 hInv1
    rw [hRecv] at h; exact h
  have hInv3 : st3.objects.invExt :=
    replyRecvPostReceiveDonation_preserves_objects_invExt_of_none _ _ _ _ st2 st3 () hInv2 hPost
  -- the legs' frames
  have hR1 : st1.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
    have h := endpointReplyOnCore_replenishQueueOnCore receiver prevCaller msg executingCore st c
    rw [hReply] at h; exact h
  have hR2 : st2.scheduler.replenishQueueOnCore c = st1.scheduler.replenishQueueOnCore c := by
    have h := endpointReceiveDualWithCapsOnCore_replenishQueueOnCore_of_no_preReturn endpointId
      receiver (some replyId) receiverCspaceRoot receiverSlotBase executingCore st1 hPre c
    rw [hRecv] at h; exact h
  have hR3 : st3.scheduler.replenishQueueOnCore c = st2.scheduler.replenishQueueOnCore c :=
    replyRecvPostReceiveDonation_replenishQueueOnCore_of_none _ _ _ _ st2 st3 () hInv2 hPost c
  -- the body's post-state is the stagers over the hand-off over `st3`
  unfold endpointReplyRecvOnCore at hBody
  simp only [hReply, hPop, hRecv, hPost] at hBody
  have hOut := (Prod.mk.inj (Except.ok.inj hBody)).2
  rw [← hOut, Architecture.stageWokenSendCompletion_scheduler_eq,
    Architecture.stageDeliveredMessage_scheduler_eq]
  rcases applyReceiveLegPipHandoff_cases st3 receiver nextThread
      ((recordedReplyServer? st prevCaller).getD receiver) executingCore with hH | hH
  · rw [hH, hR3, hR2, hR1]
  · rw [hH]
    unfold applyReceiverPipHandoff
    rw [(PriorityInheritance.propagatePipChainCrossCore_replenish_readings st3 receiver
      executingCore st3.objectIndex.length hInv3).1 c, hR3, hR2, hR1]


/-- **WS-RR RR8.12 Cut C6e (the exactness frame)**: the live `.replyRecv` arm
writes no replenish queue outside `replyRecvHandoffReplenishCores` — the
FOOTPRINT's own segment, with no hypothesis about which path any of the four
stages took.

The `_of_no_donation` sibling above says the arm migrates *nothing* where all
three hand-offs decline; this says *where* it migrates when they answer, which is
what the replenish clause of `schedFootprintCoversWrites` needs.  Each stage's own
`_ne` is stated at the very sub-segment the definition appends at that stage — the
pop's pair, the block path's pair, the re-donation's pair — so this proof is the
composition `replyRecvHandoffReplenishCores_eq_of_legs` already names rather than a
second reading of the arm.  The tail (the priority hand-off and the two stagers)
writes run queues and register contexts and no replenish queue at all. -/
theorem endpointReplyRecvOnCore_replenishQueueOnCore_ne
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId)
    (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage) (receiverCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : Concurrency.CoreId)
    (st stOut : SystemState) (summary' : CapTransferSummary) (c : Concurrency.CoreId)
    (hObjInv : st.objects.invExt)
    (hne : c ∉ replyRecvHandoffReplenishCores endpointId receiver replyId prevCaller msg
      receiverCspaceRoot receiverSlotBase executingCore st)
    (hBody : endpointReplyRecvOnCore endpointId receiver replyId prevCaller msg receiverCspaceRoot
        receiverSlotBase executingCore st = .ok (summary', stOut)) :
    stOut.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold endpointReplyRecvOnCore at hBody
  cases hReply : endpointReplyOnCore receiver prevCaller msg executingCore st with
  | mk st1 res1 =>
    rw [hReply] at hBody
    cases res1 with
    | error e => simp only [] at hBody; cases hBody
    | ok replySgi =>
      simp only [] at hBody
      have hR1 : st1.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
        have h := endpointReplyOnCore_replenishQueueOnCore receiver prevCaller msg executingCore
          st c
        rw [hReply] at h; exact h
      have hInv1 : st1.objects.invExt := by
        have h := endpointReplyOnCore_preserves_objects_invExt receiver prevCaller msg
          executingCore st hObjInv
        rw [hReply] at h; exact h
      cases hPop : replyRecvPopDonation replyId prevCaller st1 with
      | error e => rw [hPop] at hBody; simp only [] at hBody; cases hBody
      | ok popPair =>
        obtain ⟨returned?, st1p⟩ := popPair
        rw [hPop] at hBody
        simp only [] at hBody
        cases hRecv : endpointReceiveDualWithCapsOnCore endpointId receiver (some replyId)
            receiverCspaceRoot receiverSlotBase executingCore st1p with
        | mk st2 res2 =>
          rw [hRecv] at hBody
          cases res2 with
          | error e => simp only [] at hBody; cases hBody
          | ok triple =>
            obtain ⟨nextThread, summary, sgi2⟩ := triple
            simp only [] at hBody
            -- The segment, decomposed at the two legs the definition reads it through.
            rw [replyRecvHandoffReplenishCores_eq_of_legs endpointId receiver replyId prevCaller
              msg receiverCspaceRoot receiverSlotBase executingCore st st1 st1p st2 replySgi sgi2
              returned? nextThread summary hReply hPop hRecv] at hne
            simp only [List.mem_append, not_or] at hne
            obtain ⟨hnePop, hnePre, hnePost⟩ := hne
            have hInv1p : st1p.objects.invExt :=
              replyRecvPopDonation_preserves_objects_invExt replyId prevCaller st1 st1p returned?
                hInv1 hPop
            have hInv2 : st2.objects.invExt := by
              have h := endpointReceiveDualWithCapsOnCore_preserves_objects_invExt endpointId
                receiver (some replyId) receiverCspaceRoot receiverSlotBase executingCore st1p
                hInv1p
              rw [hRecv] at h; exact h
            have hR1p : st1p.scheduler.replenishQueueOnCore c
                = st1.scheduler.replenishQueueOnCore c :=
              replyRecvPopDonation_replenishQueueOnCore_ne replyId prevCaller st1 st1p returned? c
                hnePop hPop
            have hR2 : st2.scheduler.replenishQueueOnCore c
                = st1p.scheduler.replenishQueueOnCore c :=
              endpointReceiveDualWithCapsOnCore_replenishQueueOnCore_ne endpointId receiver
                (some replyId) receiverCspaceRoot receiverSlotBase executingCore st1p st2
                nextThread summary sgi2 c hInv1p hnePre hRecv
            cases hPost : replyRecvPostReceiveDonation receiver
                ((recordedReplyServer? st prevCaller).getD receiver) nextThread
                executingCore
                returned? st2 with
            | error e => rw [hPost] at hBody; simp only [] at hBody; cases hBody
            | ok p3 =>
              obtain ⟨u, st3⟩ := p3
              rw [hPost] at hBody
              simp only [] at hBody
              have hR3 : st3.scheduler.replenishQueueOnCore c
                  = st2.scheduler.replenishQueueOnCore c :=
                replyRecvPostReceiveDonation_replenishQueueOnCore_ne receiver
                  ((recordedReplyServer? st prevCaller).getD receiver) nextThread
                  executingCore
                  returned? st2 st3 u c hInv2 hnePost hPost
              have hInv3 : st3.objects.invExt :=
                replyRecvPostReceiveDonation_preserves_objects_invExt receiver
                  ((recordedReplyServer? st prevCaller).getD receiver) nextThread
                  executingCore
                  returned? st2 st3 u hInv2 hPost
              have hOut := (Prod.mk.inj (Except.ok.inj hBody)).2
              rw [← hOut, Architecture.stageWokenSendCompletion_scheduler_eq,
                Architecture.stageDeliveredMessage_scheduler_eq]
              rcases applyReceiveLegPipHandoff_cases st3 receiver nextThread
                  ((recordedReplyServer? st prevCaller).getD receiver) executingCore with hH | hH
              · rw [hH, hR3, hR2, hR1p, hR1]
              · rw [hH]
                unfold applyReceiverPipHandoff
                rw [(PriorityInheritance.propagatePipChainCrossCore_replenish_readings st3 receiver
                  executingCore st3.objectIndex.length hInv3).1 c, hR3, hR2, hR1p, hR1]


/-- **WS-RR RR8.12 Cut C6f (the exactness frame)**: the `.receive` arm's leg and
WS-OD OD3.6 donation write no replenish queue outside
`endpointReceiveHandoffReplenishCores` — the FOOTPRINT's own segment, keyed on it
rather than on which of the arm's three shapes the state takes.

The claim is about the leg **composed with the donation** and not with the chain
walk: the walk's cores are state-discovered and are declared dynamically through
`pipChainSchedFootprint`, which is why `.receive` is the one declared arm whose
walk sits outside its run segment.

`queueHeadBlockedConsistent` is the one invariant this needs, and it is needed for
exactly one corner: a rendezvous whose sender is *not* a `Call` yet whose
`callDonationSchedContext?` answers `some`.  There the segment is empty and the
donation must be shown inert, which is
`endpointReceiveDualWithCapsOnCore_not_dequeuedCall_of_blockedOnSend` — stated at
`.blockedOnSend` rather than at "not a `Call`" for the reason its own docstring
gives, and that conjunct is what says `.blockedOnSend` is the reachable non-`Call`
shape for a send queue's head. -/
theorem endpointReceiveLegAndDonation_replenishQueueOnCore_ne (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : Concurrency.CoreId) (st st1 stDon : SystemState) (dequeued : SeLe4n.ThreadId)
    (summary : CapTransferSummary) (sgi : Option (Concurrency.CoreId × Concurrency.SgiKind)) (c : Concurrency.CoreId)
    (hObjInv : st.objects.invExt) (hHeads : queueHeadBlockedConsistent st)
    (hne : c ∉ endpointReceiveHandoffReplenishCores st endpointId receiver)
    (hLeg : endpointReceiveDualWithCapsOnCore endpointId receiver replyId receiverCspaceRoot
      receiverSlotBase executingCore st = (st1, .ok (dequeued, summary, sgi)))
    (hDon : applyReceiveRendezvousDonation st1 receiver dequeued = .ok stDon) :
    stDon.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  cases hSender : receiveRendezvousSender? st endpointId with
  | none =>
    -- The BLOCK path: the leg dequeued nobody and reports the receiver's own id,
    -- and a thread donates nothing to itself.
    have hDq : dequeued = receiver :=
      endpointReceiveDualWithCapsOnCore_ok_dequeued_eq_receiver_of_blocked endpointId receiver
        replyId receiverCspaceRoot receiverSlotBase executingCore st st1 dequeued summary sgi
        hSender hLeg
    subst hDq
    have hCallSender : receiveRendezvousCallSender? st endpointId = none := by
      unfold receiveRendezvousCallSender?
      rw [hSender]
      rfl
    have hDonating : receiveRendezvousDonatingSender? st endpointId dequeued = none :=
      receiveRendezvousDonatingSender?_of_no_callSender st endpointId dequeued hCallSender
    have hLegNe : c ∉ receivePreReturnReplenishCores st endpointId dequeued := by
      rw [show endpointReceiveHandoffReplenishCores st endpointId dequeued
            = receivePreReturnReplenishCores st endpointId dequeued by
          unfold endpointReceiveHandoffReplenishCores; rw [hDonating]] at hne
      exact hne
    have hR1 := endpointReceiveDualWithCapsOnCore_replenishQueueOnCore_ne endpointId dequeued
      replyId receiverCspaceRoot receiverSlotBase executingCore st st1 dequeued summary sgi c
      hObjInv hLegNe hLeg
    have hSeg : rendezvousCallDonationReplenishCores st1 dequeued dequeued = [] :=
      rendezvousCallDonationReplenishCores_of_no_donation st1 dequeued dequeued
        (callDonationSchedContext?_self st1 dequeued)
    rw [applyReceiveRendezvousDonation_replenishQueueOnCore_ne st1 stDon dequeued dequeued c
      (by rw [hSeg]; simp) hDon, hR1]
  | some sender =>
    -- The RENDEZVOUS paths: the leg reports the send queue's head.
    obtain ⟨ep, hEp, hHead⟩ : ∃ ep, st.getEndpoint? endpointId = some ep ∧
        ep.sendQ.head = some sender := by
      unfold receiveRendezvousSender? at hSender
      cases hE : st.getEndpoint? endpointId with
      | none => rw [hE] at hSender; simp at hSender
      | some ep => rw [hE] at hSender; exact ⟨ep, rfl, hSender⟩
    have hDq : dequeued = sender :=
      endpointReceiveDualWithCapsOnCore_ok_dequeued_eq_head endpointId receiver replyId
        receiverCspaceRoot receiverSlotBase executingCore st st1 dequeued summary sgi ep sender
        hEp hHead hLeg
    subst hDq
    -- A rendezvous returns no loan, so the leg's own segment is empty.
    have hR1 := endpointReceiveDualWithCapsOnCore_replenishQueueOnCore_ne endpointId receiver
      replyId receiverCspaceRoot receiverSlotBase executingCore st st1 dequeued summary sgi c
      hObjInv
      (by rw [receivePreReturnReplenishCores_of_sender st endpointId receiver dequeued hSender]
          simp)
      hLeg
    rw [← hR1]
    cases hDonPost : callDonationSchedContext? st1 dequeued receiver with
    | none =>
      exact applyReceiveRendezvousDonation_replenishQueueOnCore_ne st1 stDon receiver dequeued c
        (by rw [rendezvousCallDonationReplenishCores_of_no_donation st1 receiver dequeued hDonPost]
            simp)
        hDon
    | some scId =>
      have hBindFrame := endpointReceiveDualWithCapsOnCore_sameSchedContextBindings_of_rendezvous
        endpointId receiver replyId receiverCspaceRoot receiverSlotBase executingCore st ep
        dequeued hObjInv hEp hHead
      rw [hLeg] at hBindFrame
      have hDonPre : callDonationSchedContext? st dequeued receiver = some scId :=
        callDonationSchedContext?_some_of_sameSchedContextBindings hBindFrame dequeued receiver
          scId hDonPost
      by_cases hIsCall : rendezvousSenderIsCall st dequeued
      · -- A donating `Call` rendezvous: the segment names the pair, at the pre-state,
        -- and the leg moves no thread's home core.
        have hDonating : receiveRendezvousDonatingSender? st endpointId receiver = some dequeued :=
          receiveRendezvousDonatingSender?_of_donation st endpointId receiver dequeued scId
            (by unfold receiveRendezvousCallSender?; rw [hSender]; simp only [Option.bind_some,
              if_pos hIsCall]) hDonPre
        rw [show endpointReceiveHandoffReplenishCores st endpointId receiver
              = [determineTargetCore st dequeued, determineTargetCore st receiver] by
            unfold endpointReceiveHandoffReplenishCores; rw [hDonating]] at hne
        have hHome : ∀ x, determineTargetCore st1 x = determineTargetCore st x := fun x => by
          have h := endpointReceiveDualWithCapsOnCore_determineTargetCore_eq_of_rendezvous
            endpointId receiver replyId receiverCspaceRoot receiverSlotBase executingCore st ep
            dequeued x hObjInv hEp hHead
          rw [hLeg] at h
          exact h
        have hSeg : rendezvousCallDonationReplenishCores st1 receiver dequeued
            = [determineTargetCore st dequeued, determineTargetCore st receiver] := by
          unfold rendezvousCallDonationReplenishCores
          rw [hDonPost, hHome dequeued, hHome receiver]
        exact applyReceiveRendezvousDonation_replenishQueueOnCore_ne st1 stDon receiver dequeued c
          (by rw [hSeg]; exact hne) hDon
      · -- A rendezvous whose sender is not a `Call`: the post-state guard is false,
        -- so the donation is the identity however the resolver answers.
        -- The donation resolver answered `some`, so it resolved the caller too.
        obtain ⟨senderTcb, hTcb⟩ : ∃ t, lookupTcb st dequeued = some t := by
          cases hT : lookupTcb st dequeued with
          | none =>
            exfalso
            unfold callDonationSchedContext? at hDonPre
            simp only [hT] at hDonPre
            repeat' split at hDonPre
            all_goals simp at hDonPre
          | some t => exact ⟨t, rfl⟩
        have hTcbObj : st.objects[dequeued.toObjId]? = some (.tcb senderTcb) := by
          unfold lookupTcb at hTcb
          split at hTcb
          · exact absurd hTcb (by simp)
          · exact (SystemState.getTcb?_eq_some_iff st dequeued senderTcb).mp hTcb
        have hEpObj : st.objects[endpointId]? = some (.endpoint ep) :=
          (SystemState.getEndpoint?_eq_some_iff st endpointId ep).mp hEp
        have hShape := (hHeads endpointId ep dequeued senderTcb hEpObj hTcbObj).2 hHead
        have hSend : senderTcb.ipcState = .blockedOnSend endpointId := by
          rcases hShape with h | h
          · exact h
          · exact absurd (by unfold rendezvousSenderIsCall; rw [hTcb]; simp only [h]) hIsCall
        have hGuard := endpointReceiveDualWithCapsOnCore_not_dequeuedCall_of_blockedOnSend
          endpointId receiver replyId receiverCspaceRoot receiverSlotBase executingCore st ep
          dequeued senderTcb endpointId hObjInv hEp hHead hTcb hSend
        rw [hLeg] at hGuard
        unfold applyReceiveRendezvousDonation at hDon
        rw [hGuard] at hDon
        simp only [Bool.false_eq_true, if_false] at hDon
        rw [(Except.ok.inj hDon).symm]


-- ============================================================================
-- Audit IPC-2 (`v0.36.49`): object-store integrity and observer atomicity of the
-- live ReplyRecv
-- ============================================================================
--
-- These two restate, for the transition the `.replyRecv` arm runs, the two facts
-- the deleted two-leg composite carried (`…_preserves_objects_invExt`,
-- `…_observer_atomic`).  Every leg's frame is unconditional, so the composite's
-- is too.

/-- **Audit IPC-2**: the live ReplyRecv preserves object-store integrity — each
of its five steps and both return-frame stagers do. -/
theorem endpointReplyRecvOnCore_preserves_objects_invExt (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId)
    (msg : IpcMessage) (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : Concurrency.CoreId) (st st' : SystemState) (summary : CapTransferSummary)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReplyRecvOnCore endpointId receiver replyId prevCaller msg
        receiverCspaceRoot receiverSlotBase executingCore st = .ok (summary, st')) :
    st'.objects.invExt := by
  have hInv1 := endpointReplyOnCore_preserves_objects_invExt receiver prevCaller msg
    executingCore st hObjInv
  unfold endpointReplyRecvOnCore at hStep
  simp only [] at hStep
  cases hRep : endpointReplyOnCore receiver prevCaller msg executingCore st with
  | mk st1 res =>
    rw [hRep] at hInv1 hStep
    cases res with
    | error e => exact absurd hStep (by simp)
    | ok _ =>
      simp only [] at hStep
      cases hPop : replyRecvPopDonation replyId prevCaller st1 with
      | error e => rw [hPop] at hStep; exact absurd hStep (by simp)
      | ok popPair =>
        obtain ⟨returnedSc?, st1p⟩ := popPair
        rw [hPop] at hStep
        simp only [] at hStep
        have hInv1p : st1p.objects.invExt :=
          replyRecvPopDonation_preserves_objects_invExt replyId prevCaller st1 st1p
            returnedSc? hInv1 hPop
        have hInv2 := endpointReceiveDualWithCapsOnCore_preserves_objects_invExt endpointId
          receiver (some replyId) receiverCspaceRoot receiverSlotBase executingCore st1p hInv1p
        cases hRcv : endpointReceiveDualWithCapsOnCore endpointId receiver (some replyId)
            receiverCspaceRoot receiverSlotBase executingCore st1p with
        | mk st2 res2 =>
          rw [hRcv] at hInv2 hStep
          cases res2 with
          | error e => simp only [] at hStep; exact absurd hStep (by simp)
          | ok pair =>
            rcases pair with ⟨nextThread, recvSummary, recvSgi⟩
            simp only [] at hStep
            cases hDon : replyRecvPostReceiveDonation receiver
                ((recordedReplyServer? st prevCaller).getD receiver) nextThread
                executingCore returnedSc? st2 with
            | error e => rw [hDon] at hStep; exact absurd hStep (by simp)
            | ok pair2 =>
              rcases pair2 with ⟨u2, st3⟩
              rw [hDon] at hStep
              simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
              rw [← hStep.2]
              have hInv3 := replyRecvPostReceiveDonation_preserves_objects_invExt receiver
                ((recordedReplyServer? st prevCaller).getD receiver) nextThread executingCore
                returnedSc? st2 st3 u2 hInv2 hDon
              exact stageWokenSendCompletion_objects_invExt _ _
                (stageDeliveredMessage_preserves_objects_invExt _ _ _
                  (applyReceiveLegPipHandoff_preserves_objects_invExt _ _ _ _ _ hInv3))

open SeLe4n.Kernel.Concurrency in
/-- **Audit IPC-2**: under the `.replyRecv` footprint the live ReplyRecv is
observationally atomic to any thread's IPC state — the field both legs write.

The transition is `Kernel`-shaped (a failure carries no state), so the 2PL
bracket runs its state-threading form: the post-state on success, the input
state on failure.  The lock-set arguments are the full `lockSet_replyRecv`
arity, so the claim covers every footprint the arm can declare. -/
theorem endpointReplyRecvOnCore_observer_atomic
    (endpointId : SeLe4n.ObjId) (receiver prevCaller : SeLe4n.ThreadId) (msg : IpcMessage)
    (replyId : SeLe4n.ReplyId) (receiverCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : Concurrency.CoreId)
    (cnRoot : SeLe4n.ObjId) (newSender? : Option SeLe4n.ThreadId)
    (donatedSc? : Option SeLe4n.SchedContextId) (donatedOwner? : Option SeLe4n.ThreadId)
    (observed : SeLe4n.ThreadId) (installsCaps : Bool)
    (donationServer? : Option SeLe4n.ThreadId) (redonatedSc? : Option SeLe4n.SchedContextId)
    (belowHeadReply? : Option SeLe4n.ReplyId) (outerCaller? : Option SeLe4n.ThreadId)
    (queueNeighbour? : Option SeLe4n.ThreadId)
    (redonationOldHead? donatedHead? : Option SeLe4n.ReplyId)
    (preReturnSc? : Option SeLe4n.SchedContextId) (preReturnOwner? : Option SeLe4n.ThreadId)
    (preReturnHead? preReturnBelowHead? : Option SeLe4n.ReplyId)
    (preReturnOuterCaller? : Option SeLe4n.ThreadId)
    (answeredFrameAbove? answeredFrameBelow? : Option SeLe4n.ReplyId)
    (originRecipient? : Option SeLe4n.ThreadId)
    (s : SystemState) (hInv : s.objects.invExt) :
    let S := lockSet_replyRecv receiver cnRoot prevCaller endpointId newSender? donatedSc?
      donatedOwner? (some replyId) installsCaps donationServer? redonatedSc?
      belowHeadReply? outerCaller? queueNeighbour? redonationOldHead? donatedHead?
      preReturnSc? preReturnOwner? preReturnHead? preReturnBelowHead?
      preReturnOuterCaller? answeredFrameAbove? answeredFrameBelow? originRecipient?
    let action : SystemState → SystemState × Except KernelError CapTransferSummary :=
      fun s' => match endpointReplyRecvOnCore endpointId receiver replyId prevCaller msg
          receiverCspaceRoot receiverSlotBase executingCore s' with
        | .ok (r, s'') => (s'', .ok r)
        | .error e => (s', .error e)
    threadIpcStateObserver observed
        (acquireAll executingCore S.lockAcquireSequence s)
      = threadIpcStateObserver observed s
    ∧ threadIpcStateObserver observed (withLockSet S executingCore action s).1
      = threadIpcStateObserver observed
          (action (acquireAll executingCore S.lockAcquireSequence s)).1 := by
  intro S action
  refine lockSet_observer_atomic_of_objectStoreObserver S executingCore action s _
    (threadIpcStateObserver_insensitiveOn executingCore observed) hInv ?_
  intro s' h
  show (match endpointReplyRecvOnCore endpointId receiver replyId prevCaller msg
          receiverCspaceRoot receiverSlotBase executingCore s' with
        | .ok (r, s'') => (s'', Except.ok r)
        | .error e => (s', .error e)).1.objects.invExt
  cases hStep : endpointReplyRecvOnCore endpointId receiver replyId prevCaller msg
      receiverCspaceRoot receiverSlotBase executingCore s' with
  | error e => exact h
  | ok pair =>
    obtain ⟨r, s''⟩ := pair
    exact endpointReplyRecvOnCore_preserves_objects_invExt endpointId receiver replyId
      prevCaller msg receiverCspaceRoot receiverSlotBase executingCore s' s'' r h hStep


end SeLe4n.Kernel
