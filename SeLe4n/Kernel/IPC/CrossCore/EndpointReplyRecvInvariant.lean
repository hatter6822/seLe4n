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
non-interference are `endpointReplyRecvOnCore_confinedToCores`
(`SlotConfinement/IpcArms.lean`, production since WS-LS LS2.3) /
`endpointReplyRecvOnCore_crossCoreNonInterference`
(`InformationFlow/NonInterferenceCrossCore.lean`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (bootCoreId
  LockKey)

-- ============================================================================
-- The answer to the replied-to caller (`replyRecvAnswerCaller`): its frames
-- ============================================================================

/-- Answering the caller preserves object-store integrity, on both answers. -/
theorem replyRecvAnswerCaller_preserves_objects_invExt
    (answer : Option Architecture.FaultReplyOutcome) (st : SystemState)
    (prevCaller : SeLe4n.ThreadId) (capInfo : Nat) (hObjInv : st.objects.invExt) :
    (replyRecvAnswerCaller answer st prevCaller capInfo).objects.invExt := by
  cases answer with
  | none => exact stageDeliveredMessage_objects_invExt _ _ _ hObjInv
  | some outcome =>
    cases outcome with
    | restart frame => exact applyFaultRestart_preserves_objects_invExt _ _ _ hObjInv
    | abandon => exact faultAbandonOnCore_preserves_objects_invExt _ _ _ hObjInv

/-- Answering the caller writes no replenish queue: the staging and a restart write
registers, an abandon deschedules. -/
theorem replyRecvAnswerCaller_replenishQueueOnCore
    (answer : Option Architecture.FaultReplyOutcome) (st : SystemState)
    (prevCaller : SeLe4n.ThreadId) (capInfo : Nat) (c : Concurrency.CoreId) :
    (replyRecvAnswerCaller answer st prevCaller capInfo).scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
  cases answer with
  | none => rw [replyRecvAnswerCaller_none, Architecture.stageDeliveredMessage_scheduler_eq]
  | some outcome => exact faultReplyApplyOnCore_replenishQueueOnCore st prevCaller outcome c

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
  | none => rw [hHead] at h; simp only [] at h; split at h <;> simp at h
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
        split at h
        rotate_left
        · split at h <;> simp at h
        cases hRet : returnDonatedSchedContextResolved st holder0 scId0
            target with
        | error e => rw [hRet] at h; simp only [] at h; cases h
        | ok st1' =>
          rw [hRet] at h
          have hPair : some (scId0, holder0) = some (scId, holder) :=
            (by simpa using h : some (scId0, holder0) = some (scId, holder) ∧ _).1
          -- `cases hHead : …` has already rewritten the goal's left-hand side,
          -- so what remains is the pair equality the pop's result carries.
          exact hPair

/-- **WS-RR RR8.12 Cut C2 (`v0.35.162`)**: a pop that hands a context back **is** the
resolved return followed by the settle of the returned context on the recipient's
home (WS-ZA ZA6.33), read off the pop's own pre-state — the decomposition the
scheduler-domain footprint's coverage theorem
(`schedLockSet_endpointReplyRecvOnCore_covers_pop`) consumes.  The recipient is
the answered caller (seL4-MCS `reply_pop`; WS-SX SX12, D31), so the settle's
destination and the footprint's cannot differ. -/
theorem replyRecvPopDonation_ok_some_decompose (rid : SeLe4n.ReplyId)
    (target : SeLe4n.ThreadId) (st st' : SystemState)
    (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    (h : replyRecvPopDonation rid target st = .ok (some (scId, holder), st')) :
    ∃ st1', returnDonatedSchedContextResolved st holder scId
        target = .ok st1' ∧
      st' = SchedContextOps.settleReturnedContext st1'
        (determineTargetCore st target) scId := by
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
      split at h
      rotate_left
      · split at h <;> simp at h
      cases hRet : returnDonatedSchedContextResolved st holder scId
          target with
      | error e => rw [hRet] at h; simp only [] at h; cases h
      | ok st1' =>
        rw [hRet] at h
        simp only [] at h
        exact ⟨st1', rfl, ((Prod.mk.inj (Except.ok.inj h)).2).symm⟩

/-- **WS-ZA ZA6.34: a pop that hands no context back** is the pop at an unheld
head — the frame resolves no holder, and the pop of the context it heads, if any,
as seL4-MCS's `reply_pop` runs it with no thread losing a context — or the held
pop whose recipient holds a context of its own (`keepDonatedSchedContext`), where
the context stays with its holder.  The identity where the frame heads nothing
(`replyRecvPopDonation_ok_none_eq`). -/
theorem replyRecvPopDonation_ok_none_decompose (rid : SeLe4n.ReplyId) (target : SeLe4n.ThreadId)
    (st st' : SystemState)
    (h : replyRecvPopDonation rid target st = .ok (none, st')) :
    (replyFrameHeadHolder? st rid = none ∧
      popUnheldReplyHead st rid target (determineTargetCore st target) = .ok st') ∨
    ∃ scId holder, replyFrameHeadHolder? st rid = some (scId, holder) ∧
      donationRecipientAcceptable st target = false ∧
      keepDonatedSchedContextResolved st holder scId = .ok st' := by
  unfold replyRecvPopDonation at h
  cases hHead : replyFrameHeadHolder? st rid with
  | none =>
      rw [hHead] at h
      simp only [] at h
      refine Or.inl ⟨rfl, ?_⟩
      cases hP : popUnheldReplyHead st rid target (determineTargetCore st target) with
      | error e => rw [hP] at h; cases h
      | ok s =>
        rw [hP] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
        rw [h]
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
        split at h
        · cases hRet : returnDonatedSchedContextResolved st holder oldScId
              target with
          | error e => rw [hRet] at h; simp only [] at h; cases h
          | ok st1' =>
            rw [hRet] at h
            simp only [] at h
            exact absurd (Prod.mk.inj (Except.ok.inj h)).1 (by simp)
        · rename_i hAcc
          refine Or.inr ⟨oldScId, holder, rfl, by simpa using hAcc, ?_⟩
          cases hK : keepDonatedSchedContextResolved st holder oldScId with
          | error e => rw [hK] at h; cases h
          | ok s =>
            rw [hK] at h
            simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
            rw [h]

/-- **WS-RR RR8.12 Cut C2**: and a pop that hands nothing back at a frame heading
nothing commits nothing, so a `.replyRecv` whose answered frame heads no context
runs its receive leg on the reply leg's own post-state.  What licenses the
footprint's empty pop pair. -/
theorem replyRecvPopDonation_ok_none_eq (rid : SeLe4n.ReplyId) (target : SeLe4n.ThreadId)
    (st st' : SystemState) (hNoHead : replyFrameHeadContext? st rid = none)
    (h : replyRecvPopDonation rid target st = .ok (none, st')) : st' = st := by
  rcases replyRecvPopDonation_ok_none_decompose rid target st st' h with
    ⟨-, hP⟩ | ⟨_, _, hH, -, -⟩
  · rw [popUnheldReplyHead_of_no_head st rid _ _ hNoHead] at hP
    cases hP; rfl
  · rw [replyFrameHeadHolder?_of_no_head st rid hNoHead] at hH; cases hH

/-- **WS-RR RR8.12 Cut C6e (the exactness frame)**: the pop writes no replenish
queue outside `replyDonationReturnReplenishCores` — the FOOTPRINT's own first
segment, and the one the `.reply` spine's pop reads too (Cut C3a gave that pair one
owner).

Two branches, both the pop's own.  A frame that heads no context returns nothing,
so the pop is the identity; one that does is the resolved return — a store chain,
so scheduler-silent, keeping every release link — followed by the settle, which
writes exactly the cores `replyDonationReturnReplenishCores_of_head` names. -/
theorem replyRecvPopDonation_replenishQueueOnCore_ne (rid : SeLe4n.ReplyId)
    (target : SeLe4n.ThreadId) (st st' : SystemState)
    (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)) (c : Concurrency.CoreId)
    (hObjInv : st.objects.invExt)
    (hne : c ∉ replyDonationReturnReplenishCores st rid target)
    (h : replyRecvPopDonation rid target st = .ok (returned?, st')) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  cases hRet : returned? with
  | none =>
    subst hRet
    rcases replyRecvPopDonation_ok_none_decompose rid target st st' h with
      ⟨hNoH, hP⟩ | ⟨_, _, -, -, hK⟩
    rotate_right
    · rw [keepDonatedSchedContextResolved_scheduler_eq hK]
    cases hH : replyFrameHeadContext? st rid with
    | none =>
      rw [popUnheldReplyHead_of_no_head st rid _ _ hH] at hP; cases hP; rfl
    | some scId =>
      rw [replyDonationReturnReplenishCores_of_unheld st rid target scId hNoH hH] at hne
      simp only [List.mem_append, List.mem_singleton, not_or] at hne
      exact popUnheldReplyHead_replenishQueueOnCore_ne hObjInv
        (fun s hs => by rw [hH] at hs; cases hs; exact hne.1) hne.2 hP
  | some pair =>
    obtain ⟨scId, holder⟩ := pair
    subst hRet
    have hHead := replyRecvPopDonation_holder_eq_frameHead rid target st st' scId holder h
    rw [replyDonationReturnReplenishCores_of_head st rid target scId holder hHead] at hne
    simp only [List.mem_append, List.mem_singleton, not_or] at hne
    obtain ⟨hFrom, hTo⟩ := hne
    obtain ⟨st1', hResolved, hEq⟩ :=
      replyRecvPopDonation_ok_some_decompose rid target st st' scId holder h
    obtain ⟨newOwner?, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hResolved
    have hP : c ∉ SchedContextOps.purgeReplenishCores st1' scId := by
      rw [returnDonatedSchedContext_purgeReplenishCores hObjInv hPop]; exact hFrom
    rw [hEq, SchedContextOps.settleReturnedContext_replenishQueueOnCore_ne st1'
      (determineTargetCore st target) scId c hP hTo,
      returnDonatedSchedContext_scheduler_eq st st1' holder scId
        target newOwner? hPop]
    rfl

/-- **WS-RM (`v0.35.6`)**: the pop preserves object-store integrity — the return
is a store chain over existing keys and the settle writes release links alone. -/
theorem replyRecvPopDonation_preserves_objects_invExt (rid : SeLe4n.ReplyId)
    (target : SeLe4n.ThreadId)
    (st st' : SystemState) (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId))
    (hObjInv : st.objects.invExt)
    (hStep : replyRecvPopDonation rid target st = .ok (returned?, st')) :
    st'.objects.invExt := by
  by_cases hR : returned? = none
  · subst hR
    rcases replyRecvPopDonation_ok_none_decompose rid target st st' hStep with
      ⟨-, hP⟩ | ⟨_, _, -, -, hK⟩
    · exact popUnheldReplyHead_objects_invExt hObjInv hP
    · exact keepDonatedSchedContextResolved_objects_invExt hObjInv hK
  unfold replyRecvPopDonation at hStep
  cases hHead : replyFrameHeadHolder? st rid with
  | none =>
      rw [hHead] at hStep
      simp only [] at hStep
      split at hStep <;> simp at hStep
      exact absurd hStep.1.symm hR
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
        split at hStep
        rotate_left
        · split at hStep <;> simp at hStep
          exact absurd hStep.1.symm hR
        cases hRet : returnDonatedSchedContextResolved st holder oldScId
              target with
        | error e => rw [hRet] at hStep; simp only [] at hStep; cases hStep
        | ok st1' =>
          rw [hRet] at hStep
          obtain ⟨n, _, hPopN⟩ := returnDonatedSchedContextResolved_ok_decompose hRet
          have hEq : SchedContextOps.settleReturnedContext st1'
                (determineTargetCore st target) oldScId
              = st' :=
            (by simpa using hStep : some (oldScId, holder) = returned? ∧ _).2
          rw [← hEq]
          exact SchedContextOps.settleReturnedContext_objects_invExt _ _ _
            (returnDonatedSchedContext_preserves_objects_invExt st st1' _ _ _ hObjInv n hPopN)

/-- **WS-RR RR2.20 / WS-RM (`v0.35.6`): the pop restores replenish-queue affinity
consistency on every core.**

The return rebinds the SchedContext from the recorded server to its original
owner, and the SM5.H invariant `replenishQueueAffinityConsistentOnCore` says a
context's CBS replenishments sit on its bound thread's home core — so the return
falsifies it from the instant it commits unless the replenishment follows the
binding, which is exactly what this step's second half does: the settle purges it
off the core its link names and re-places it on the recipient's home (WS-ZA
ZA6.33). -/
theorem replyRecvPopDonation_preserves_replenishQueueAffinityConsistent_smp
    (rid : SeLe4n.ReplyId) (target : SeLe4n.ThreadId) (st st' : SystemState)
    (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId))
    (hObjInv : st.objects.invExt) (hRef : st.releaseQueueRefined)
    (hCons : replenishQueueAffinityConsistent_smp st)
    (h : replyRecvPopDonation rid target st = .ok (returned?, st')) :
    replenishQueueAffinityConsistent_smp st' := by
  by_cases hR : returned? = none
  · subst hR
    rcases replyRecvPopDonation_ok_none_decompose rid target st st' h with
      ⟨-, hU⟩ | ⟨_, _, -, -, hK⟩
    rotate_right
    · obtain ⟨_, -, hK'⟩ := keepDonatedSchedContextResolved_ok_decompose hK
      exact keepDonatedSchedContext_preserves_replenishQueueAffinityConsistent_smp hObjInv hCons hK'
    rcases popUnheldReplyHead_objects_frame hU with
      ⟨_, rfl⟩ | ⟨scId, n, st1, _, _, hP, rfl⟩ | ⟨_, _, -, -, hS⟩
    · exact hCons
    rotate_left
    · have F := SchedLinkFrame.severUnheldSchedContext hObjInv hS
      exact replenishQueueAffinityConsistent_smp_of_frame F.binding F.aux F.replenish hCons
    · exact returnUnheldSchedContext_settle_preserves_replenishQueueAffinityConsistent_smp
        hObjInv hRef hCons rfl hP
  unfold replyRecvPopDonation at h
  cases hHead : replyFrameHeadHolder? st rid with
  | none =>
      rw [hHead] at h
      simp only [] at h
      split at h <;> simp at h
      exact absurd h.1.symm hR
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
        split at h
        rotate_left
        · split at h <;> simp at h
          exact absurd h.1.symm hR
        cases hRet : returnDonatedSchedContextResolved st holder oldScId
            target with
        | error e =>
            rw [hRet] at h
            simp only [] at h
            cases h
        | ok st1' =>
            rw [hRet] at h
            simp only [] at h
            obtain ⟨n, _, hPopN⟩ := returnDonatedSchedContextResolved_ok_decompose hRet
            have hEq : SchedContextOps.settleReturnedContext st1'
                  (determineTargetCore st target) oldScId
                = st' :=
              (by simpa using h : some (oldScId, holder) = returned? ∧ _).2
            rw [← hEq]
            exact returnDonatedSchedContext_settle_preserves_replenishQueueAffinityConsistent_smp
              st st1' holder oldScId target _
              hObjInv hRef hCons rfl n hPopN

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
      (descheduleAtPlacement_objectsAgreeOffRunLinks _ _)).mpr (hc c)
  unfold replyRecvPostReceiveDonation at h
  cases returned? with
  | none =>
    simp only [] at h
    cases hCall : rendezvousDequeuedCall st nextThread with
    | false =>
        rw [hCall] at h; simp only [Bool.false_eq_true, if_false] at h; cases h
        exact hPip st hObjInv hCons
    | true =>
        rw [hCall] at h; simp only [if_true] at h
        cases hDon : applyRendezvousCallDonation st tid nextThread with
        | error e => rw [hDon] at h; simp only [] at h; cases h
        | ok st2 =>
            rw [hDon] at h; simp only [] at h; cases h
            exact hPip _
              (applyRendezvousCallDonation_preserves_objects_invExt _ st2 tid nextThread
                hObjInv hDon)
              (applyRendezvousCallDonation_preserves_replenishQueueAffinityConsistent_smp
                _ st2 tid nextThread hObjInv hCons hDon)
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

  **WS-HP HP10.7**: the destination is the REDIRECTED recipient, so `hOwnerHome`
  is quantified over the head-driven trigger's answer.  The settle (WS-ZA ZA6.33)
  purges off the context's own link, so the source needs no hypothesis.  See
  `applyReplyDonationOnCore_preserves_replenishQueueAffinityConsistent_smp`. -/
  | reply (rid : SeLe4n.ReplyId) (targetVtid : SeLe4n.ValidThreadId)
      (ownerHome : Concurrency.CoreId)
      (hOwnerHome : ∀ scId holder, replyFrameHeadHolder? st rid = some (scId, holder) →
          determineTargetCore st targetVtid.val = ownerHome)
      (hUnheldHome : ∀ scId, replyFrameHeadHolder? st rid = none →
          replyFrameHeadContext? st rid = some scId →
          determineTargetCore st targetVtid.val = ownerHome)
      (hStep : applyReplyDonationOnCore st rid targetVtid ownerHome
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
replenishment follows the binding — which is why every live path moves it: the
call-side hand-offs migrate it (`migrateSchedContextReplenishment`, a same-core
hand-off costing nothing), and the reply-side returns settle it
(`settleReturnedContext`, WS-ZA ZA6.33), which reads the release queues and so
needs them refined.

This is the catalogued statement over every path.  Its proof is the per-path
theorems and nothing else: the aggregation is the content, since a reader
looking for "the donation theorem" found several names and no claim about the
family. -/
theorem donation_perCore_consistent (st st' : SystemState)
    (hObjInv : st.objects.invExt) (hRef : st.releaseQueueRefined)
    (hCons : replenishQueueAffinityConsistent_smp st)
    (hStep : PerCoreDonationStep st st') :
    replenishQueueAffinityConsistent_smp st' := by
  cases hStep with
  | call callerVtid receiverVtid donorHome doneeHome hDonorHome hDoneeHome h =>
      exact applyCallDonationOnCore_preserves_replenishQueueAffinityConsistent_smp
        st st' callerVtid receiverVtid donorHome doneeHome hObjInv hCons hDonorHome hDoneeHome h
  | reply rid targetVtid ownerHome hOwnerHome hUnheldHome h =>
      exact applyReplyDonationOnCore_preserves_replenishQueueAffinityConsistent_smp
        st st' rid targetVtid ownerHome hObjInv hRef hCons hOwnerHome hUnheldHome h
  | replyRecvPop rid target returned? h =>
      exact replyRecvPopDonation_preserves_replenishQueueAffinityConsistent_smp
        rid target st st' returned? hObjInv hRef hCons h
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
* the migration writes only `schedContexts` and the replenishment queue, so it
  leaves the object store unchanged.

**WS-HP HP4.5**: the pre-state condition is quantified over the head-driven
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
    -- **WS-OD OD4.4**: the return resolves its new owner from the context's reply
    -- stack; this is the obligation that resolution carries.
    (hStackValid : ∀ scId serverTid originalOwner,
        replyStackOuterCallerValid st scId serverTid originalOwner)
    -- **WS-ZA ZA6.34**: the unheld pop's coherence obligation -- see
    -- `applyReplyDonation_preserves_ipcInvariantFull`.
    (hUnheld : unheldReplyPopCoherent st rid target)
    (h : replyRecvPopDonation rid target st = .ok (returned?, st')) :
    ipcInvariantFull st' := by
  by_cases hR : returned? = none
  · subst hR
    rcases replyRecvPopDonation_ok_none_decompose rid target st st' h with
      ⟨hNoH, hP⟩ | ⟨scId, holder, hH, -, hK⟩
    · exact popUnheldReplyHead_preserves_ipcInvariantFull hObjInv hInv hStackValid hUnheld hNoH hP
    · obtain ⟨n, hRes, hK'⟩ := keepDonatedSchedContextResolved_ok_decompose hK
      exact keepDonatedSchedContext_preserves_ipcInvariantFull hObjInv hInv
        (hHolderDonation scId holder hH) (hStackValid scId holder target n hRes).2 hK'
  unfold replyRecvPopDonation at h
  cases hHead : replyFrameHeadHolder? st rid with
  | none =>
      rw [hHead] at h
      simp only [] at h
      split at h <;> simp at h
      exact absurd h.1.symm hR
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
        split at h
        rotate_left
        · split at h <;> simp at h
          exact absurd h.1.symm hR
        have hHEq : holderV.val = holder :=
          SeLe4n.ThreadId.toValid?_some_val_eq holder holderV hHV
        cases hRet : returnDonatedSchedContextResolved st holder oldScId
            target with
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
                target n = .ok st1' := by
              rw [hHEq]; exact hPopN
            have hRetWV : replyDonationReturn? st holderV.val = some (oldScId, target) := by
              rw [hHEq]; exact hRetW
            -- **WS-HP HP10.7**: three cases, as in the `.reply` spine — no origin,
            -- an origin that *is* the answered caller, and a distinct origin, the
            -- last taking the generalised bundle under the redirect's own guard.
            have hInv1' : ipcInvariantFull st1' := by
              exact returnDonatedSchedContext_preserves_ipcInvariantFull st st1' holderV oldScId
                target hObjInv hInv hRetWV n
                (donationReturnOuterValid_of_stackValid
                  (hStackValid oldScId holderV.val target) hResN) hRetV
            -- The settle is invisible to every bundle reading.
            have hInvM : ipcInvariantFull (SchedContextOps.settleReturnedContext st1'
                (determineTargetCore st target) oldScId) :=
              ipcInvariantFull_of_objectsAgreeOffSchedulerLinks
                (.of_releaseLinks (SchedContextOps.settleReturnedContext_agree _ _ _)) hInv1'
            exact h.2 ▸ hInvM

/-- **The reply leg's capability transfer never refuses**: a transfer with
nothing to move, no receiver or no slot moves nothing, and the transfer loop
(`ipcUnwrapCapsLoop`) stops rather than fails on a capability it cannot take. -/
theorem ipcUnwrapCapsLoop_ok (caps : Array TransferCap) (endpointId : Option SeLe4n.ObjId)
    (rtcb : TCB) :
    ∀ (fuel idx : Nat) (slot? : Option CSpaceAddr) (acc : Array CapTransferResult)
      (st : SystemState),
      ∃ r, ipcUnwrapCapsLoop caps endpointId rtcb idx slot? acc fuel st = .ok r
  | 0, _, _, acc, st => ⟨_, rfl⟩
  | fuel + 1, idx, slot?, acc, st => by
    simp only [ipcUnwrapCapsLoop]
    cases caps[idx]? with
    | none => exact ⟨_, rfl⟩
    | some tc =>
      simp only []
      split
      · exact ipcUnwrapCapsLoop_ok caps endpointId rtcb fuel _ _ _ _
      · cases slot? with
        | none => exact ⟨_, rfl⟩
        | some dst =>
          simp only []
          cases ipcTransferSingleCap tc.cap tc.srcSlot dst st with
          | error _ => exact ⟨_, rfl⟩
          | ok p => exact ipcUnwrapCapsLoop_ok caps endpointId rtcb fuel _ _ _ _

theorem replyRecvReplyTransfer_ok (answer : Option Architecture.FaultReplyOutcome)
    (pre : SystemState) (replier prevCaller : SeLe4n.ThreadId) (grant : Bool)
    (st : SystemState) :
    ∃ r, replyRecvReplyTransfer answer pre replier prevCaller grant st = .ok r := by
  cases answer with
  | some _ => exact ⟨_, rfl⟩
  | none =>
    simp only [replyRecvReplyTransfer_none, replyTransferCaps, receiveTransferCaps]
    cases replyCapRequest pre replier grant with
    | none => exact ⟨_, rfl⟩
    | some req =>
      obtain ⟨root, addrs⟩ := req
      simp only []
      split
      · exact ⟨_, rfl⟩
      · cases receiverCapTarget? pre prevCaller with
        | none => exact ⟨_, rfl⟩
        | some t => exact ipcUnwrapCapsLoop_ok _ _ _ _ _ _ _ _

theorem replyRecvReplyTransfer_scheduler_eq {answer : Option Architecture.FaultReplyOutcome}
    {pre : SystemState} {replier prevCaller : SeLe4n.ThreadId} {grant : Bool}
    {st st' : SystemState} {summary : CapTransferSummary}
    (h : replyRecvReplyTransfer answer pre replier prevCaller grant st = .ok (summary, st')) :
    st'.scheduler = st.scheduler := by
  rw [replyRecvReplyTransfer_eq_receiveTransferCaps] at h
  exact receiveTransferCaps_scheduler_eq h

theorem replyRecvReplyTransfer_objects_invExt {answer : Option Architecture.FaultReplyOutcome}
    {pre : SystemState} {replier prevCaller : SeLe4n.ThreadId} {grant : Bool}
    {st st' : SystemState} {summary : CapTransferSummary} (hI : st.objects.invExt)
    (h : replyRecvReplyTransfer answer pre replier prevCaller grant st = .ok (summary, st')) :
    st'.objects.invExt := by
  rw [replyRecvReplyTransfer_eq_receiveTransferCaps] at h
  exact receiveTransferCaps_objects_invExt hI h

/-- **The reply leg's capability transfer writes only the CNode the
`.replyRecv` footprint names** (`replyInstallCNode?`,
`lockSet_endpointReplyRecvOnCore_covers_replyInstall`): any other object agrees
with the pre-transfer state off derivation metadata, whatever the grant right
and whatever the answer (a fault answer transfers nothing). -/
theorem replyRecvReplyTransfer_writes_destination
    (answer : Option Architecture.FaultReplyOutcome) (pre st st' : SystemState)
    (replier target : SeLe4n.ThreadId) (grant : Bool) (summary : CapTransferSummary)
    (oid : SeLe4n.ObjId) (hObjInv : st.objects.invExt)
    (hStep : replyRecvReplyTransfer answer pre replier target grant st = .ok (summary, st'))
    (hNe : replyInstallCNode? pre replier target ≠ some oid) :
    SystemState.objectAgreesOffDerivationMetadataAt st' st oid := by
  cases answer with
  | none =>
    exact replyTransferCaps_writes_destination pre st st' replier target grant summary oid
      hObjInv hStep hNe
  | some o =>
    rw [replyRecvReplyTransfer_some] at hStep
    cases hStep
    exact .of_eq rfl

/-- **The reply leg's transfer leaves the state as it found it when the
footprint names no install** (`replyInstallCNode?` is `none`), on either
answer. -/
theorem replyRecvReplyTransfer_of_noInstall
    (answer : Option Architecture.FaultReplyOutcome) (pre st : SystemState)
    (replier target : SeLe4n.ThreadId) (grant : Bool)
    (h : replyInstallCNode? pre replier target = none) :
    replyRecvReplyTransfer answer pre replier target grant st
      = .ok ({ results := #[] }, st) := by
  cases answer with
  | none => exact replyTransferCaps_of_noInstall pre st replier target grant h
  | some o => rfl

/-- **The reply-receive footprint covers its reply leg's CDT write**: a reply
transfer that changes the CDT runs under a footprint that declares
`stateLevelLock` for write (`replyInstallCdtLock?`). -/
theorem lockSet_endpointReplyRecvOnCore_covers_replyTransferCdt
    (answer : Option Architecture.FaultReplyOutcome) (pre st st' : SystemState)
    (replier : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (target : SeLe4n.ThreadId) (endpointObjId : SeLe4n.ObjId) (grant : Bool)
    (summary : CapTransferSummary)
    (hStep : replyRecvReplyTransfer answer pre replier target grant st = .ok (summary, st'))
    (hCdt : st'.cdt ≠ st.cdt) :
    (Concurrency.stateLevelLock, Concurrency.AccessMode.write)
      ∈ (lockSet_endpointReplyRecvOnCore pre replier cnodeRootObjId target
          endpointObjId).pairs := by
  cases h : replyInstallCNode? pre replier target with
  | none =>
    rw [replyRecvReplyTransfer_of_noInstall answer pre st replier target grant h] at hStep
    cases hStep
    exact absurd rfl hCdt
  | some r =>
    exact lockSet_endpointReplyRecvOnCore_covers_replyInstallCdt pre replier
      cnodeRootObjId target endpointObjId (by rw [h]; rfl)

/-- **The reply-receive footprint declares the CNode its receive leg installs
into, read after the reply leg's capability transfer.**  The receive leg runs on
the transfer's post-state and reads its receive slot there (seL4's
`getReceiveSlots`, called from `receiveIPC` after `doReplyTransfer`).  Whatever
the answer and the reply capability's grant right, a receive slot read after the
transfer is the pre-state's (`receiveInstallCNode?`: no grant, a fault answer,
or a reply asking for nothing) or the one an installing transfer leaves
(`receiveInstallCNodeAfterReply?`), and the footprint declares both.  The second
is the answer when the answered caller and the replier share a CSpace and the
reply installs a CNode capability into the slot the replier's receive path
crosses, which the pre-state resolution cannot see. -/
theorem lockSet_endpointReplyRecvOnCore_covers_receiveLegSlot
    (answer : Option Architecture.FaultReplyOutcome) (st s : SystemState)
    (replier : SeLe4n.ThreadId) (cnodeRootObjId : SeLe4n.ObjId)
    (target : SeLe4n.ThreadId) (endpointObjId : SeLe4n.ObjId) (grant : Bool)
    (summary : CapTransferSummary) (dst : CSpaceAddr)
    (hStep : replyRecvReplyTransfer answer st replier target grant st = .ok (summary, s))
    (hCaps : receiveInstallsCaps st endpointObjId = true)
    (hSlot : receiverCapSlot? s replier = some dst) :
    (Concurrency.cnodeLock dst.cnode, Concurrency.AccessMode.write)
      ∈ (lockSet_endpointReplyRecvOnCore st replier cnodeRootObjId target
          endpointObjId).pairs := by
  have hCases : receiverCapSlot? s replier = receiverCapSlot? st replier ∨
      receiverCapSlot? s replier
        = receiverCapSlot? (replyTransferInstalledState st replier target) replier := by
    cases answer with
    | none =>
      exact replyTransferCaps_receiverCapSlot_cases st s replier target replier grant summary
        hStep
    | some o =>
      rw [replyRecvReplyTransfer_some] at hStep
      cases hStep
      exact .inl rfl
  rcases hCases with h | h
  · exact lockSet_endpointReplyRecvOnCore_covers_receiveSlot st replier cnodeRootObjId target
      endpointObjId dst hCaps (h ▸ hSlot)
  · exact lockSet_endpointReplyRecvOnCore_covers_receiveSlotAfterReply st replier
      cnodeRootObjId target endpointObjId dst hCaps (h ▸ hSlot)

@[simp] theorem replyRecvReceiveLegState_eq_of_ok (answer : Option Architecture.FaultReplyOutcome)
    (pre : SystemState) (replier : SeLe4n.ThreadId) (grant : Bool) (rid : SeLe4n.ReplyId)
    (target : SeLe4n.ThreadId)
    (st1 st1q st1p : SystemState) (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId))
    (xs : CapTransferSummary)
    (h : replyRecvPopDonation rid target st1 = .ok (returned?, st1q))
    (hX : replyRecvReplyTransfer answer pre replier target grant st1q = .ok (xs, st1p)) :
    replyRecvReceiveLegState answer pre replier grant rid target st1 =
      receiveReturnSchedContext true (replyRecvAnswerCaller answer st1p target xs.capInfo)
        replier := by
  unfold replyRecvReceiveLegState; rw [h]; simp only []; rw [hX]

theorem replyRecvReplyStepState_eq_of_ok {answer : Option Architecture.FaultReplyOutcome}
    {pre : SystemState} {replier : SeLe4n.ThreadId} {grant : Bool} {rid : SeLe4n.ReplyId}
    {target : SeLe4n.ThreadId} {st1 st1q st1p : SystemState}
    {returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)} {xs : CapTransferSummary}
    (h : replyRecvPopDonation rid target st1 = .ok (returned?, st1q))
    (hX : replyRecvReplyTransfer answer pre replier target grant st1q = .ok (xs, st1p)) :
    replyRecvReplyStepState answer pre replier grant rid target st1 =
      replyRecvAnswerCaller answer st1p target xs.capInfo := by
  unfold replyRecvReplyStepState; rw [h]; simp only []; rw [hX]

/-- The receive leg runs on the reply step's state, after seL4-MCS
`receiveIPC`'s return. -/
theorem replyRecvReceiveLegState_eq_replyStep {answer : Option Architecture.FaultReplyOutcome}
    {pre : SystemState} {replier : SeLe4n.ThreadId} {grant : Bool} {rid : SeLe4n.ReplyId}
    {target : SeLe4n.ThreadId} {st1 st1q : SystemState}
    {returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)}
    (h : replyRecvPopDonation rid target st1 = .ok (returned?, st1q)) :
    replyRecvReceiveLegState answer pre replier grant rid target st1 =
      receiveReturnSchedContext true
        (replyRecvReplyStepState answer pre replier grant rid target st1) replier := by
  obtain ⟨⟨xs, st1p⟩, hX⟩ := replyRecvReplyTransfer_ok answer pre replier target grant st1q
  rw [replyRecvReceiveLegState_eq_of_ok _ _ _ _ _ _ _ _ _ _ _ h hX,
    replyRecvReplyStepState_eq_of_ok h hX]

@[simp] theorem replyRecvPoppedDonation_eq_of_ok (rid : SeLe4n.ReplyId)
    (target : SeLe4n.ThreadId)
    (st1 st1p : SystemState) (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId))
    (h : replyRecvPopDonation rid target st1 = .ok (returned?, st1p)) :
    replyRecvPoppedDonation rid target st1 = returned? := by
  unfold replyRecvPoppedDonation; rw [h]

theorem replyRecvReceiveLegState_eq_of_error (answer : Option Architecture.FaultReplyOutcome)
    (pre : SystemState) (replier : SeLe4n.ThreadId) (grant : Bool) (rid : SeLe4n.ReplyId)
    (target : SeLe4n.ThreadId)
    (st1 : SystemState) (e : KernelError)
    (h : replyRecvPopDonation rid target st1 = .error e) :
    replyRecvReceiveLegState answer pre replier grant rid target st1 = st1 := by
  unfold replyRecvReceiveLegState; rw [h]

/-- **The thread a receive dequeues owns no loan**, on the receive's committed
state: a rendezvous dequeues the head of the send queue, which waits on the
endpoint (`queueHeadBlockedConsistent`) and so on no reply, while a loan's owner
waits on a reply (`donationOwnerValid`), and the receive writes no binding
(`endpointReceiveDualWithCapsOnCore_sameSchedContextBindings_of_rendezvous`).  A
receive that blocks reports the receiver itself, which `hRecvNotOwner` covers.
The rendezvous donation's donor obligation. -/
theorem endpointReceiveDualWithCapsOnCore_dequeuedNotOwner
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (executingCore : Concurrency.CoreId) (st st' : SystemState) (dequeued : SeLe4n.ThreadId)
    (summary : CapTransferSummary) (sgi : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hRecvNotOwner : ∀ (s : SeLe4n.ThreadId) (sTcb : TCB) (sc0 : SeLe4n.SchedContextId),
      st'.getTcb? s = some sTcb → sTcb.schedContextBinding ≠ .donated sc0 receiver)
    (hStep : endpointReceiveDualWithCapsOnCore endpointId receiver replyId executingCore st =
      (st', .ok (dequeued, summary, sgi))) :
    ∀ (s : SeLe4n.ThreadId) (sTcb : TCB) (sc0 : SeLe4n.SchedContextId),
      st'.getTcb? s = some sTcb → sTcb.schedContextBinding ≠ .donated sc0 dequeued := by
  cases hS : receiveRendezvousSender? st endpointId with
  | none =>
    rw [endpointReceiveDualWithCapsOnCore_ok_dequeued_eq_receiver_of_blocked endpointId receiver
      replyId executingCore st st' dequeued summary sgi hS hStep]
    exact hRecvNotOwner
  | some sender =>
    unfold receiveRendezvousSender? at hS
    cases hEp : st.getEndpoint? endpointId with
    | none => rw [hEp] at hS; cases hS
    | some ep =>
      rw [hEp] at hS
      have hHead : ep.sendQ.head = some sender := hS
      rw [endpointReceiveDualWithCapsOnCore_ok_dequeued_eq_head endpointId receiver replyId
        executingCore st st' dequeued summary sgi ep sender hEp hHead hStep]
      have hBnd := endpointReceiveDualWithCapsOnCore_sameSchedContextBindings_of_rendezvous
        endpointId receiver replyId executingCore st ep sender hObjInv hEp hHead
      rw [hStep] at hBnd
      refine notDonationOwner_of_notBlockedOnReply hInv.donationOwnerValid hBnd ?_
      intro tcb hT ep' rt hR
      have hQ := (hInv.queueHeadBlockedConsistent endpointId ep sender tcb
        ((SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp)
        ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT)).2 hHead
      rcases hQ with h | h <;> rw [h] at hR <;> cases hR

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
  descheduled and then the recorded server is walked, and the deschedule writes
  only run-queue links.

`hReceiverNotOwner` is stated at *this* step's pre-state (the receive leg's
committed state), not at the reply leg's: the pop no longer runs between them,
so there is nothing to transport it across, and the fused statement's
`hReceiverNotAwaitingReply` -- which existed only to carry it through the pop's
binding trichotomy -- has no subject here. -/
theorem replyRecvPostReceiveDonation_preserves_ipcInvariantFull
    (tid recordedServer nextThread : SeLe4n.ThreadId) (serverCore : Concurrency.CoreId)
    (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId))
    (st st' : SystemState) (u : Unit)
    (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st)
    (hReceiverNotOwner : ∀ (tid' : SeLe4n.ThreadId) (tcb : TCB)
        (scId : SeLe4n.SchedContextId),
        st.getTcb? tid' = some tcb → tcb.schedContextBinding ≠ .donated scId tid)
    (hDequeuedNotOwner : ∀ (tid' : SeLe4n.ThreadId) (tcb : TCB)
        (scId : SeLe4n.SchedContextId),
        st.getTcb? tid' = some tcb → tcb.schedContextBinding ≠ .donated scId nextThread)
    (h : replyRecvPostReceiveDonation tid recordedServer nextThread serverCore returned? st
        = .ok (u, st')) :
    ipcInvariantFull st' := by
  unfold replyRecvPostReceiveDonation at h
  cases returned? with
  | none =>
    simp only [] at h
    cases hCall : rendezvousDequeuedCall st nextThread with
    | false =>
        rw [hCall] at h; simp only [Bool.false_eq_true, if_false, Except.ok.injEq,
          Prod.mk.injEq] at h
        exact h.2 ▸ propagatePipChainCrossCore_preserves_ipcInvariantFull st recordedServer
          serverCore _ hObjInv hInv
    | true =>
        rw [hCall] at h; simp only [if_true] at h
        cases hDon : applyRendezvousCallDonation st tid nextThread with
        | error e => rw [hDon] at h; simp only [] at h; cases h
        | ok st2 =>
            rw [hDon] at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h
            have hStep : applyReceiveRendezvousDonation st tid nextThread = .ok st2 := by
              unfold applyReceiveRendezvousDonation
              rw [hCall]
              simpa using hDon
            have hInv2 : ipcInvariantFull st2 :=
              applyReceiveRendezvousDonation_preserves_ipcInvariantFull _ st2
                tid nextThread hObjInv hInv hReceiverNotOwner hDequeuedNotOwner hStep
            have hObjInv2 : st2.objects.invExt :=
              applyReceiveRendezvousDonation_preserves_objects_invExt _ st2 tid
                nextThread hObjInv hStep
            exact h.2 ▸ propagatePipChainCrossCore_preserves_ipcInvariantFull st2
              recordedServer serverCore _ hObjInv2 hInv2
  | some pair =>
    obtain ⟨scIdP, holder⟩ := pair
    simp only [] at h
    cases hCall : rendezvousDequeuedCall st nextThread with
    | false =>
        rw [hCall] at h; simp only [Bool.false_eq_true, if_false, Except.ok.injEq,
          Prod.mk.injEq] at h
        -- Both arms run `descheduleAtPlacement` now, so this branch splits on
        -- the resolver exactly as the Call arm below does (round 11) -- and on
        -- the HOLDER, which is the thread the pop unbound (PR #897 review).
        have hDesched : ipcInvariantFull (descheduleAtPlacement st holder) :=
          ipcInvariantFull_of_objectsAgreeOffRunLinks
            (descheduleAtPlacement_objectsAgreeOffRunLinks _ _) hInv
        have hDeschedInvExt : (descheduleAtPlacement st holder).objects.invExt :=
          descheduleAtPlacement_preserves_objects_invExt st holder hObjInv
        exact h.2 ▸ propagatePipChainCrossCore_preserves_ipcInvariantFull _ recordedServer
          serverCore _ hDeschedInvExt hDesched
    | true =>
        rw [hCall] at h; simp only [if_true] at h
        -- The deschedule runs first on this arm.  It writes no object, so the
        -- donation's object-level hypotheses transport verbatim; what it does
        -- write is the run queue, which no conjunct reads.
        have hA : (replyRecvHolderDeschedule tid holder st).objectsAgreeOffRunLinks st := by
          unfold replyRecvHolderDeschedule
          split
          · exact .refl _
          · exact descheduleAtPlacement_objectsAgreeOffRunLinks _ _
        have hSObj : (replyRecvHolderDeschedule tid holder st).objects.invExt := by
          unfold replyRecvHolderDeschedule
          split
          · exact hObjInv
          · exact descheduleAtPlacement_preserves_objects_invExt _ _ hObjInv
        have hSInv : ipcInvariantFull (replyRecvHolderDeschedule tid holder st) :=
          ipcInvariantFull_of_objectsAgreeOffRunLinks hA hInv
        have hSNotOwner : ∀ (tid' : SeLe4n.ThreadId) (tcb : TCB)
            (scId : SeLe4n.SchedContextId),
            (replyRecvHolderDeschedule tid holder st).getTcb? tid'
              = some tcb → tcb.schedContextBinding ≠ .donated scId tid := by
          intro tid' tcb scId hTcb
          rw [SystemState.getTcb?_eq_some_iff] at hTcb
          run_links_back hA at tcb hTcb
          exact hReceiverNotOwner tid' tcb scId ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hTcb)
        have hSDqNotOwner : ∀ (tid' : SeLe4n.ThreadId) (tcb : TCB)
            (scId : SeLe4n.SchedContextId),
            (replyRecvHolderDeschedule tid holder st).getTcb? tid'
              = some tcb → tcb.schedContextBinding ≠ .donated scId nextThread := by
          intro tid' tcb scId hTcb
          rw [SystemState.getTcb?_eq_some_iff] at hTcb
          run_links_back hA at tcb hTcb
          exact hDequeuedNotOwner tid' tcb scId ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hTcb)
        cases hDon : applyRendezvousCallDonation
            (replyRecvHolderDeschedule tid holder st) tid nextThread with
        | error e => rw [hDon] at h; simp only [] at h; cases h
        | ok st2 =>
            rw [hDon] at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h
            -- The guard reads a TCB, and the deschedule writes no object, so the
            -- arm the donation takes is the arm the guard selected.
            have hCallD : rendezvousDequeuedCall
                (replyRecvHolderDeschedule tid holder st) nextThread = true := by
              rw [rendezvousDequeuedCall_of_objectsAgreeOffRunLinks hA]
              exact hCall
            have hStep : applyReceiveRendezvousDonation
                (replyRecvHolderDeschedule tid holder st)
                tid nextThread = .ok st2 := by
              unfold applyReceiveRendezvousDonation
              rw [hCallD]
              simpa using hDon
            have hInv2 : ipcInvariantFull st2 :=
              applyReceiveRendezvousDonation_preserves_ipcInvariantFull _ st2
                tid nextThread hSObj hSInv hSNotOwner hSDqNotOwner hStep
            have hObjInv2 : st2.objects.invExt :=
              applyReceiveRendezvousDonation_preserves_objects_invExt _ st2 tid
                nextThread hSObj hStep
            exact h.2 ▸ propagatePipChainCrossCore_preserves_ipcInvariantFull st2
              recordedServer serverCore _ hObjInv2 hInv2

theorem replyRecvPostReceiveReplenishCores_none_of_no_call (tid nextThread : SeLe4n.ThreadId)
    (st : SystemState) (h : rendezvousDequeuedCall st nextThread = false) :
    replyRecvPostReceiveReplenishCores tid nextThread none st = [] := by
  unfold replyRecvPostReceiveReplenishCores
  simp [h]

theorem replyRecvPostReceiveReplenishCores_none_of_call (tid nextThread : SeLe4n.ThreadId)
    (st : SystemState) (h : rendezvousDequeuedCall st nextThread = true) :
    replyRecvPostReceiveReplenishCores tid nextThread none st
      = rendezvousCallDonationReplenishCores st tid nextThread := by
  unfold replyRecvPostReceiveReplenishCores
  simp [h]

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
theorem replyRecvHandoffReplenishCores_eq_of_pop (answer : Option Architecture.FaultReplyOutcome)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId)
    (msg : IpcMessage) (grant : Bool)
    (executingCore : Concurrency.CoreId) (st st1 st1q st1p : SystemState)
    (sgi : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)) (xs : CapTransferSummary)
    (hReply : endpointReplyOnCore receiver prevCaller msg executingCore st = (st1, .ok sgi))
    (hPop : replyRecvPopDonation replyId prevCaller st1 = .ok (returned?, st1q))
    (hX : replyRecvReplyTransfer answer st receiver prevCaller grant st1q = .ok (xs, st1p)) :
    replyRecvHandoffReplenishCores answer endpointId receiver replyId prevCaller msg grant
        executingCore st
      = replyDonationReturnReplenishCores st1 replyId prevCaller ++
          (receiveReturnReplenishCoresAt true (replyRecvAnswerCaller answer st1p prevCaller xs.capInfo) receiver ++
          (receivePreReturnReplenishCores (receiveReturnSchedContext true (replyRecvAnswerCaller answer st1p prevCaller xs.capInfo) receiver) endpointId
              receiver ++
            (match endpointReceiveDualWithCapsOnCore endpointId receiver (some replyId) executingCore
                (receiveReturnSchedContext true (replyRecvAnswerCaller answer st1p prevCaller xs.capInfo) receiver) with
             | (_, .error _) => []
             | (st2, .ok (nextThread, _, _)) =>
                replyRecvPostReceiveReplenishCores receiver nextThread returned? st2))) := by
  unfold replyRecvHandoffReplenishCores
  simp only [hReply, hPop, hX]
  rfl

/-- ...and once the receive leg has run too, the third component is the post-receive
pair at that leg's post-state. -/
theorem replyRecvHandoffReplenishCores_eq_of_legs (answer : Option Architecture.FaultReplyOutcome)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId)
    (msg : IpcMessage) (grant : Bool)
    (executingCore : Concurrency.CoreId) (st st1 st1q st1p st2 : SystemState)
    (sgi sgi2 : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)) (xs : CapTransferSummary)
    (nextThread : SeLe4n.ThreadId) (summary : CapTransferSummary)
    (hReply : endpointReplyOnCore receiver prevCaller msg executingCore st = (st1, .ok sgi))
    (hPop : replyRecvPopDonation replyId prevCaller st1 = .ok (returned?, st1q))
    (hX : replyRecvReplyTransfer answer st receiver prevCaller grant st1q = .ok (xs, st1p))
    (hRecv : endpointReceiveDualWithCapsOnCore endpointId receiver (some replyId) executingCore
        (receiveReturnSchedContext true (replyRecvAnswerCaller answer st1p prevCaller xs.capInfo) receiver)
      = (st2, .ok (nextThread, summary, sgi2))) :
    replyRecvHandoffReplenishCores answer endpointId receiver replyId prevCaller msg grant
        executingCore st
      = replyDonationReturnReplenishCores st1 replyId prevCaller ++
          (receiveReturnReplenishCoresAt true (replyRecvAnswerCaller answer st1p prevCaller xs.capInfo) receiver ++
          (receivePreReturnReplenishCores (receiveReturnSchedContext true (replyRecvAnswerCaller answer st1p prevCaller xs.capInfo) receiver) endpointId
              receiver ++
            replyRecvPostReceiveReplenishCores receiver nextThread returned? st2)) := by
  rw [replyRecvHandoffReplenishCores_eq_of_pop answer endpointId receiver replyId prevCaller msg
    grant executingCore st st1 st1q st1p sgi returned? xs hReply hPop hX]
  simp only [hRecv]

/-- **WS-RR RR8.12 Cut C2**: the reply leg's wake — the answered caller's home
core — is a run-queue write member, unconditionally: it is the head of the arm's
own write set. -/
theorem schedLockSet_endpointReplyRecvOnCore_contains_prevCaller_runQueue_write
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId)
    (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage) (grant : Bool)
    (executingCore : Concurrency.CoreId) (st : SystemState) :
    (LockKey.runQueue (determineTargetCore st prevCaller), Concurrency.AccessMode.write)
      ∈ schedLockSet_endpointReplyRecvOnCore endpointId receiver replyId prevCaller msg grant
          executingCore st := by
  refine (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr ?_
  unfold endpointReplyRecvWriteSet endpointReplyRecvAnsweringWriteSet
  exact List.mem_cons_self ..

/-- **WS-RR RR8.12 Cut C2**: every core the receive leg writes — resolved at the
pop's post-state, the state that leg runs on — is a run-queue write member. -/
theorem schedLockSet_endpointReplyRecvOnCore_covers_receiveLeg
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId)
    (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage) (grant : Bool)
    (executingCore : Concurrency.CoreId)
    (st st1 st1q st1p : SystemState) (sgi : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)) (xs : CapTransferSummary)
    (hReply : endpointReplyOnCore receiver prevCaller msg executingCore st = (st1, .ok sgi))
    (hPop : replyRecvPopDonation replyId prevCaller st1 = .ok (returned?, st1q))
    (hX : replyRecvReplyTransfer none st receiver prevCaller grant st1q = .ok (xs, st1p)) :
    ∀ c ∈ endpointReceiveDualWriteSet (receiveReturnSchedContext true (replyRecvAnswerCaller none st1p prevCaller xs.capInfo) receiver) endpointId executingCore,
      (LockKey.runQueue c, Concurrency.AccessMode.write)
        ∈ schedLockSet_endpointReplyRecvOnCore endpointId receiver replyId prevCaller msg grant
            executingCore st := by
  intro c hc
  refine (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr ?_
  unfold endpointReplyRecvWriteSet endpointReplyRecvAnsweringWriteSet
  simp only [hReply, hPop, hX, List.mem_cons, List.mem_append, replyRecvAnswerCores,
    List.nil_append]
  exact Or.inr (Or.inl hc)

/-- **WS-RR RR8.12 Cut C2 (coverage, the pop)**: the `.replyRecv` footprint covers the
replenish-queue write lock of every core the pop's settle writes (WS-ZA ZA6.33) —
the purge's core and the recipient's home, `replyDonationReturnReplenishCores` at
the frame the pop resolves (`replyRecvPopDonation_holder_eq_frameHead`), on the
reply leg's post-state, which is the state the pop runs on.  A `withLockSet`
bracket over this footprint therefore holds every slot the settle writes.
Conditioned on the pop having handed a context back, because that is the only
shape on which there is a settle to cover. -/
theorem schedLockSet_endpointReplyRecvOnCore_covers_pop
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId)
    (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage) (grant : Bool)
    (executingCore : Concurrency.CoreId)
    (st st1 st1q : SystemState) (sgi : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    (hReply : endpointReplyOnCore receiver prevCaller msg executingCore st = (st1, .ok sgi))
    (hPop : replyRecvPopDonation replyId prevCaller st1 = .ok (some (scId, holder), st1q)) :
    ∀ c ∈ replyDonationReturnReplenishCores st1 replyId prevCaller,
      (LockKey.replenishQueue c, Concurrency.AccessMode.write)
        ∈ schedLockSet_endpointReplyRecvOnCore endpointId receiver replyId prevCaller msg grant
            executingCore st := by
  intro c hc
  obtain ⟨⟨xs, st1p⟩, hX⟩ := replyRecvReplyTransfer_ok none st receiver prevCaller grant st1q
  have hSeg := replyRecvHandoffReplenishCores_eq_of_pop none endpointId receiver replyId
    prevCaller msg grant executingCore st st1 st1q st1p sgi _ xs hReply hPop hX
  refine (mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mpr ?_
  rw [hSeg]
  exact List.mem_append_left _ hc

/-- **WS-RR RR8.12 Cut C2 (coverage, the block path)**: on a receive leg that blocks
holding a loan, the footprint covers the pre-receive return's migration footprint
member for member — at the cores the migration actually resolves on the post-pop
state it runs on (`receivePreReturnReplenishCores_covers_migration`).  The `.replyRecv`
sibling of `schedLockSet_endpointReceiveOnCore_covers_preReturnMigration`, read at
the state the arm's receive leg runs on rather than at the syscall's pre-state,
because that is where this arm's leg runs.  Conditioned on the pop's OWN guard and
on the pop having committed, as its sibling is. -/
theorem schedLockSet_endpointReplyRecvOnCore_covers_preReturnMigration
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId)
    (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage) (grant : Bool)
    (executingCore : Concurrency.CoreId)
    (st st1 st1q st1p stClean : SystemState) (sgi : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (returned? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)) (xs : CapTransferSummary)
    (ep : Endpoint) (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId)
    (hReply : endpointReplyOnCore receiver prevCaller msg executingCore st = (st1, .ok sgi))
    (hPop : replyRecvPopDonation replyId prevCaller st1 = .ok (returned?, st1q))
    (hX : replyRecvReplyTransfer none st receiver prevCaller grant st1q = .ok (xs, st1p))
    (hObjInv : (receiveReturnSchedContext true (replyRecvAnswerCaller none st1p prevCaller xs.capInfo) receiver).objects.invExt)
    (hEp : (receiveReturnSchedContext true (replyRecvAnswerCaller none st1p prevCaller xs.capInfo) receiver).getEndpoint? endpointId = some ep) (hHead : ep.sendQ.head = none)
    (hDon : preReceiveDonation? (receiveReturnSchedContext true (replyRecvAnswerCaller none st1p prevCaller xs.capInfo) receiver) receiver = some (scId, owner))
    (hClean : cleanupPreReceiveDonationChecked (receiveReturnSchedContext true (replyRecvAnswerCaller none st1p prevCaller xs.capInfo) receiver)
      receiver = .ok stClean) :
    ∀ p ∈ migrateSchedContextReplenishmentLockSet (determineTargetCore (receiveReturnSchedContext true (replyRecvAnswerCaller none st1p prevCaller xs.capInfo) receiver) receiver)
             (replenishHomeOfSchedContext stClean scId
               (determineTargetCore (receiveReturnSchedContext true (replyRecvAnswerCaller none st1p prevCaller xs.capInfo) receiver) receiver)),
      p ∈ schedLockSet_endpointReplyRecvOnCore endpointId receiver replyId prevCaller msg grant
            executingCore st := by
  intro p hp
  simp only [migrateSchedContextReplenishmentLockSet, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  have hSeg := replyRecvHandoffReplenishCores_eq_of_pop none endpointId receiver replyId
    prevCaller msg grant executingCore st st1 st1q st1p sgi returned? xs hReply hPop hX
  have hPre := receivePreReturnReplenishCores_covers_migration _ stClean endpointId receiver scId
    owner hObjInv (receiveRendezvousSender?_of_blocked _ endpointId ep hEp hHead) hDon hClean
  rcases hp with h | h <;> subst h
  · refine (mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mpr ?_
    rw [hSeg]; simp only [List.mem_append]; exact Or.inr (Or.inr (Or.inl hPre.1))
  · refine (mem_schedFootprintOfCores_replenishQueue_iff _ _ _).mpr ?_
    rw [hSeg]; simp only [List.mem_append]; exact Or.inr (Or.inr (Or.inl hPre.2))

/-- **WS-RR RR8.12 Cut C2 (coverage, the re-donation)**: on a receive leg that
dequeues a `Call` after the pop handed a context back, the footprint covers WS-OD
OD3.6's donation footprint member for member — hence, by
`applyCallDonationOnCoreLockSet_covers_migration`, the SM5.H migration's two
replenish-queue write locks — at the cores the donation **actually** resolves, on the
post-deschedule state it runs on, under the donation's OWN resolver
(`applyRendezvousCallDonation_ok_migrates` is the licence that those are the
migration's endpoints).  Conditioned on all three of the arm's own gates, because
those are the only shapes on which there is a migration to cover; a coverage claim
elsewhere would be covering nothing while reading like coverage. -/
theorem schedLockSet_endpointReplyRecvOnCore_covers_postReceiveDonation
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId)
    (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage) (grant : Bool)
    (executingCore : Concurrency.CoreId)
    (st st1 st1q st1p st2 : SystemState) (sgi sgi2 : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (scId0 scId : SeLe4n.SchedContextId) (holder nextThread : SeLe4n.ThreadId)
    (xs summary : CapTransferSummary)
    (hReply : endpointReplyOnCore receiver prevCaller msg executingCore st = (st1, .ok sgi))
    (hPop : replyRecvPopDonation replyId prevCaller st1 = .ok (some (scId0, holder), st1q))
    (hX : replyRecvReplyTransfer none st receiver prevCaller grant st1q = .ok (xs, st1p))
    (hRecv : endpointReceiveDualWithCapsOnCore endpointId receiver (some replyId) executingCore
        (receiveReturnSchedContext true (replyRecvAnswerCaller none st1p prevCaller xs.capInfo) receiver)
      = (st2, .ok (nextThread, summary, sgi2)))
    (hCall : rendezvousDequeuedCall st2 nextThread = true)
    (hDon : callDonationSchedContext? (replyRecvHolderDeschedule receiver holder st2)
        nextThread receiver = some scId) :
    ∀ p ∈ applyCallDonationOnCoreLockSet
             (determineTargetCore (replyRecvHolderDeschedule receiver holder st2) nextThread)
             (determineTargetCore (replyRecvHolderDeschedule receiver holder st2) receiver),
      p ∈ schedLockSet_endpointReplyRecvOnCore endpointId receiver replyId prevCaller msg grant
            executingCore st := by
  have hSeg := replyRecvHandoffReplenishCores_eq_of_legs none endpointId receiver replyId
    prevCaller msg grant executingCore st st1 st1q st1p st2 sgi sgi2 _ xs nextThread
    summary hReply hPop hX hRecv
  refine schedFootprintOfCores_subset (fun _ h => absurd h (by simp)) (fun c hc => ?_)
  rw [hSeg, replyRecvPostReceiveReplenishCores_of_call receiver nextThread scId0 holder st2 hCall,
    rendezvousCallDonationReplenishCores_of_donation _ receiver nextThread scId hDon]
  simp only [List.mem_append]
  exact Or.inr (Or.inr (Or.inr hc))

/-- **WS-RR RR8.12 Cut C2**: where no hand-off fires — the pop handed nothing back,
the receive leg's block path returns no loan, and the post-receive half's donation
of a dequeued `Call` (the one `.receive` makes) migrates nothing (`hDecl`) — the
segment is empty, so the footprint is the table lock and the run queues alone. -/
theorem replyRecvHandoffReplenishCores_of_no_donation (answer : Option Architecture.FaultReplyOutcome)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId)
    (msg : IpcMessage) (grant : Bool)
    (executingCore : Concurrency.CoreId) (st st1 st1q st1p : SystemState)
    (sgi : Option (Concurrency.CoreId × Concurrency.SgiKind)) (xs : CapTransferSummary)
    (hReply : endpointReplyOnCore receiver prevCaller msg executingCore st = (st1, .ok sgi))
    (hPop : replyRecvPopDonation replyId prevCaller st1 = .ok (none, st1q))
    (hX : replyRecvReplyTransfer answer st receiver prevCaller grant st1q = .ok (xs, st1p))
    (hNoHead : replyFrameHeadContext? st1 replyId = none)
    (hRet : receiveReturnReplenishCoresAt true (replyRecvAnswerCaller answer st1p prevCaller xs.capInfo) receiver = [])
    (hPre : receivePreReturn? (receiveReturnSchedContext true (replyRecvAnswerCaller answer st1p prevCaller xs.capInfo) receiver) endpointId receiver = none)
    (hDecl : ∀ st2 nextThread summary sgi2,
      endpointReceiveDualWithCapsOnCore endpointId receiver (some replyId) executingCore
          (receiveReturnSchedContext true (replyRecvAnswerCaller answer st1p prevCaller xs.capInfo) receiver) =
        (st2, .ok (nextThread, summary, sgi2)) →
      replyRecvPostReceiveReplenishCores receiver nextThread none st2 = []) :
    replyRecvHandoffReplenishCores answer endpointId receiver replyId prevCaller msg grant
      executingCore st = [] := by
  rw [replyRecvHandoffReplenishCores_eq_of_pop answer endpointId receiver replyId prevCaller msg
    grant executingCore st st1 st1q st1p sgi none xs hReply hPop hX,
    replyDonationReturnReplenishCores_of_no_head st1 replyId prevCaller hNoHead, hRet,
    receivePreReturnReplenishCores_of_none _ endpointId
    receiver hPre, List.nil_append, List.nil_append, List.nil_append]
  split
  · rfl
  · next h => exact hDecl _ _ _ _ h

/-- **WS-RR RR8.12 Cut C2 (the empty segment)**: a `.replyRecv` that hands nothing
back and returns no loan declares **no** replenish-queue lock — over-declaring is
sound and not free (SM8.D's CC-5), and
`endpointReplyRecvOnCore_replenishQueueOnCore_of_no_donation` is the licence that the
transition writes none there either. -/
theorem schedLockSet_endpointReplyRecvOnCore_no_replenishQueue_of_no_donation
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId)
    (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage) (grant : Bool)
    (executingCore : Concurrency.CoreId)
    (st st1 st1q st1p : SystemState) (sgi : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (xs : CapTransferSummary)
    (hReply : endpointReplyOnCore receiver prevCaller msg executingCore st = (st1, .ok sgi))
    (hPop : replyRecvPopDonation replyId prevCaller st1 = .ok (none, st1q))
    (hX : replyRecvReplyTransfer none st receiver prevCaller grant st1q = .ok (xs, st1p))
    (hNoHead : replyFrameHeadContext? st1 replyId = none)
    (hRet : receiveReturnReplenishCoresAt true (replyRecvAnswerCaller none st1p prevCaller xs.capInfo) receiver = [])
    (hPre : receivePreReturn? (receiveReturnSchedContext true (replyRecvAnswerCaller none st1p prevCaller xs.capInfo) receiver) endpointId receiver = none)
    (hDecl : ∀ st2 nextThread summary sgi2,
      endpointReceiveDualWithCapsOnCore endpointId receiver (some replyId) executingCore
          (receiveReturnSchedContext true (replyRecvAnswerCaller none st1p prevCaller xs.capInfo) receiver) =
        (st2, .ok (nextThread, summary, sgi2)) →
      replyRecvPostReceiveReplenishCores receiver nextThread none st2 = [])
    (c : Concurrency.CoreId) :
    (LockKey.replenishQueue c, Concurrency.AccessMode.write)
      ∉ schedLockSet_endpointReplyRecvOnCore endpointId receiver replyId prevCaller msg grant
          executingCore st := by
  intro hMem
  have := (mem_schedFootprintOfCores_replenishQueue_iff _ _ c).mp hMem
  rw [replyRecvHandoffReplenishCores_of_no_donation none endpointId receiver replyId prevCaller
    msg grant executingCore st st1 st1q st1p sgi xs hReply hPop hX hNoHead hRet hPre hDecl] at this
  simp at this

/-- **WS-RR RR8.12 Cut C2 (frame)**: the receive leg writes no replenish queue where
`receivePreReturn?` answers `none` — on a rendezvous (the leg itself donates
nothing; the arm's donation is a later step), on a block by a receiver holding no
loan, and on an endpoint the store does not resolve (the leg commits nothing).  The
resolver's `none` is exactly the disjunction of the frames the leg already has. -/
theorem endpointReceiveDualWithCapsOnCore_replenishQueueOnCore_of_no_preReturn
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (hPre : receivePreReturn? st endpointId receiver = none) (c : Concurrency.CoreId) :
    (endpointReceiveDualWithCapsOnCore endpointId receiver replyId executingCore st).1.scheduler.replenishQueueOnCore c
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
            receiver replyId executingCore st ep sender hEp
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
            receiver replyId executingCore st ep hEp hHead
            hNoDon c

/-- The post-receive half on a pop that handed nothing back and a receive leg that
dequeued no `Call` is the chain walk from the recorded server, and nothing else. -/
theorem replyRecvPostReceiveDonation_ok_none_eq (tid recordedServer nextThread : SeLe4n.ThreadId)
    (serverCore : Concurrency.CoreId) (st st' : SystemState) (u : Unit)
    (hNoCall : rendezvousDequeuedCall st nextThread = false)
    (h : replyRecvPostReceiveDonation tid recordedServer nextThread serverCore none st
      = .ok (u, st')) :
    st' = (PriorityInheritance.propagatePipChainCrossCore st recordedServer serverCore).1 := by
  unfold replyRecvPostReceiveDonation at h
  simp only [hNoCall, Bool.false_eq_true, if_false] at h
  exact ((Prod.mk.inj (Except.ok.inj h)).2).symm

/-- On a pop that handed nothing back and a receive leg that dequeued a `Call`, the
post-receive half is the donation `.receive` makes (`applyRendezvousCallDonation`)
followed by the chain walk from the recorded server. -/
theorem replyRecvPostReceiveDonation_ok_none_call (tid recordedServer nextThread : SeLe4n.ThreadId)
    (serverCore : Concurrency.CoreId) (st st' : SystemState) (u : Unit)
    (hCall : rendezvousDequeuedCall st nextThread = true)
    (h : replyRecvPostReceiveDonation tid recordedServer nextThread serverCore none st
      = .ok (u, st')) :
    ∃ st2, applyRendezvousCallDonation st tid nextThread = .ok st2 ∧
      st' = (PriorityInheritance.propagatePipChainCrossCore st2 recordedServer serverCore).1 := by
  unfold replyRecvPostReceiveDonation at h
  simp only [hCall, if_true] at h
  cases hDon : applyRendezvousCallDonation st tid nextThread with
  | error e => rw [hDon] at h; simp only [] at h; cases h
  | ok st2 =>
    rw [hDon] at h; simp only [] at h
    exact ⟨st2, rfl, ((Prod.mk.inj (Except.ok.inj h)).2).symm⟩

/-- ...so it writes no replenish queue outside its segment (WS-RR RR2.20's frame
over the walk, and the donation's own frame at the cores it migrates between)... -/
theorem replyRecvPostReceiveDonation_replenishQueueOnCore_of_none
    (tid recordedServer nextThread : SeLe4n.ThreadId) (serverCore : Concurrency.CoreId)
    (st st' : SystemState) (u : Unit) (hObjInv : st.objects.invExt)
    (h : replyRecvPostReceiveDonation tid recordedServer nextThread serverCore none st
      = .ok (u, st')) (c : Concurrency.CoreId)
    (hne : c ∉ replyRecvPostReceiveReplenishCores tid nextThread none st) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  cases hCall : rendezvousDequeuedCall st nextThread with
  | false =>
    rw [replyRecvPostReceiveDonation_ok_none_eq tid recordedServer nextThread serverCore st st' u
      hCall h]
    exact (PriorityInheritance.propagatePipChainCrossCore_replenish_readings st recordedServer
      serverCore _ hObjInv).1 c
  | true =>
    obtain ⟨st2, hDon, rfl⟩ := replyRecvPostReceiveDonation_ok_none_call tid recordedServer
      nextThread serverCore st st' u hCall h
    rw [replyRecvPostReceiveReplenishCores_none_of_call tid nextThread st hCall] at hne
    have hInv2 := applyRendezvousCallDonation_preserves_objects_invExt _ st2 tid nextThread
      hObjInv hDon
    rw [(PriorityInheritance.propagatePipChainCrossCore_replenish_readings st2 recordedServer
      serverCore _ hInv2).1 c,
      applyRendezvousCallDonation_replenishQueueOnCore_ne _ st2 tid nextThread c hne hDon]

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
      serverCore st st' u hObjInv h c hne
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
  cases hCall : rendezvousDequeuedCall st nextThread with
  | false =>
    rw [replyRecvPostReceiveDonation_ok_none_eq tid recordedServer nextThread serverCore st st' u
      hCall h]
    exact PriorityInheritance.propagatePipChainCrossCore_preserves_objects_invExt st recordedServer
      serverCore _ hObjInv
  | true =>
    obtain ⟨st2, hDon, rfl⟩ := replyRecvPostReceiveDonation_ok_none_call tid recordedServer
      nextThread serverCore st st' u hCall h
    exact PriorityInheritance.propagatePipChainCrossCore_preserves_objects_invExt st2
      recordedServer serverCore _
      (applyRendezvousCallDonation_preserves_objects_invExt _ st2 tid nextThread hObjInv hDon)

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

The post-receive half on a pop that returned nothing donates a dequeued `Call`
caller's context to an `.unbound` receiver, as seL4-MCS's `receiveIPC` and this
kernel's own `.receive` arm do, and that donation migrates replenishments; `hDecl`
is the hypothesis that it migrates none (no `Call` dequeued, a receiver already
bound, or a caller holding no context), the segment's `none` arm read at the
receive leg's post-state. -/
theorem endpointReplyRecvOnCore_replenishQueueOnCore_of_no_donation
    {answer : Option Architecture.FaultReplyOutcome}
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId)
    (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage) (grant : Bool)
    (executingCore : Concurrency.CoreId)
    (st st1 st1q st1p st2 st3 stOut : SystemState) (sgi sgi2 : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (nextThread : SeLe4n.ThreadId) (xs summary summary' : CapTransferSummary)
    (hObjInv : st.objects.invExt)
    (hReply : endpointReplyOnCore receiver prevCaller msg executingCore st = (st1, .ok sgi))
    (hPop : replyRecvPopDonation replyId prevCaller st1 = .ok (none, st1q))
    (hX : replyRecvReplyTransfer answer st receiver prevCaller grant st1q = .ok (xs, st1p))
    (hNoHead : replyFrameHeadContext? st1 replyId = none)
    (hRecv : endpointReceiveDualWithCapsOnCore endpointId receiver (some replyId) executingCore
        (receiveReturnSchedContext true (replyRecvAnswerCaller answer st1p prevCaller xs.capInfo) receiver)
      = (st2, .ok (nextThread, summary, sgi2)))
    (hRet : receiveReturnReplenishCoresAt true (replyRecvAnswerCaller answer st1p prevCaller xs.capInfo) receiver = [])
    (hPre : receivePreReturn? (receiveReturnSchedContext true (replyRecvAnswerCaller answer st1p prevCaller xs.capInfo) receiver) endpointId
      receiver = none)
    (hPost : replyRecvPostReceiveDonation receiver ((recordedReplyServer? st prevCaller).getD receiver)
        nextThread executingCore
        none st2 = .ok ((), st3))
    (hDecl : replyRecvPostReceiveReplenishCores receiver nextThread none st2 = [])
    (hBody : endpointReplyRecvAnsweringOnCore answer endpointId receiver replyId prevCaller msg grant executingCore st = .ok (summary', stOut))
    (c : Concurrency.CoreId) :
    stOut.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  -- the pop hands nothing back, so it commits nothing
  have hPopEq : st1q = st1 :=
    replyRecvPopDonation_ok_none_eq replyId prevCaller st1 st1q hNoHead hPop
  rw [hPopEq] at hPop hX
  -- the body's post-state is the hand-off over `st3`
  unfold endpointReplyRecvAnsweringOnCore at hBody
  simp only [hReply, hPop, hX, hRecv, hPost] at hBody
  have hOut := (Prod.mk.inj (Except.ok.inj hBody)).2
  -- object-store integrity along the spine, for the two walks' frames
  have hInv1 : st1.objects.invExt := by
    have h := endpointReplyOnCore_preserves_objects_invExt receiver prevCaller msg executingCore
      st hObjInv
    rw [hReply] at h; exact h
  have hInv1p : st1p.objects.invExt := replyRecvReplyTransfer_objects_invExt hInv1 hX
  have hInv1a := replyRecvAnswerCaller_preserves_objects_invExt answer st1p prevCaller
    xs.capInfo hInv1p
  have hRa := replyRecvAnswerCaller_replenishQueueOnCore answer st1p prevCaller xs.capInfo c
  generalize (replyRecvAnswerCaller answer st1p prevCaller xs.capInfo) = st1a at hRecv hRet hPre hInv1a hRa
  have hInv2 : st2.objects.invExt := by
    have h := endpointReceiveDualWithCapsOnCore_preserves_objects_invExt endpointId receiver
      (some replyId) executingCore
          (receiveReturnSchedContext true st1a receiver)
      (receiveReturnSchedContext_objects_invExt true st1a receiver hInv1a)
    rw [hRecv] at h; exact h
  have hInv3 : st3.objects.invExt :=
    replyRecvPostReceiveDonation_preserves_objects_invExt_of_none _ _ _ _ st2 st3 () hInv2 hPost
  -- the legs' frames
  have hR1 : st1.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
    have h := endpointReplyOnCore_replenishQueueOnCore receiver prevCaller msg executingCore st c
    rw [hReply] at h; exact h
  have hR2 : st2.scheduler.replenishQueueOnCore c = st1.scheduler.replenishQueueOnCore c := by
    have h := endpointReceiveDualWithCapsOnCore_replenishQueueOnCore_of_no_preReturn endpointId
      receiver (some replyId) executingCore
          (receiveReturnSchedContext true st1a receiver) hPre c
    rw [hRecv, receiveReturnSchedContext_replenishQueueOnCore_ne true st1a receiver hInv1a c
      (by rw [hRet]; simp), hRa, replyRecvReplyTransfer_scheduler_eq hX] at h; exact h
  have hR3 : st3.scheduler.replenishQueueOnCore c = st2.scheduler.replenishQueueOnCore c :=
    replyRecvPostReceiveDonation_replenishQueueOnCore_of_none _ _ _ _ st2 st3 () hInv2 hPost c
      (by rw [hDecl]; simp)
  rw [← hOut]
  rcases applyReceiveLegPipHandoff_cases st3 receiver nextThread
      ((recordedReplyServer? st prevCaller).getD receiver) executingCore with hH | hH
  · rw [hH, hR3, hR2, hR1]
  · rw [hH]
    unfold applyReceiverPipHandoff
    rw [(PriorityInheritance.propagatePipChainCrossCore_replenish_readings st3 receiver
      executingCore st3.objects.size hInv3).1 c, hR3, hR2, hR1]


/-- **WS-RR RR8.12 Cut C6e (the exactness frame)**: the live `.replyRecv` arm
writes no replenish queue outside `replyRecvHandoffReplenishCores` — the
FOOTPRINT's own segment, with no hypothesis about which path any of the four
stages took.

The `_of_no_donation` sibling above says the arm migrates *nothing* where all
three hand-offs decline; this says *where* it migrates when they answer, which is
what the replenish clause of `footprintCoversWrites` needs.  Each stage's own
`_ne` is stated at the very sub-segment the definition appends at that stage — the
pop's pair, the block path's pair, the re-donation's pair — so this proof is the
composition `replyRecvHandoffReplenishCores_eq_of_legs` already names rather than a
second reading of the arm.  The tail (the priority hand-off and the two stagers)
writes run queues and register contexts and no replenish queue at all. -/
theorem endpointReplyRecvOnCore_replenishQueueOnCore_ne
    {answer : Option Architecture.FaultReplyOutcome}
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId)
    (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage) (grant : Bool)
    (executingCore : Concurrency.CoreId)
    (st stOut : SystemState) (summary' : CapTransferSummary) (c : Concurrency.CoreId)
    (hObjInv : st.objects.invExt)
    (hne : c ∉ replyRecvHandoffReplenishCores answer endpointId receiver replyId prevCaller msg
      grant executingCore st)
    (hBody : endpointReplyRecvAnsweringOnCore answer endpointId receiver replyId prevCaller msg
      grant executingCore st = .ok (summary', stOut)) :
    stOut.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  unfold endpointReplyRecvAnsweringOnCore at hBody
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
        obtain ⟨returned?, st1q⟩ := popPair
        rw [hPop] at hBody
        simp only [] at hBody
        obtain ⟨⟨xs, st1p⟩, hX⟩ := replyRecvReplyTransfer_ok answer st receiver prevCaller grant st1q
        rw [hX] at hBody
        simp only [] at hBody
        cases hRecv : endpointReceiveDualWithCapsOnCore endpointId receiver (some replyId) executingCore
            (receiveReturnSchedContext true (replyRecvAnswerCaller answer st1p prevCaller xs.capInfo)
              receiver) with
        | mk st2 res2 =>
          rw [hRecv] at hBody
          cases res2 with
          | error e => simp only [] at hBody; cases hBody
          | ok triple =>
            obtain ⟨nextThread, summary, sgi2⟩ := triple
            simp only [] at hBody
            -- The segment, decomposed at the two legs the definition reads it through.
            rw [replyRecvHandoffReplenishCores_eq_of_legs answer endpointId receiver replyId
              prevCaller msg grant executingCore st st1 st1q st1p st2 replySgi sgi2
              returned? xs nextThread summary hReply hPop hX hRecv] at hne
            simp only [List.mem_append, not_or] at hne
            obtain ⟨hnePop, hneRet, hnePre, hnePost⟩ := hne
            have hInv1q : st1q.objects.invExt :=
              replyRecvPopDonation_preserves_objects_invExt replyId prevCaller st1 st1q returned?
                hInv1 hPop
            have hInv1p : st1p.objects.invExt := replyRecvReplyTransfer_objects_invExt hInv1q hX
            have hInv1a := replyRecvAnswerCaller_preserves_objects_invExt answer st1p prevCaller
              xs.capInfo hInv1p
            have hRa := replyRecvAnswerCaller_replenishQueueOnCore answer st1p prevCaller
              xs.capInfo c
            generalize replyRecvAnswerCaller answer st1p prevCaller xs.capInfo = st1a at hRecv hneRet hnePre hInv1a hRa
            have hInv2 : st2.objects.invExt := by
              have h := endpointReceiveDualWithCapsOnCore_preserves_objects_invExt endpointId
                receiver (some replyId) executingCore
                    (receiveReturnSchedContext true st1a receiver)
                (receiveReturnSchedContext_objects_invExt true st1a receiver hInv1a)
              rw [hRecv] at h; exact h
            have hR1p : st1a.scheduler.replenishQueueOnCore c
                = st1.scheduler.replenishQueueOnCore c := by
              rw [hRa, replyRecvReplyTransfer_scheduler_eq hX]
              exact replyRecvPopDonation_replenishQueueOnCore_ne replyId prevCaller st1 st1q
                returned? c hInv1 hnePop hPop
            have hR2 : st2.scheduler.replenishQueueOnCore c
                = st1a.scheduler.replenishQueueOnCore c := by
              rw [← receiveReturnSchedContext_replenishQueueOnCore_ne true st1a receiver hInv1a c
                hneRet]
              exact endpointReceiveDualWithCapsOnCore_replenishQueueOnCore_ne endpointId receiver
                (some replyId) executingCore
                (receiveReturnSchedContext true st1a receiver) st2
                nextThread summary sgi2 c
                (receiveReturnSchedContext_objects_invExt true st1a receiver hInv1a) hnePre hRecv
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
              rw [← hOut]
              rcases applyReceiveLegPipHandoff_cases st3 receiver nextThread
                  ((recordedReplyServer? st prevCaller).getD receiver) executingCore with hH | hH
              · rw [hH, hR3, hR2, hR1p, hR1]
              · rw [hH]
                unfold applyReceiverPipHandoff
                rw [(PriorityInheritance.propagatePipChainCrossCore_replenish_readings st3 receiver
                  executingCore st3.objects.size hInv3).1 c, hR3, hR2, hR1p, hR1]


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
    (executingCore : Concurrency.CoreId) (st st1 stDon : SystemState) (dequeued : SeLe4n.ThreadId)
    (summary : CapTransferSummary) (sgi : Option (Concurrency.CoreId × Concurrency.SgiKind)) (c : Concurrency.CoreId)
    (hObjInv : st.objects.invExt) (hHeads : queueHeadBlockedConsistent st)
    (hne : c ∉ endpointReceiveHandoffReplenishCores st endpointId receiver replyId.isSome)
    (hLeg : endpointReceiveDualWithCapsOnCore endpointId receiver replyId executingCore st = (st1, .ok (dequeued, summary, sgi)))
    (hDon : applyReceiveRendezvousDonation st1 receiver dequeued = .ok stDon) :
    stDon.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  cases hSender : receiveRendezvousSender? st endpointId with
  | none =>
    -- The BLOCK path: the leg dequeued nobody and reports the receiver's own id,
    -- and a thread donates nothing to itself.
    have hDq : dequeued = receiver :=
      endpointReceiveDualWithCapsOnCore_ok_dequeued_eq_receiver_of_blocked endpointId receiver
        replyId executingCore st st1 dequeued summary sgi
        hSender hLeg
    subst hDq
    have hCallSender : receiveRendezvousLinkedCaller? st endpointId replyId.isSome = none := by
      unfold receiveRendezvousLinkedCaller?
      rw [hSender]
      rfl
    have hDonating : receiveRendezvousDonatingSender? st endpointId dequeued replyId.isSome = none :=
      receiveRendezvousDonatingSender?_of_no_callSender st endpointId dequeued replyId.isSome
        hCallSender
    have hLegNe : c ∉ receivePreReturnReplenishCores st endpointId dequeued := by
      rw [show endpointReceiveHandoffReplenishCores st endpointId dequeued replyId.isSome
            = receivePreReturnReplenishCores st endpointId dequeued by
          unfold endpointReceiveHandoffReplenishCores; rw [hDonating]] at hne
      exact hne
    have hR1 := endpointReceiveDualWithCapsOnCore_replenishQueueOnCore_ne endpointId dequeued
      replyId executingCore st st1 dequeued summary sgi c
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
      endpointReceiveDualWithCapsOnCore_ok_dequeued_eq_head endpointId receiver replyId executingCore st st1 dequeued summary sgi ep sender
        hEp hHead hLeg
    subst hDq
    -- A rendezvous returns no loan, so the leg's own segment is empty.
    have hR1 := endpointReceiveDualWithCapsOnCore_replenishQueueOnCore_ne endpointId receiver
      replyId executingCore st st1 dequeued summary sgi c
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
        endpointId receiver replyId executingCore st ep
        dequeued hObjInv hEp hHead
      rw [hLeg] at hBindFrame
      have hDonPre : callDonationSchedContext? st dequeued receiver = some scId :=
        callDonationSchedContext?_some_of_sameSchedContextBindings hBindFrame dequeued receiver
          scId hDonPost
      by_cases hLinked : receiveRendezvousLinkedCaller? st endpointId replyId.isSome = some dequeued
      · -- A donating `Call` rendezvous the receive LINKS: the segment names the pair,
        -- at the pre-state, and the leg moves no thread's home core.
        have hDonating : receiveRendezvousDonatingSender? st endpointId receiver replyId.isSome
            = some dequeued :=
          receiveRendezvousDonatingSender?_of_donation st endpointId receiver replyId.isSome
            dequeued scId hLinked hDonPre
        rw [show endpointReceiveHandoffReplenishCores st endpointId receiver replyId.isSome
              = [determineTargetCore st dequeued, determineTargetCore st receiver] by
            unfold endpointReceiveHandoffReplenishCores; rw [hDonating]] at hne
        have hHome : ∀ x, determineTargetCore st1 x = determineTargetCore st x := fun x => by
          have h := endpointReceiveDualWithCapsOnCore_determineTargetCore_eq_of_rendezvous
            endpointId receiver replyId executingCore st ep
            dequeued x hObjInv hEp hHead
          rw [hLeg] at h
          exact h
        have hSeg : rendezvousCallDonationReplenishCores st1 receiver dequeued
            = [determineTargetCore st dequeued, determineTargetCore st receiver] := by
          unfold rendezvousCallDonationReplenishCores
          rw [hDonPost, hHome dequeued, hHome receiver]
        exact applyReceiveRendezvousDonation_replenishQueueOnCore_ne st1 stDon receiver dequeued c
          (by rw [hSeg]; exact hne) hDon
      · -- A rendezvous the receive links to no reply -- a plain `Send`, or a `Call`
        -- whose cap grants no reply or whose receive supplied none: the leg leaves the
        -- dequeued thread `.ready`, so the post-state guard is false and the donation
        -- is the identity however the resolver answers.
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
        have hGuard : rendezvousDequeuedCall
            (endpointReceiveDualWithCapsOnCore endpointId receiver replyId executingCore st).1
              dequeued = false := by
          rcases hShape with hSend | hCall
          · exact endpointReceiveDualWithCapsOnCore_not_dequeuedCall_of_blockedOnSend
              endpointId receiver replyId executingCore st ep
              dequeued senderTcb endpointId hObjInv hEp hHead hTcb hSend
          · cases hLk : ((senderTcb.ipcCanGrant || senderTcb.ipcCanGrantReply) && replyId.isSome) with
            | false =>
              exact endpointReceiveDualWithCapsOnCore_not_dequeuedCall_of_noLink
                endpointId receiver replyId executingCore st ep
                dequeued senderTcb endpointId hObjInv hEp hHead hTcb hCall hLk
            | true =>
              rw [Bool.and_eq_true] at hLk
              exact absurd (receiveRendezvousLinkedCaller?_of_blockedOnCall st endpointId
                replyId.isSome ep dequeued senderTcb endpointId hEp hHead hTcb hCall hLk.1 hLk.2)
                hLinked
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
theorem endpointReplyRecvOnCore_preserves_objects_invExt
    {answer : Option Architecture.FaultReplyOutcome}
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId)
    (msg : IpcMessage) (grant : Bool)
    (executingCore : Concurrency.CoreId) (st st' : SystemState) (summary : CapTransferSummary)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReplyRecvAnsweringOnCore answer endpointId receiver replyId prevCaller msg
      grant executingCore st = .ok (summary, st')) :
    st'.objects.invExt := by
  have hInv1 := endpointReplyOnCore_preserves_objects_invExt receiver prevCaller msg
    executingCore st hObjInv
  unfold endpointReplyRecvAnsweringOnCore at hStep
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
        obtain ⟨returnedSc?, st1q⟩ := popPair
        rw [hPop] at hStep
        simp only [] at hStep
        obtain ⟨⟨xs, st1p⟩, hX⟩ := replyRecvReplyTransfer_ok answer st receiver prevCaller grant st1q
        rw [hX] at hStep
        simp only [] at hStep
        have hInv1p : st1p.objects.invExt :=
          replyRecvReplyTransfer_objects_invExt
            (replyRecvPopDonation_preserves_objects_invExt replyId prevCaller st1 st1q
              returnedSc? hInv1 hPop) hX
        have hInv1a := replyRecvAnswerCaller_preserves_objects_invExt answer st1p prevCaller
          xs.capInfo hInv1p
        generalize replyRecvAnswerCaller answer st1p prevCaller xs.capInfo = st1a at hStep hInv1a
        have hInv2 := endpointReceiveDualWithCapsOnCore_preserves_objects_invExt endpointId
          receiver (some replyId) executingCore
              (receiveReturnSchedContext true st1a receiver)
              (receiveReturnSchedContext_objects_invExt true st1a receiver hInv1a)
        cases hRcv : endpointReceiveDualWithCapsOnCore endpointId receiver (some replyId) executingCore
            (receiveReturnSchedContext true st1a receiver) with
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
              exact applyReceiveLegPipHandoff_preserves_objects_invExt _ _ _ _ _ hInv3

open SeLe4n.Kernel.Concurrency in
/-- **Audit IPC-2** (**WS-LS LS2.1**: over the pair, hypothesis-free): under the
`.replyRecv` footprint the live ReplyRecv is observationally atomic to any
thread's IPC state — the field both legs write.

The transition is `Kernel`-shaped (a failure carries no state), so the 2PL
bracket runs its state-threading form: the post-state on success, the input
state on failure.  The lock-set arguments are the full `lockSet_replyRecv`
arity, so the claim covers every footprint the arm can declare.  The `invExt`
hypothesis and the acquire-fold conjunct are dropped because the growing phase
no longer touches the kernel state — a strengthening (plan O6);
`endpointReplyRecvOnCore_preserves_objects_invExt` above stands on its own. -/
theorem endpointReplyRecvOnCore_observer_atomic
    (endpointId : SeLe4n.ObjId) (receiver prevCaller : SeLe4n.ThreadId) (msg : IpcMessage)
    (grant : Bool) (replyId : SeLe4n.ReplyId)
    (executingCore : Concurrency.CoreId)
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
    -- **WS-ZA ZA4.6/ZA4.7**: and at the reply-waiter and sender-CSpace-root
    -- arities, rather than at their defaults.
    (rwPrev? rwNext? rwHead? : Option SeLe4n.ThreadId) (senderRoot? : Option SeLe4n.ObjId)
    (s : LockedSystemState) :
    let S := lockSet_replyRecv receiver cnRoot prevCaller endpointId newSender? donatedSc?
      donatedOwner? (some replyId) installsCaps donationServer? redonatedSc?
      belowHeadReply? outerCaller? queueNeighbour? redonationOldHead? donatedHead?
      preReturnSc? preReturnOwner? preReturnHead? preReturnBelowHead?
      preReturnOuterCaller? answeredFrameAbove? answeredFrameBelow?
      rwPrev? rwNext? rwHead? senderRoot?
    let action : SystemState → SystemState × Except KernelError CapTransferSummary :=
      fun s' => match endpointReplyRecvOnCore endpointId receiver replyId prevCaller msg grant
          executingCore s' with
        | .ok (r, s'') => (s'', .ok r)
        | .error e => (s', .error e)
    threadIpcStateObserver observed (withLockSet S executingCore action s).1.kernel
      = threadIpcStateObserver observed (action s.kernel).1 := by
  intro S action
  exact lockSet_observer_atomic S executingCore action s _



-- ============================================================================
-- WS-SX SX33: the donation pop's admission, read before the reply leg
-- ============================================================================
--
-- seL4-MCS's `reply_pop` cannot refuse, so the reply-receive decides every pop
-- refusal before the reply leg's first write (`replyRecvPopAdmits`).  The
-- four sub-pops' commit tests are exact (`*_of_ok` below with the existing
-- `*_ok_of_commits`), and the leg keeps every read of the test but the answered
-- caller's own state (`endpointReplyOnCore_popCommits`).

/-- A context store over a stored context, then the head pop, looks every
thread up as the state before them did. -/
theorem lookupTcb_of_contextStore_headPop {st s1 s2 : SystemState}
    {scId : SeLe4n.SchedContextId} {sc sc' : SchedContext}
    {head? : Option (SeLe4n.ReplyId × Reply)} (hInv : st.objects.invExt)
    (hSc : st.objects[scId.toObjId]? = some (.schedContext sc))
    (h1 : storeObject scId.toObjId (.schedContext sc') st = .ok ((), s1))
    (h2 : storeDonationHeadPop scId head? s1 = .ok s2) (t : SeLe4n.ThreadId) :
    lookupTcb s2 t = lookupTcb st t := by
  have hInv1 := storeObject_preserves_objects_invExt st s1 _ _ hInv h1
  have hG := storeObject_schedContextAt_getTcb?_eq st s1 scId sc sc'
    ((SystemState.getSchedContext?_eq_some_iff _ _ _).mpr hSc) hInv h1 t
  unfold lookupTcb
  rw [storeDonationHeadPop_getTcb?_eq hInv1 h2 t, hG]

/-- A TCB store keeps every thread stored. -/
theorem lookupTcb_isSome_of_tcbStore {s s' : SystemState} {k : SeLe4n.ThreadId} {t0 : TCB}
    (hInv : s.objects.invExt) (hk : (lookupTcb s k).isSome)
    (hS : storeObject k.toObjId (.tcb t0) s = .ok ((), s')) (t : SeLe4n.ThreadId)
    (h : (lookupTcb s' t).isSome) : (lookupTcb s t).isSome := by
  by_cases e : t.toObjId = k.toObjId
  · have : t = k := SeLe4n.ThreadId.toObjId_injective _ _ e
    subst this; exact hk
  · unfold lookupTcb at h ⊢
    rw [storeObject_getTcb?_ne s s' _ _ t e hInv hS] at h
    exact h

/-- **A donation return that succeeds was admitted**: every check
`donatedReturnCommits` makes is one the return made on its way to success. -/
theorem donatedReturnCommits_of_ok {st st' : SystemState}
    {serverTid : SeLe4n.ThreadId} {scId : SeLe4n.SchedContextId} {originalOwner : SeLe4n.ThreadId}
    (hInv : st.objects.invExt)
    (h : returnDonatedSchedContextResolved st serverTid scId originalOwner = .ok st') :
    donatedReturnCommits st serverTid scId originalOwner = true := by
  obtain ⟨n, hRes, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose h
  obtain ⟨sc0, hSc0, hB⟩ := returnDonatedSchedContext_ok_implies_sc_bound _ _ _ _ _ _ hPop
  obtain ⟨sc, head?, ct, svt, s1, s2, s3, s4, hSc, hOut, hRcp, _, h1, h2, hL2, h3, hL3, _, _⟩ :=
    returnDonatedSchedContext_ok_storeChain _ _ _ _ _ _ hPop
  have hScG : st.getSchedContext? scId = some sc :=
    (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr hSc
  rw [hScG] at hSc0; cases hSc0
  have hEq := lookupTcb_of_contextStore_headPop hInv hSc h1 h2
  have hInv2 := storeDonationHeadPop_preserves_objects_invExt
    (storeObject_preserves_objects_invExt st s1 _ _ hInv h1) h2
  have hOw : (lookupTcb st originalOwner).isSome := by rw [← hEq, hL2]; rfl
  have hSv : (lookupTcb st serverTid).isSome := by
    rw [← hEq]
    exact lookupTcb_isSome_of_tcbStore hInv2 (by rw [hL2]; rfl) h3 serverTid (by rw [hL3]; rfl)
  unfold donatedReturnCommits
  rw [hRes]; simp only []; rw [hScG]
  simp only [hB, beq_self_eq_true, hOut, hRcp, hOw, hSv, Bool.and_self]

/-- **A held pop that succeeds was admitted** (`keptPopCommits`). -/
theorem keptPopCommits_of_ok {st st' : SystemState} {holder : SeLe4n.ThreadId}
    {scId : SeLe4n.SchedContextId} (hInv : st.objects.invExt)
    (h : keepDonatedSchedContextResolved st holder scId = .ok st') :
    keptPopCommits st holder scId = true := by
  obtain ⟨n, hRes, hPop⟩ := keepDonatedSchedContextResolved_ok_decompose h
  obtain ⟨sc, head?, ht, s1, s2, hBind, hSc, hB, hOut, _, h1, h2, hL2, _⟩ :=
    keepDonatedSchedContext_ok_storeChainGuarded hPop
  have hScG : st.getSchedContext? scId = some sc :=
    (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr hSc
  have hEq := lookupTcb_of_contextStore_headPop hInv hSc h1 h2 holder
  unfold keptPopCommits
  rw [hRes]; simp only []; rw [hScG]
  simp only [hB, beq_self_eq_true, hOut, ← hEq, hL2, Option.bind_some, hBind, Bool.and_self]

/-- **An unheld pop that succeeds was admitted** (`unheldReturnCommits`). -/
theorem unheldReturnCommits_of_ok {st st' : SystemState} {scId : SeLe4n.SchedContextId}
    {owner : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : returnUnheldSchedContextResolved st scId owner = .ok st') :
    unheldReturnCommits st scId owner = true := by
  obtain ⟨n, hRes, hPop⟩ := returnUnheldSchedContextResolved_ok_decompose h
  obtain ⟨sc, head?, ot, s1, s2, s3, hSc, hB, hOut, hRcp, _, h1, h2, hL2, _⟩ :=
    returnUnheldSchedContext_ok_storeChain _ _ _ _ _ hPop
  have hScG : st.getSchedContext? scId = some sc :=
    (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr hSc
  have hEq := lookupTcb_of_contextStore_headPop hInv hSc h1 h2 owner
  unfold unheldReturnCommits
  rw [hRes]; simp only []; rw [hScG]
  simp only [hB, beq_self_eq_true, hOut, hRcp, ← hEq, hL2, Option.isSome_some, Bool.and_self]

/-- **A sever that succeeds was admitted** (`unheldSeverCommits`). -/
theorem unheldSeverCommits_of_ok {st st' : SystemState} {scId : SeLe4n.SchedContextId}
    (h : severUnheldSchedContextResolved st scId = .ok st') :
    unheldSeverCommits st scId = true := by
  obtain ⟨n, hRes, hPop⟩ := severUnheldSchedContextResolved_ok_decompose h
  obtain ⟨sc, _, _, hSc, hB, _⟩ := severUnheldSchedContext_ok_storeChain hPop
  have hScG : st.getSchedContext? scId = some sc :=
    (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr hSc
  unfold unheldSeverCommits
  rw [hRes]; simp only []; rw [hScG]
  simp only [hB, beq_self_eq_true]

/-- **The donation pop commits exactly where `replyRecvPopCommits` admits.** -/
theorem replyRecvPopDonation_ok_iff_commits {st : SystemState} {rid : SeLe4n.ReplyId}
    {target : SeLe4n.ThreadId} (hInv : st.objects.invExt) :
    (∃ r, replyRecvPopDonation rid target st = .ok r) ↔
      replyRecvPopCommits st rid target = true := by
  unfold replyRecvPopDonation replyRecvPopCommits
  cases hH : replyFrameHeadHolder? st rid with
  | some p =>
    obtain ⟨scId, holder⟩ := p
    simp only []
    cases hV : holder.toValid? with
    | none => simp
    | some hv =>
    cases hT : target.toValid? with
    | none => simp
    | some tv =>
    simp only [Option.isSome_some, Bool.true_and]
    cases hA : donationRecipientAcceptable st target with
    | true =>
      rw [heldPopCommits_of_acceptable hA]
      simp only [↓reduceIte]
      constructor
      · rintro ⟨r, hr⟩
        cases hR : returnDonatedSchedContextResolved st holder scId target with
        | error e => rw [hR] at hr; cases hr
        | ok s => exact donatedReturnCommits_of_ok hInv hR
      · intro hc
        obtain ⟨s, hs⟩ := returnDonatedSchedContextResolved_ok_of_commits hInv hc
        exact ⟨_, by rw [hs]⟩
    | false =>
      rw [heldPopCommits_of_not_acceptable hA]
      simp only [Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro ⟨r, hr⟩
        cases hR : keepDonatedSchedContextResolved st holder scId with
        | error e => rw [hR] at hr; cases hr
        | ok s => exact keptPopCommits_of_ok hInv hR
      · intro hc
        obtain ⟨s, hs⟩ := keepDonatedSchedContextResolved_ok_of_commits hInv hc
        exact ⟨_, by rw [hs]⟩
  | none =>
    simp only []
    unfold popUnheldReplyHead
    cases hC : replyFrameHeadContext? st rid with
    | none => simp
    | some scId =>
      simp only []
      unfold unheldPopCommits
      cases hA : donationRecipientAcceptable st target with
      | true =>
        simp only [↓reduceIte]
        constructor
        · rintro ⟨r, hr⟩
          cases hR : returnUnheldSchedContextResolved st scId target with
          | error e => rw [hR] at hr; cases hr
          | ok s => exact unheldReturnCommits_of_ok hInv hR
        · intro hc
          obtain ⟨s, hs⟩ := returnUnheldSchedContextResolved_ok_of_commits hInv hc
          exact ⟨_, by rw [hs]⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        constructor
        · rintro ⟨r, hr⟩
          cases hR : severUnheldSchedContextResolved st scId with
          | error e => rw [hR] at hr; cases hr
          | ok s => exact unheldSeverCommits_of_ok hR
        · intro hc
          obtain ⟨s, hs⟩ := severUnheldSchedContextResolved_ok_of_commits hInv hc
          exact ⟨_, by rw [hs]⟩

/-- **What the reply leg keeps of the donation pop's reads**: every context,
every frame but `rid`, `rid`'s links, every binding and every thread's IPC
state but the answered caller's, which it leaves ready. -/
structure ReplyPopReadsAgree (st st1 : SystemState) (rid : SeLe4n.ReplyId) (c : SeLe4n.ThreadId) :
    Prop where
  sc : ∀ s, st1.getSchedContext? s = st.getSchedContext? s
  reply : ∀ r, r ≠ rid → st1.getReply? r = st.getReply? r
  links : (st1.getReply? rid).map (fun x => (x.next, x.prev)) =
    (st.getReply? rid).map (fun x => (x.next, x.prev))
  bind : ∀ t, (st1.getTcb? t).map TCB.schedContextBinding =
    (st.getTcb? t).map TCB.schedContextBinding
  ipc : ∀ t, t ≠ c → (st1.getTcb? t).map TCB.ipcState = (st.getTcb? t).map TCB.ipcState
  ready : ∀ x, st1.getTcb? c = some x → x.ipcState = .ready

namespace ReplyPopReadsAgree
variable {st st1 : SystemState} {rid : SeLe4n.ReplyId} {c : SeLe4n.ThreadId}

theorem headContext (h : ReplyPopReadsAgree st st1 rid c) :
    replyFrameHeadContext? st1 rid = replyFrameHeadContext? st rid := by
  have hL := h.links
  unfold replyFrameHeadContext?
  cases h1 : st1.getReply? rid with
  | none =>
    rw [h1] at hL
    cases h0 : st.getReply? rid with
    | none => rfl
    | some _ => rw [h0] at hL; cases hL
  | some r1 =>
    rw [h1] at hL
    cases h0 : st.getReply? rid with
    | none => rw [h0] at hL; cases hL
    | some r0 =>
      rw [h0] at hL
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hL
      simp only [hL.1, h.sc]

theorem headHolder (h : ReplyPopReadsAgree st st1 rid c) :
    replyFrameHeadHolder? st1 rid = replyFrameHeadHolder? st rid := by
  unfold replyFrameHeadHolder?
  rw [h.headContext]
  split <;> simp only [h.sc]

theorem lookupTcb_bind (h : ReplyPopReadsAgree st st1 rid c) (t : SeLe4n.ThreadId) :
    (lookupTcb st1 t).map TCB.schedContextBinding = (lookupTcb st t).map TCB.schedContextBinding := by
  unfold lookupTcb; split
  · rfl
  · exact h.bind t

theorem lookupTcb_isSome (h : ReplyPopReadsAgree st st1 rid c) (t : SeLe4n.ThreadId) :
    (lookupTcb st1 t).isSome = (lookupTcb st t).isSome := by
  have := h.lookupTcb_bind t
  cases a : lookupTcb st1 t <;> cases b : lookupTcb st t <;> simp_all

theorem recipient (h : ReplyPopReadsAgree st st1 rid c) (t : SeLe4n.ThreadId) :
    donationRecipientAcceptable st1 t = donationRecipientAcceptable st t := by
  have := h.lookupTcb_bind t
  unfold donationRecipientAcceptable
  cases a : lookupTcb st1 t <;> cases b : lookupTcb st t <;> simp_all

theorem heldOuter (h : ReplyPopReadsAgree st st1 rid c) (holder : SeLe4n.ThreadId)
    (n : Option SeLe4n.ThreadId) : heldPopOuter? st1 holder n = heldPopOuter? st holder n := by
  have := h.bind holder
  unfold heldPopOuter?
  cases a : st1.getTcb? holder <;> cases b : st.getTcb? holder <;> simp_all

/-- Off the answered caller, the outer caller is read as before the leg. -/
theorem outer_of_ne (h : ReplyPopReadsAgree st st1 rid c) (s o : SeLe4n.ThreadId)
    (n : Option SeLe4n.ThreadId) (hn : n ≠ some c) :
    outerCallerAcceptable st1 s o n = outerCallerAcceptable st s o n := by
  cases n with
  | none => rfl
  | some x =>
    have hx : x ≠ c := fun e => hn (by rw [e])
    have hB := h.bind x
    have hI := h.ipc x hx
    unfold outerCallerAcceptable
    cases a : st1.getTcb? x <;> cases b : st.getTcb? x <;> simp_all

/-- On the answered caller, the leg made it ready, so it is no outer caller. -/
theorem outer_caller (h : ReplyPopReadsAgree st st1 rid c) (s o : SeLe4n.ThreadId) :
    outerCallerAcceptable st1 s o (some c) = false := by
  unfold outerCallerAcceptable
  cases a : st1.getTcb? c with
  | none => simp [a]
  | some x => simp [a, h.ready x a]

/-- At the frame's own context, the reply-stack resolver reads as before the
leg: the leg kept the frame's links and every other frame. -/
theorem outerCaller (h : ReplyPopReadsAgree st st1 rid c) {scId : SeLe4n.SchedContextId}
    (hH : replyFrameHeadContext? st rid = some scId) :
    replyStackOuterCaller? st1 scId = replyStackOuterCaller? st scId := by
  obtain ⟨r, sc, hR, hN, hSc, hSR⟩ := replyFrameHeadContext?_eq_some hH
  have hL := h.links
  rw [hR] at hL
  cases h1 : st1.getReply? rid with
  | none => rw [h1] at hL; cases hL
  | some r1 =>
  rw [h1] at hL
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hL
  obtain ⟨hN1, hP1⟩ := hL
  unfold replyStackOuterCaller? donationHeadOf?
  rw [h.sc, hSc]
  simp only [hSR, h1, hR, hN1, hN, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hP1]
  cases hPr : r.prev with
  | none => rfl
  | some below =>
    simp only []
    by_cases hb : below = rid
    · subst hb
      simp only [h1, hR, hN1, hN]
      rfl
    · rw [h.reply below hb]
end ReplyPopReadsAgree

namespace ReplyPopReadsAgree
variable {st st1 : SystemState} {rid : SeLe4n.ReplyId} {c : SeLe4n.ThreadId}

/-- The pop's commit test on the kept state is the admission on the first. -/
theorem commits (h : ReplyPopReadsAgree st st1 rid c) :
    replyRecvPopCommits st1 rid c = replyRecvPopAdmitsCore st rid c := by
  unfold replyRecvPopCommits replyRecvPopAdmitsCore
  rw [h.headHolder]
  cases hH : replyFrameHeadHolder? st rid with
  | some p =>
    obtain ⟨scId, holder⟩ := p
    simp only []
    have hHC : replyFrameHeadContext? st rid = some scId := by
      unfold replyFrameHeadHolder? at hH
      split at hH
      · cases hH
      · next s hs => split at hH; · cases hH
                     · cases hH; exact hs
    have hRes := h.outerCaller hHC
    unfold heldPopCommits
    rw [h.recipient c]
    split
    · unfold donatedReturnCommits
      rw [hRes, h.sc]
      split
      · rfl
      · next n _ =>
        split
        · rfl
        · by_cases hn : n = some c
          · subst hn
            simp only [h.outer_caller, Bool.and_false, Bool.false_and]
            unfold outerCallerAcceptable; simp
          · rw [h.outer_of_ne _ _ _ hn, h.recipient c, h.lookupTcb_isSome, h.lookupTcb_isSome]
    · unfold keptPopCommits keptPopOuterIsNot
      rw [hRes, h.sc]
      split
      · rfl
      · next n hN =>
        rw [h.heldOuter]
        simp only [hN]
        have hbd : (lookupTcb st1 holder).bind (fun ht => ht.schedContextBinding.scId?) =
            (lookupTcb st holder).bind (fun ht => ht.schedContextBinding.scId?) := by
          have hb := h.lookupTcb_bind holder
          cases a : lookupTcb st1 holder <;> cases b : lookupTcb st holder <;> simp_all
        split
        · simp
        · by_cases hn : heldPopOuter? st holder n = some c
          · rw [hn, h.outer_caller]; simp
          · rw [h.outer_of_ne _ _ _ hn, hbd]
            have hn' : (heldPopOuter? st holder n != some c) = true := by simpa using hn
            rw [hn', Bool.and_true]
  | none =>
    simp only []
    rw [h.headContext]
    split
    · rfl
    · next scId hC =>
      have hRes := h.outerCaller hC
      unfold unheldPopCommits unheldReturnCommits unheldSeverCommits
      rw [h.recipient c, hRes, h.sc]
      split
      · split
        · rfl
        · next n _ =>
          split
          · rfl
          · by_cases hn : n = some c
            · subst hn
              simp only [h.outer_caller, Bool.and_false, Bool.false_and]
              unfold outerCallerAcceptable; simp
            · rw [h.outer_of_ne _ _ _ hn, h.lookupTcb_isSome]
      · rfl
end ReplyPopReadsAgree

/-- The consume leaves a reply it does not find absent. -/
theorem consumeCallerReply_getReply?_none {st st' : SystemState} {caller : SeLe4n.ThreadId}
    {rid : SeLe4n.ReplyId} (hObjInv : st.objects.invExt) (hGet : st.getReply? rid = none)
    (h : SystemState.consumeCallerReply caller rid st = .ok ((), st')) :
    st'.getReply? rid = none := by
  unfold SystemState.consumeCallerReply SystemState.consumeReply at h
  rw [hGet] at h
  simp only [] at h
  cases hT : st.getTcb? caller with
  | none => rw [hT] at h; cases h; exact hGet
  | some t =>
    rw [hT] at h
    simp only [] at h
    have hTo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
    unfold SystemState.getReply? at hGet ⊢
    by_cases e : rid.toObjId = caller.toObjId
    · rw [e, storeObject_objects_eq st st' _ _ hObjInv h]
    · rw [storeObject_objects_ne st st' _ _ _ e hObjInv h]; exact hGet

/-- The frame cut leaves the cut frame's `next` as it was, or none. -/
theorem cutReplyFrameOutOrSelf_next {st : SystemState} {rid : SeLe4n.ReplyId} {r : Reply}
    (hObjInv : st.objects.invExt) (hR : st.getReply? rid = some r) :
    ∃ x, (cutReplyFrameOutOrSelf st rid).getReply? rid = some x ∧
      (x.next = r.next ∨ x.next = none) := by
  unfold cutReplyFrameOutOrSelf
  split
  · next st' hC =>
    revert hC
    unfold cutReplyFrameOut
    rw [hR]; simp only []
    cases hN : r.next with
    | none =>
      simp only []
      cases hP : r.prev with
      | none => intro hC; cases hC; exact ⟨r, hR, .inl hN⟩
      | some below =>
        simp only []
        cases hB : st.getReply? below with
        | none => intro hC; cases hC; exact ⟨r, hR, .inl hN⟩
        | some b =>
          simp only []
          split
          · intro hC; cases hC; exact ⟨r, hR, .inl hN⟩
          · next hBn =>
            intro hC
            have hBn' : b.next = some (.frame rid) := by simpa using hBn
            exact ⟨_, (severReplyFrameBelowStores_values hObjInv hR hN hB hBn' hC).2.1,
              .inr (by simp [hN])⟩
    | some link =>
      cases link with
      | head s => intro hC; cases hC; exact ⟨r, hR, .inl hN⟩
      | frame above =>
        simp only []
        cases hA : st.getReply? above with
        | none => intro hC; cases hC
        | some a =>
          simp only []
          split
          · intro hC; cases hC
          · next hAp =>
            intro hC
            have hAp' : a.prev = some rid := by simpa using hAp
            exact ⟨_, cutReplyFrameStores_getReply?_cut hObjInv hR hN hA hAp' hC, .inr rfl⟩
  · exact ⟨r, hR, .inl rfl⟩

/-- **The removal makes no frame a head**: a frame heading a context after it
headed that context before it. -/
theorem removeCallerReplyFrame_head_backward {st st' : SystemState} {caller : SeLe4n.ThreadId}
    {rid : SeLe4n.ReplyId} (hObjInv : st.objects.invExt)
    (h : removeCallerReplyFrame caller rid st = .ok ((), st')) {r1 : Reply}
    {s : SeLe4n.SchedContextId} (h1 : st'.getReply? rid = some r1)
    (hN1 : r1.next = some (.head s)) :
    ∃ r, st.getReply? rid = some r ∧ r.next = some (.head s) := by
  rw [removeCallerReplyFrame_eq] at h
  have hInvX := cutReplyFrameOutOrSelf_preserves_objects_invExt st rid hObjInv
  cases hR : st.getReply? rid with
  | none =>
    have hX : (cutReplyFrameOutOrSelf st rid).getReply? rid = none := by
      unfold cutReplyFrameOutOrSelf cutReplyFrameOut; rw [hR]; exact hR
    rw [consumeCallerReply_getReply?_none hInvX hX h] at h1; cases h1
  | some r =>
    obtain ⟨x, hX, hXn⟩ := cutReplyFrameOutOrSelf_next hObjInv hR
    have := SystemState.consumeCallerReply_getReply?_caller_none _ caller rid x hInvX hX st' h
    rw [this] at h1; cases h1
    refine ⟨r, rfl, ?_⟩
    unfold Reply.consumed at hN1
    cases hx : x.next with
    | none => rw [hx] at hN1; cases hN1
    | some l =>
      cases l with
      | frame _ => rw [hx] at hN1; cases hN1
      | head s' =>
        rw [hx] at hN1; simp only [] at hN1; cases hN1
        rcases hXn with e | e
        · rw [← e, hx]
        · rw [hx] at e; cases e

/-- A store of a TCB over a TCB keeps every context and every reply. -/
theorem storeObject_tcbOverTcb_getters {st st' : SystemState} {k : SeLe4n.ObjId} {t0 t1 : TCB}
    (hInv : st.objects.invExt) (hK : st.objects[k]? = some (.tcb t0))
    (h : storeObject k (.tcb t1) st = .ok ((), st')) :
    (∀ s, st'.getSchedContext? s = st.getSchedContext? s) ∧
      (∀ r, st'.getReply? r = st.getReply? r) := by
  have hEq := storeObject_objects_eq st st' _ _ hInv h
  refine ⟨fun s => ?_, fun r => ?_⟩
  · unfold SystemState.getSchedContext?
    by_cases e : s.toObjId = k
    · rw [e, hEq, hK]
    · rw [storeObject_objects_ne st st' _ _ _ e hInv h]
  · unfold SystemState.getReply?
    by_cases e : r.toObjId = k
    · rw [e, hEq, hK]
    · rw [storeObject_objects_ne st st' _ _ _ e hInv h]

/-- Two stores agreeing off the reply-waiter links read every context and every
reply alike. -/
theorem objectsAgreeOffReplyLinks_getters {st st' : SystemState}
    (h : SystemState.objectsAgreeOffReplyLinks st' st) :
    (∀ s, st'.getSchedContext? s = st.getSchedContext? s) ∧
      (∀ r, st'.getReply? r = st.getReply? r) := by
  refine ⟨fun s => Option.ext fun sc => ?_, fun r => Option.ext fun rr => ?_⟩
  · rw [SystemState.getSchedContext?_eq_some_iff, SystemState.getSchedContext?_eq_some_iff]
    exact ⟨h.get_of_not_tcb' (by intro t e; cases e), h.get_of_not_tcb (by intro t e; cases e)⟩
  · rw [SystemState.getReply?_eq_some_iff, SystemState.getReply?_eq_some_iff]
    exact ⟨h.get_of_not_tcb' (by intro t e; cases e), h.get_of_not_tcb (by intro t e; cases e)⟩

/-- The consume keeps every other reply. -/
theorem consumeCallerReply_getReply?_ne {st st' : SystemState} {caller : SeLe4n.ThreadId}
    {rid r : SeLe4n.ReplyId} (hObjInv : st.objects.invExt) (hne : r ≠ rid)
    (h : SystemState.consumeCallerReply caller rid st = .ok ((), st')) :
    st'.getReply? r = st.getReply? r := by
  have hK : r.toObjId ≠ rid.toObjId := fun e => hne (SeLe4n.ReplyId.toObjId_injective _ _ e)
  unfold SystemState.consumeCallerReply at h
  cases hC : SystemState.consumeReply rid st with
  | error e => rw [hC] at h; cases h
  | ok p =>
    obtain ⟨_, s1⟩ := p
    rw [hC] at h
    simp only [] at h
    have h1 : s1.getReply? r = st.getReply? r := by
      unfold SystemState.consumeReply at hC
      cases hG : st.getReply? rid with
      | none => rw [hG] at hC; cases hC; rfl
      | some x =>
        rw [hG] at hC
        unfold SystemState.getReply?
        rw [storeObject_objects_ne st s1 _ _ _ hK hObjInv hC]
    have hInv1 : s1.objects.invExt := by
      unfold SystemState.consumeReply at hC
      cases hG : st.getReply? rid with
      | none => rw [hG] at hC; cases hC; exact hObjInv
      | some x => rw [hG] at hC; exact storeObject_preserves_objects_invExt st s1 _ _ hObjInv hC
    cases hT : s1.getTcb? caller with
    | none => rw [hT] at h; cases h; exact h1
    | some t =>
      rw [hT] at h
      simp only [] at h
      rw [← h1]
      exact (storeObject_tcbOverTcb_getters hInv1
        ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) h).2 r

/-- **The reply leg, as the donation pop reads it** (a caller whose reply link
is the frame `rid` or nothing): it writes no context, it makes no frame a head,
and where `rid` heads a context it keeps every other reply and `rid`'s links. -/
theorem endpointReplyOnCore_popFrame {replier c : SeLe4n.ThreadId} {msg : IpcMessage}
    {core : Concurrency.CoreId} {st : SystemState} {rid : SeLe4n.ReplyId}
    (hInv : st.objects.invExt)
    (hFrame : ∀ t, lookupTcb st c = some t → t.replyObject = none ∨ t.replyObject = some rid) :
    (∀ s, (endpointReplyOnCore replier c msg core st).1.getSchedContext? s =
      st.getSchedContext? s) ∧
    (∀ r1 s, (endpointReplyOnCore replier c msg core st).1.getReply? rid = some r1 →
      r1.next = some (.head s) → ∃ r, st.getReply? rid = some r ∧ r.next = some (.head s)) ∧
    (∀ s, replyFrameHeadContext? st rid = some s →
      (∀ r, r ≠ rid → (endpointReplyOnCore replier c msg core st).1.getReply? r =
        st.getReply? r) ∧
      ((endpointReplyOnCore replier c msg core st).1.getReply? rid).map
          (fun y => (y.next, y.prev)) = (st.getReply? rid).map (fun y => (y.next, y.prev))) := by
  rcases endpointReplyOnCore_state_eq replier c msg core st with hEq |
    ⟨tcb, st', server, pre, hLk, hStore, hPost, hTail⟩
  · rw [hEq]
    exact ⟨fun _ => rfl, fun r1 s h1 hN => ⟨r1, h1, hN⟩, fun _ _ => ⟨fun _ _ => rfl, rfl⟩⟩
  rw [hPost]
  -- the caller's own write
  have hS1 : storeObject c.toObjId
      (.tcb (TCB.setIpcState { tcb with pendingMessage := some msg } .ready)) st = .ok ((), st') := by
    unfold storeTcbIpcStateAndMessage_fromTcb at hStore
    split at hStore
    · cases hStore
    · next hS => cases hStore; exact hS
  have hT0 : st.objects[c.toObjId]? = some (.tcb tcb) := by
    unfold lookupTcb at hLk; split at hLk; · cases hLk
    exact (SystemState.getTcb?_eq_some_iff _ _ _).mp hLk
  obtain ⟨g1s, g1r⟩ := storeObject_tcbOverTcb_getters hInv hT0 hS1
  have hInv1 := storeObject_preserves_objects_invExt st st' _ _ hInv hS1
  -- the wake
  have hTc1 : st'.getTcb? c = some (TCB.setIpcState { tcb with pendingMessage := some msg } .ready) :=
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr (storeObject_objects_eq st st' _ _ hInv hS1)
  have hW := wakeThread_objectsAgreeOffRunLinks_of_ready st' c core _ hTc1
    (TCB.ipcState_setIpcState _ _) hInv1
  have g2s := hW.getSchedContext?
  have g2r := hW.getReply?
  have hInvW := wakeThread_preserves_objects_invExt st' c core hInv1
  -- the reply-waiter unlink
  obtain ⟨g4s, g4r⟩ := objectsAgreeOffReplyLinks_getters
    (SystemState.unlinkReplyWaiterOpt_objectsAgreeOffReplyLinks pre c server)
  rcases hTail with ⟨_, hPre⟩ | ⟨rid', hRO, hRm⟩
  · subst hPre
    have gs : ∀ s, ((wakeThread st' c core).1.unlinkReplyWaiterOpt c server).getSchedContext? s =
        st.getSchedContext? s := fun s => by rw [g4s, g2s, g1s]
    have gr : ∀ r, ((wakeThread st' c core).1.unlinkReplyWaiterOpt c server).getReply? r =
        st.getReply? r := fun r => by rw [g4r, g2r, g1r]
    exact ⟨gs, fun r1 s h1 hN => ⟨r1, by rw [← gr]; exact h1, hN⟩,
      fun _ _ => ⟨fun r _ => gr r, by rw [gr]⟩⟩
  have hR' : rid' = rid := by
    rcases hFrame tcb hLk with e | e <;> rw [hRO] at e
    · cases e
    · cases e; rfl
  subst hR'
  have g3s := removeCallerReplyFrame_getSchedContext?_eq _ _ c rid' hInvW hRm
  refine ⟨fun s => by rw [g4s, g3s, g2s, g1s], fun r1 s h1 hN => ?_, fun s hH => ?_⟩
  · rw [g4r] at h1
    obtain ⟨r, hr, hrN⟩ := removeCallerReplyFrame_head_backward hInvW hRm h1 hN
    exact ⟨r, by rw [← g1r, ← g2r]; exact hr, hrN⟩
  · have hHW : replyFrameHeadContext? (wakeThread st' c core).1 rid' = some s := by
      exact (replyFrameHeadContext?_congr (s1 := st) (s2 := (wakeThread st' c core).1) rid'
        (by rw [g2r, g1r]) (fun q => by rw [g2s, g1s])).trans hH
    have hCut := cutReplyFrameOutOrSelf_eq_self_of_no_frame_above _ rid'
      (replyFrameAbove?_of_headContext _ rid' s hHW) (replyFrameBelow?_of_headContext _ rid' s hHW)
    have hRm' := hRm
    rw [removeCallerReplyFrame_eq, hCut] at hRm'
    refine ⟨fun r hne => by rw [g4r, consumeCallerReply_getReply?_ne hInvW hne hRm', g2r, g1r], ?_⟩
    obtain ⟨rr, _, hRr, hNr, _, _⟩ := replyFrameHeadContext?_eq_some hHW
    rw [g4r, SystemState.consumeCallerReply_getReply?_caller_none _ c rid' rr hInvW hRr pre hRm',
      ← g1r, ← g2r, hRr]
    simp only [Option.map_some, Reply.consumed, hNr]

/-- **The reply leg, as the donation pop reads it**, at a frame heading a
context: the pop reads the leg's state as it reads the state before it, the
answered caller made ready. -/
theorem endpointReplyOnCore_popReadsAgree {replier c : SeLe4n.ThreadId} {msg : IpcMessage}
    {core : Concurrency.CoreId} {st : SystemState} {rid : SeLe4n.ReplyId}
    {x : Option (Concurrency.CoreId × Concurrency.SgiKind)} {s : SeLe4n.SchedContextId}
    (hInv : st.objects.invExt)
    (hFrame : ∀ t, lookupTcb st c = some t → t.replyObject = none ∨ t.replyObject = some rid)
    (hOk : (endpointReplyOnCore replier c msg core st).2 = .ok x)
    (hH : replyFrameHeadContext? st rid = some s) :
    ReplyPopReadsAgree st (endpointReplyOnCore replier c msg core st).1 rid c := by
  obtain ⟨gs, _, gr⟩ := endpointReplyOnCore_popFrame (replier := replier) (msg := msg)
    (core := core) hInv hFrame
  obtain ⟨grr, gl⟩ := gr s hH
  have hF := endpointReplyOnCore_donationOwnerFrameExcept replier c msg core st hInv
  have hB := endpointReplyOnCore_sameSchedContextBindings replier c msg core st hInv
  have hTcb : ∀ t, (∃ y, (endpointReplyOnCore replier c msg core st).1.getTcb? t = some y) ↔
      ∃ y, st.getTcb? t = some y := fun t => by
    simp only [SystemState.getTcb?_eq_some_iff]
    constructor
    · rintro ⟨y, hy⟩; obtain ⟨z, hz, _⟩ := hB t y hy; exact ⟨z, hz⟩
    · rintro ⟨z, hz⟩; obtain ⟨y, hy, _⟩ := hF.tcbForward t z hz; exact ⟨y, hy⟩
  refine ⟨gs, grr, gl, fun t => ?_, fun t hne => ?_, fun y hy =>
    endpointReplyOnCore_ok_target_ready replier c msg core st hInv hOk hy⟩
  · cases h0 : st.getTcb? t with
    | none =>
      cases h1 : (endpointReplyOnCore replier c msg core st).1.getTcb? t with
      | none => rfl
      | some y => obtain ⟨z, hz⟩ := (hTcb t).mp ⟨y, h1⟩; rw [h0] at hz; cases hz
    | some z =>
      obtain ⟨y, hy, hyb, _⟩ := hF.tcbForward t z ((SystemState.getTcb?_eq_some_iff _ _ _).mp h0)
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hy]; simp [hyb]
  · cases h0 : st.getTcb? t with
    | none =>
      cases h1 : (endpointReplyOnCore replier c msg core st).1.getTcb? t with
      | none => rfl
      | some y => obtain ⟨z, hz⟩ := (hTcb t).mp ⟨y, h1⟩; rw [h0] at hz; cases hz
    | some z =>
      obtain ⟨y, hy, _, hyi⟩ := hF.tcbForward t z ((SystemState.getTcb?_eq_some_iff _ _ _).mp h0)
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hy]
      rcases hyi with e | e
      · exact absurd e hne
      · simp [e]

/-- **The pop's admission, read before the reply leg**: where the answered
caller's reply link is the frame `rid` or nothing, the donation pop commits on
the reply leg's state exactly where `replyRecvPopAdmitsCore` admits on the
state before it. -/
theorem endpointReplyOnCore_popCommits {replier c : SeLe4n.ThreadId} {msg : IpcMessage}
    {core : Concurrency.CoreId} {st : SystemState} {rid : SeLe4n.ReplyId}
    {x : Option (Concurrency.CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (hFrame : ∀ t, lookupTcb st c = some t → t.replyObject = none ∨ t.replyObject = some rid)
    (hOk : (endpointReplyOnCore replier c msg core st).2 = .ok x) :
    replyRecvPopCommits (endpointReplyOnCore replier c msg core st).1 rid c =
      replyRecvPopAdmitsCore st rid c := by
  cases hH : replyFrameHeadContext? st rid with
  | some s => exact (endpointReplyOnCore_popReadsAgree hInv hFrame hOk hH).commits
  | none =>
    obtain ⟨gs, gb, _⟩ := endpointReplyOnCore_popFrame (replier := replier) (msg := msg)
      (core := core) hInv hFrame
    have hH1 : replyFrameHeadContext? (endpointReplyOnCore replier c msg core st).1 rid = none := by
      cases e : replyFrameHeadContext? (endpointReplyOnCore replier c msg core st).1 rid with
      | none => rfl
      | some s =>
        obtain ⟨r1, sc, h1, hN1, hS1, hSR⟩ := replyFrameHeadContext?_eq_some e
        obtain ⟨r, hr, hrN⟩ := gb r1 s h1 hN1
        rw [gs] at hS1
        have : replyFrameHeadContext? st rid = some s := by
          unfold replyFrameHeadContext?; rw [hr]; simp [hrN, hS1, hSR]
        rw [hH] at this; cases this
    unfold replyRecvPopCommits replyRecvPopAdmitsCore
    rw [replyFrameHeadHolder?_of_no_head _ _ hH1, replyFrameHeadHolder?_of_no_head _ _ hH]
    simp only [hH1, hH]

/-- **An admitted pop commits after the reply leg** (checks first): where the
reply-receive's admission passes on its entry state, the donation pop the
composite runs on the reply leg's state cannot refuse. -/
theorem replyRecvPopDonation_ok_of_admits {replier c : SeLe4n.ThreadId} {msg : IpcMessage}
    {core : Concurrency.CoreId} {st : SystemState} {rid : SeLe4n.ReplyId}
    {x : Option (Concurrency.CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (hOk : (endpointReplyOnCore replier c msg core st).2 = .ok x)
    (hA : replyRecvPopAdmits st rid c = true) :
    ∃ r, replyRecvPopDonation rid c (endpointReplyOnCore replier c msg core st).1 = .ok r := by
  unfold replyRecvPopAdmits at hA
  simp only [Bool.and_eq_true] at hA
  have hFrame : ∀ t, lookupTcb st c = some t → t.replyObject = none ∨ t.replyObject = some rid :=
    fun t ht => by
      have h := hA.1
      unfold replyRecvCallerFrameIs at h
      rw [ht] at h
      simpa using h
  have hInv1 := endpointReplyOnCore_preserves_objects_invExt replier c msg core st hInv
  exact (replyRecvPopDonation_ok_iff_commits hInv1).mpr
    ((endpointReplyOnCore_popCommits hInv hFrame hOk).trans hA.2)

/-- **The admission refuses no pop that commits** where the caller's reply link
is the frame or nothing: it is exact there. -/
theorem replyRecvPopAdmits_of_pop_ok {replier c : SeLe4n.ThreadId} {msg : IpcMessage}
    {core : Concurrency.CoreId} {st : SystemState} {rid : SeLe4n.ReplyId}
    {x : Option (Concurrency.CoreId × Concurrency.SgiKind)}
    {r : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId) × SystemState}
    (hInv : st.objects.invExt) (hFr : replyRecvCallerFrameIs st c rid = true)
    (hOk : (endpointReplyOnCore replier c msg core st).2 = .ok x)
    (hPop : replyRecvPopDonation rid c (endpointReplyOnCore replier c msg core st).1 = .ok r) :
    replyRecvPopAdmits st rid c = true := by
  have hFrame : ∀ t, lookupTcb st c = some t → t.replyObject = none ∨ t.replyObject = some rid :=
    fun t ht => by
      have h := hFr
      unfold replyRecvCallerFrameIs at h
      rw [ht] at h
      simpa using h
  have hInv1 := endpointReplyOnCore_preserves_objects_invExt replier c msg core st hInv
  unfold replyRecvPopAdmits
  rw [hFr, Bool.true_and, ← endpointReplyOnCore_popCommits hInv hFrame hOk]
  exact (replyRecvPopDonation_ok_iff_commits hInv1).mp ⟨r, hPop⟩

end SeLe4n.Kernel
