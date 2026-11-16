-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions; see LICENSE for details.
-/
import SeLe4n.Kernel.IPC.CrossCore.ReplyHolderCancel
import SeLe4n.Kernel.Architecture.IpcBufferTlbFill

/-!
# The reply holder's cancel commutes with a per-core TLB write

`cancelReplyHolder` (seL4-MCS `cancelIPC` on a busy reply's holder) neither
reads nor writes the per-core TLB views: every read it makes is of the object
store and the scheduler, and every write it makes is a record update of other
fields.  So a write to `perCoreTlb` made before it can be made after it instead
(`cancelReplyHolder_withPerCoreTlb`), and a syscall entry that filled core `c`'s
view for an IPC-buffer read, ran the cancel, and then undid the fill reports the
cancel of the state it was handed (`tlbUndoFillOnCore_fill_of_withPerCoreTlb`).

The proof is structural, over the cancel's definition closure.  Every read is a
function of fields other than `perCoreTlb`, so it reads the same on
`s.withPerCoreTlb t` as on `s` by definition (`rfl`).  Every write is stated as
`w (s.withPerCoreTlb t) = (w s).withPerCoreTlb t` (or, for a write that can
refuse, its `Except.map`), and a composite write follows from its parts by
rewriting the reads and writes it is built from and splitting each branch it
takes on a read: both sides branch on the same read, so each branch closes by
`rfl`.
-/

namespace SeLe4n.Model

/-- The state with its per-core TLB views replaced by `t`, every other field
kept: the one write the access-time fill and its undo make. -/
def SystemState.withPerCoreTlb (s : SystemState)
    (t : Vector TlbState SeLe4n.Kernel.Concurrency.numCores) : SystemState :=
  { s with perCoreTlb := t }

end SeLe4n.Model

namespace SeLe4n.Kernel

open SeLe4n.Model

namespace PerCoreTlbFrame

variable (s : SystemState) (t : Vector TlbState Concurrency.numCores)

/-! ## Reads: each reads the same with the TLB views replaced -/

theorem objects : (s.withPerCoreTlb t).objects = s.objects := rfl
theorem scheduler : (s.withPerCoreTlb t).scheduler = s.scheduler := rfl
theorem perCoreTlb : (s.withPerCoreTlb t).perCoreTlb = t := rfl
theorem getTcb? (tid) : (s.withPerCoreTlb t).getTcb? tid = s.getTcb? tid := rfl
theorem getSchedContext? (i) : (s.withPerCoreTlb t).getSchedContext? i = s.getSchedContext? i := rfl
theorem getReply? (i) : (s.withPerCoreTlb t).getReply? i = s.getReply? i := rfl
theorem getEndpoint? (i) : (s.withPerCoreTlb t).getEndpoint? i = s.getEndpoint? i := rfl
theorem getNotification? (i) : (s.withPerCoreTlb t).getNotification? i = s.getNotification? i := rfl
theorem lookupTcb (tid) : SeLe4n.Kernel.lookupTcb (s.withPerCoreTlb t) tid = SeLe4n.Kernel.lookupTcb s tid := rfl

/-! ## Writes of the object store and the scheduler -/

theorem rewriteObject (id o h) :
    (s.withPerCoreTlb t).rewriteObject id o h = (s.rewriteObject id o h).withPerCoreTlb t := rfl

theorem mapTcbInPlace (tid g) :
    (s.withPerCoreTlb t).mapTcbInPlace tid g = (s.mapTcbInPlace tid g).withPerCoreTlb t := rfl

theorem markReschedulePendingOnCore (c) :
    (s.withPerCoreTlb t).markReschedulePendingOnCore c =
      (s.markReschedulePendingOnCore c).withPerCoreTlb t := rfl

theorem storeObject (id o) :
    storeObject id o (s.withPerCoreTlb t) =
      (storeObject id o s).map (fun p => (p.1, p.2.withPerCoreTlb t)) := rfl

theorem updateTcbAtCode (k g) :
    (s.withPerCoreTlb t).updateTcbAtCode k g = (s.updateTcbAtCode k g).withPerCoreTlb t := by
  unfold SystemState.updateTcbAtCode; split <;> rfl

theorem updateTcb (tid f) :
    (s.withPerCoreTlb t).updateTcb tid f = (s.updateTcb tid f).withPerCoreTlb t := by
  cases hT : s.getTcb? tid with
  | none =>
    rw [SystemState.updateTcb_eq_self_of_none hT,
      SystemState.updateTcb_eq_self_of_none (st := s.withPerCoreTlb t) hT]
  | some x =>
    rw [SystemState.updateTcb_eq_of_some hT,
      SystemState.updateTcb_eq_of_some (st := s.withPerCoreTlb t) hT]; rfl

theorem updateSchedContext (i f) :
    (s.withPerCoreTlb t).updateSchedContext i f = (s.updateSchedContext i f).withPerCoreTlb t := by
  cases hT : s.getSchedContext? i with
  | none =>
    rw [SystemState.updateSchedContext_eq_self_of_none hT,
      SystemState.updateSchedContext_eq_self_of_none (st := s.withPerCoreTlb t) hT]
  | some x =>
    rw [SystemState.updateSchedContext_eq_of_some hT,
      SystemState.updateSchedContext_eq_of_some (st := s.withPerCoreTlb t) hT]; rfl

theorem runLinkOn (c tid) : (s.withPerCoreTlb t).runLinkOn c tid = s.runLinkOn c tid := rfl
theorem queuedOn (c tid) : (s.withPerCoreTlb t).queuedOn c tid = s.queuedOn c tid := rfl
theorem replyPrevCode (w) : (s.withPerCoreTlb t).replyPrevCode w = s.replyPrevCode w := rfl
theorem replyNextCode (w) : (s.withPerCoreTlb t).replyNextCode w = s.replyNextCode w := rfl

/-! ## Run-queue and reply-waiter link writes -/

theorem runAppendLinks (c tid p) :
    (s.withPerCoreTlb t).runAppendLinks c tid p = (s.runAppendLinks c tid p).withPerCoreTlb t := by
  unfold SystemState.runAppendLinks
  simp only [scheduler, mapTcbInPlace, updateTcbAtCode]

theorem runAppendOnCore (c tid p) :
    (s.withPerCoreTlb t).runAppendOnCore c tid p = (s.runAppendOnCore c tid p).withPerCoreTlb t := by
  unfold SystemState.runAppendOnCore
  simp only [runAppendLinks]; rfl

theorem runEnqueueAdmitted (c tid p) :
    (s.withPerCoreTlb t).runEnqueueAdmitted c tid p =
      (s.runEnqueueAdmitted c tid p).withPerCoreTlb t := by
  unfold SystemState.runEnqueueAdmitted
  simp only [runLinkOn, runAppendOnCore]
  split <;> rfl

theorem runUnlinkLinks (tid pv nx bpv bnx) :
    (s.withPerCoreTlb t).runUnlinkLinks tid pv nx bpv bnx =
      (s.runUnlinkLinks tid pv nx bpv bnx).withPerCoreTlb t := by
  unfold SystemState.runUnlinkLinks
  simp only [mapTcbInPlace, updateTcbAtCode]

theorem runRemoveOnCore (c tid) :
    (s.withPerCoreTlb t).runRemoveOnCore c tid = (s.runRemoveOnCore c tid).withPerCoreTlb t := by
  unfold SystemState.runRemoveOnCore
  simp only [runLinkOn, runUnlinkLinks]
  split <;> rfl

theorem runRequeueOnCore (c tid p) :
    (s.withPerCoreTlb t).runRequeueOnCore c tid p =
      (s.runRequeueOnCore c tid p).withPerCoreTlb t := by
  unfold SystemState.runRequeueOnCore
  simp only [runRemoveOnCore, runEnqueueAdmitted]; rfl

theorem unlinkReplyWaiter (w x) :
    (s.withPerCoreTlb t).unlinkReplyWaiter w x = (s.unlinkReplyWaiter w x).withPerCoreTlb t := by
  unfold SystemState.unlinkReplyWaiter
  simp only [replyPrevCode, replyNextCode, mapTcbInPlace, updateTcbAtCode]

theorem unlinkReplyWaiterOpt (w o) :
    (s.withPerCoreTlb t).unlinkReplyWaiterOpt w o = (s.unlinkReplyWaiterOpt w o).withPerCoreTlb t := by
  cases o <;> simp only [SystemState.unlinkReplyWaiterOpt, unlinkReplyWaiter]

/-! ## The scheduling-key hook -/

theorem effectiveSchedParams (tcb) :
    SeLe4n.Kernel.effectiveSchedParams (s.withPerCoreTlb t) tcb =
      SeLe4n.Kernel.effectiveSchedParams s tcb := rfl
theorem hasSufficientBudget (tcb) :
    SeLe4n.Kernel.hasSufficientBudget (s.withPerCoreTlb t) tcb =
      SeLe4n.Kernel.hasSufficientBudget s tcb := rfl

theorem markReschedulePendingWhere (p) : ∀ (cs : List Concurrency.CoreId) (s : SystemState),
    SeLe4n.Kernel.markReschedulePendingWhere (s.withPerCoreTlb t) p cs =
      (SeLe4n.Kernel.markReschedulePendingWhere s p cs).withPerCoreTlb t
  | [], _ => rfl
  | c :: cs, s => by
    simp only [SeLe4n.Kernel.markReschedulePendingWhere]
    split
    · rw [markReschedulePendingOnCore, markReschedulePendingWhere p cs]
    · rw [markReschedulePendingWhere p cs]

theorem markKeyFlagsOver (tid rc w) : ∀ (cs : List Concurrency.CoreId) (s : SystemState),
    SeLe4n.Kernel.markKeyFlagsOver (s.withPerCoreTlb t) tid rc w cs =
      (SeLe4n.Kernel.markKeyFlagsOver s tid rc w cs).withPerCoreTlb t
  | [], _ => rfl
  | c :: cs, s => by
    simp only [SeLe4n.Kernel.markKeyFlagsOver, scheduler]
    split
    · rw [markReschedulePendingOnCore, markKeyFlagsOver tid rc w cs]
    · rw [markKeyFlagsOver tid rc w cs]

theorem markKeyChangeFor (tid k) :
    SeLe4n.Kernel.markKeyChangeFor (s.withPerCoreTlb t) tid k =
      (SeLe4n.Kernel.markKeyChangeFor s tid k).withPerCoreTlb t := by
  unfold SeLe4n.Kernel.markKeyChangeFor
  exact markReschedulePendingWhere t _ _ s

theorem markCandidacyGainFor (tid e) :
    SeLe4n.Kernel.markCandidacyGainFor (s.withPerCoreTlb t) tid e =
      (SeLe4n.Kernel.markCandidacyGainFor s tid e).withPerCoreTlb t := by
  unfold SeLe4n.Kernel.markCandidacyGainFor
  simp only [getTcb?, hasSufficientBudget]
  split
  · rfl
  · split
    · split
      · exact markKeyFlagsOver t _ _ _ _ s
      · rfl
    · rfl

theorem markKeyChangeFrom (pre post tid) :
    SeLe4n.Kernel.markKeyChangeFrom (pre.withPerCoreTlb t) (post.withPerCoreTlb t) tid =
      (SeLe4n.Kernel.markKeyChangeFrom pre post tid).withPerCoreTlb t := by
  unfold SeLe4n.Kernel.markKeyChangeFrom
  simp only [getTcb?, hasSufficientBudget, effectiveSchedParams]
  split
  · rw [markCandidacyGainFor, markKeyChangeFor]
  · exact markReschedulePendingWhere t _ _ post

/-! ## The priority-inheritance walk -/

theorem replyWaitersWalk : ∀ (n : Nat) (o : Option SeLe4n.ThreadId),
    (s.withPerCoreTlb t).replyWaitersWalk n o = s.replyWaitersWalk n o
  | 0, _ => rfl
  | _ + 1, none => rfl
  | n + 1, some w => by
    simp only [SystemState.replyWaitersWalk, getTcb?, replyWaitersWalk n]

theorem waitersOf (tid) :
    PriorityInheritance.waitersOf (s.withPerCoreTlb t) tid = PriorityInheritance.waitersOf s tid := by
  unfold PriorityInheritance.waitersOf SystemState.replyWaitersOf
  simp only [getTcb?, replyWaitersWalk]

theorem computeMaxWaiterPriority (tid) :
    PriorityInheritance.computeMaxWaiterPriority (s.withPerCoreTlb t) tid =
      PriorityInheritance.computeMaxWaiterPriority s tid := by
  unfold PriorityInheritance.computeMaxWaiterPriority
  rw [waitersOf]; rfl
theorem resolveEffectivePrioDeadline (tcb) :
    SeLe4n.Kernel.resolveEffectivePrioDeadline (s.withPerCoreTlb t) tcb =
      SeLe4n.Kernel.resolveEffectivePrioDeadline s tcb := rfl
theorem determineTargetCore (tid) :
    SeLe4n.Kernel.determineTargetCore (s.withPerCoreTlb t) tid =
      SeLe4n.Kernel.determineTargetCore s tid := rfl
theorem blockingServer (tid) :
    PriorityInheritance.blockingServer (s.withPerCoreTlb t) tid =
      PriorityInheritance.blockingServer s tid := rfl

theorem updatePipBoostOnCore (c tid) :
    PriorityInheritance.updatePipBoostOnCore (s.withPerCoreTlb t) c tid =
      (PriorityInheritance.updatePipBoostOnCore s c tid).withPerCoreTlb t := by
  cases hT : s.getTcb? tid with
  | none =>
    unfold PriorityInheritance.updatePipBoostOnCore
    rw [SystemState.getTcbWitnessed?_eq_none hT,
      SystemState.getTcbWitnessed?_eq_none (st := s.withPerCoreTlb t) hT]
  | some x =>
    unfold PriorityInheritance.updatePipBoostOnCore
    rw [SystemState.getTcbWitnessed?_eq_some hT,
      SystemState.getTcbWitnessed?_eq_some (st := s.withPerCoreTlb t) hT]
    simp only [computeMaxWaiterPriority, effectiveSchedParams, queuedOn,
      resolveEffectivePrioDeadline, rewriteObject]
    split
    · rfl
    · split
      · split
        · rw [runRequeueOnCore, markKeyChangeFor]
        · rw [markKeyChangeFor]
      · rw [markKeyChangeFor]

theorem pipBoostWithWake (tid e) :
    PriorityInheritance.pipBoostWithWake (s.withPerCoreTlb t) tid e =
      ((PriorityInheritance.pipBoostWithWake s tid e).1.withPerCoreTlb t,
        (PriorityInheritance.pipBoostWithWake s tid e).2) := by
  unfold PriorityInheritance.pipBoostWithWake
  simp only [determineTargetCore, updatePipBoostOnCore, queuedOn, getTcb?,
    resolveEffectivePrioDeadline]

theorem propagatePipChainCrossCore (e) : ∀ (fuel : Nat) (s : SystemState) (tid),
    PriorityInheritance.propagatePipChainCrossCore (s.withPerCoreTlb t) tid e fuel =
      ((PriorityInheritance.propagatePipChainCrossCore s tid e fuel).1.withPerCoreTlb t,
        (PriorityInheritance.propagatePipChainCrossCore s tid e fuel).2)
  | 0, _, _ => rfl
  | fuel + 1, s, tid => by
    unfold PriorityInheritance.propagatePipChainCrossCore
    simp only [pipBoostWithWake, blockingServer]
    split
    · rw [pipBoostWithWake, propagatePipChainCrossCore e fuel]
    · rfl

/-! ## Endpoint and notification queue removal -/

theorem removeThreadFromQueue (q tid) :
    SeLe4n.Kernel.removeThreadFromQueue (s.withPerCoreTlb t) q tid =
      SeLe4n.Kernel.removeThreadFromQueue s q tid := rfl

theorem spliceOutMidQueueNode (tid) :
    SeLe4n.Kernel.spliceOutMidQueueNode (s.withPerCoreTlb t) tid =
      (SeLe4n.Kernel.spliceOutMidQueueNode s tid).withPerCoreTlb t := by
  unfold SeLe4n.Kernel.spliceOutMidQueueNode
  simp only [lookupTcb, objects]
  split <;> rfl

theorem removeFromBlockingEndpoint (tid id) :
    SeLe4n.Kernel.removeFromBlockingEndpoint (s.withPerCoreTlb t) tid id =
      (SeLe4n.Kernel.removeFromBlockingEndpoint s tid id).withPerCoreTlb t := by
  unfold SeLe4n.Kernel.removeFromBlockingEndpoint
  rw [spliceOutMidQueueNode]
  dsimp only
  rcases Option.eq_none_or_eq_some ((SeLe4n.Kernel.spliceOutMidQueueNode s tid).getEndpoint? id)
    with hE | ⟨ep, hE⟩
  · rw [SystemState.getEndpointWitnessed?_eq_none hE,
      SystemState.getEndpointWitnessed?_eq_none (st := (SeLe4n.Kernel.spliceOutMidQueueNode s tid).withPerCoreTlb t) hE]
  · rw [SystemState.getEndpointWitnessed?_eq_some hE,
      SystemState.getEndpointWitnessed?_eq_some (st := (SeLe4n.Kernel.spliceOutMidQueueNode s tid).withPerCoreTlb t) hE]
    simp only [removeThreadFromQueue]
    split <;> rfl

theorem clearNtfnLinks (tid) :
    SeLe4n.Kernel.clearNtfnLinks (s.withPerCoreTlb t) tid =
      (SeLe4n.Kernel.clearNtfnLinks s tid).withPerCoreTlb t := by
  unfold SeLe4n.Kernel.clearNtfnLinks; exact updateTcb s t _ _

theorem unlinkNtfnNeighbours (p n) :
    SeLe4n.Kernel.unlinkNtfnNeighbours (s.withPerCoreTlb t) p n =
      (SeLe4n.Kernel.unlinkNtfnNeighbours s p n).withPerCoreTlb t := by
  unfold SeLe4n.Kernel.unlinkNtfnNeighbours
  cases p <;> cases n <;> simp only [updateTcb]

theorem removeFromNotificationWaitQueue (tid) :
    SeLe4n.Kernel.removeFromNotificationWaitQueue (s.withPerCoreTlb t) tid =
      (SeLe4n.Kernel.removeFromNotificationWaitQueue s tid).withPerCoreTlb t := by
  unfold SeLe4n.Kernel.removeFromNotificationWaitQueue
  simp only [getTcb?]
  split
  · split
    · rename_i oid _
      rcases Option.eq_none_or_eq_some (s.getNotification? oid) with hN | ⟨n, hN⟩
      · rw [SystemState.getNotificationWitnessed?_eq_none hN,
          SystemState.getNotificationWitnessed?_eq_none (st := s.withPerCoreTlb t) hN]
      · rw [SystemState.getNotificationWitnessed?_eq_some hN,
          SystemState.getNotificationWitnessed?_eq_some (st := s.withPerCoreTlb t) hN]
        simp only [rewriteObject, clearNtfnLinks, unlinkNtfnNeighbours]
    · rfl
  · rfl

/-! ## Stores that cannot refuse, and the reply consume -/

/-- A store succeeds, and on the state with its TLB views replaced it stores
into the same record with those views replaced. -/
theorem storeObject_ok (id o) : ∃ s', SeLe4n.Model.storeObject id o s = .ok ((), s') ∧
    SeLe4n.Model.storeObject id o (s.withPerCoreTlb t) = .ok ((), s'.withPerCoreTlb t) :=
  ⟨_, rfl, rfl⟩

theorem restoreToReadyStaging (tid r) :
    Lifecycle.Suspend.restoreToReadyStaging (s.withPerCoreTlb t) tid r =
      (Lifecycle.Suspend.restoreToReadyStaging s tid r).withPerCoreTlb t := by
  unfold Lifecycle.Suspend.restoreToReadyStaging; exact updateTcb s t _ _

theorem restoreToReadyCancelled (tid) :
    Lifecycle.Suspend.restoreToReadyCancelled (s.withPerCoreTlb t) tid =
      (Lifecycle.Suspend.restoreToReadyCancelled s tid).withPerCoreTlb t :=
  restoreToReadyStaging s t tid true

theorem consumeReply (rid) :
    SystemState.consumeReply rid (s.withPerCoreTlb t) =
      (SystemState.consumeReply rid s).map (fun p => (p.1, p.2.withPerCoreTlb t)) := by
  unfold SystemState.consumeReply
  simp only [getReply?]
  split
  · rfl
  · rfl

theorem consumeCallerReply (c rid) :
    SystemState.consumeCallerReply c rid (s.withPerCoreTlb t) =
      (SystemState.consumeCallerReply c rid s).map (fun p => (p.1, p.2.withPerCoreTlb t)) := by
  unfold SystemState.consumeCallerReply
  rw [consumeReply]
  cases SystemState.consumeReply rid s with
  | error e => rfl
  | ok p =>
    obtain ⟨⟨⟩, s1⟩ := p
    show (match (s1.withPerCoreTlb t).getTcb? c with
      | none => (Except.ok ((), s1.withPerCoreTlb t) : Except KernelError (Unit × SystemState))
      | some tcb => SeLe4n.Model.storeObject c.toObjId (.tcb { tcb with replyObjectCode := 0 })
          (s1.withPerCoreTlb t)) = _
    simp only [getTcb?]
    cases s1.getTcb? c <;> rfl

theorem consumeCallerReplyLink (c rid) :
    (s.withPerCoreTlb t).consumeCallerReplyLink c rid =
      (s.consumeCallerReplyLink c rid).withPerCoreTlb t := by
  obtain ⟨s1, h1⟩ := SystemState.consumeCallerReply_isOk s c rid
  have h1' : SystemState.consumeCallerReply c rid (s.withPerCoreTlb t) =
      .ok ((), s1.withPerCoreTlb t) := by rw [consumeCallerReply, h1]; rfl
  unfold SystemState.consumeCallerReplyLink
  split
  · rename_i s2 h2
    split
    · rename_i s3 h3
      rw [h1'] at h2; rw [h1] at h3
      cases h2; cases h3; rfl
    · rename_i h3; rw [h1] at h3; cases h3
  · rename_i h2; rw [h1'] at h2; cases h2

theorem consumeReplyLink (tid tcb) :
    Lifecycle.Suspend.consumeReplyLink (s.withPerCoreTlb t) tid tcb =
      (Lifecycle.Suspend.consumeReplyLink s tid tcb).withPerCoreTlb t := by
  unfold Lifecycle.Suspend.consumeReplyLink
  split
  · rfl
  · exact consumeCallerReplyLink s t _ _

/-! ## The reply-frame cuts -/

theorem cutFrameBelow? (rid r a) :
    SeLe4n.Kernel.cutFrameBelow? (s.withPerCoreTlb t) rid r a =
      SeLe4n.Kernel.cutFrameBelow? s rid r a := rfl

theorem severReplyFrameBelowStores (rid below r b) :
    SeLe4n.Kernel.severReplyFrameBelowStores (s.withPerCoreTlb t) rid below r b =
      (SeLe4n.Kernel.severReplyFrameBelowStores s rid below r b).map (·.withPerCoreTlb t) := by
  unfold SeLe4n.Kernel.severReplyFrameBelowStores
  obtain ⟨s1, h1, h1'⟩ := storeObject_ok s t below.toObjId (.reply { b with next := none })
  rw [h1, h1']; dsimp only
  obtain ⟨s2, h2, h2'⟩ := storeObject_ok s1 t rid.toObjId (.reply { r with prev := none })
  rw [h2, h2']; rfl

theorem cutReplyFrameStores (rid above r a) :
    SeLe4n.Kernel.cutReplyFrameStores (s.withPerCoreTlb t) rid above r a =
      (SeLe4n.Kernel.cutReplyFrameStores s rid above r a).map (·.withPerCoreTlb t) := by
  unfold SeLe4n.Kernel.cutReplyFrameStores
  rw [cutFrameBelow?]
  obtain ⟨s1, h1, h1'⟩ := storeObject_ok s t above.toObjId (.reply (a.unlinkedFrom rid))
  rw [h1, h1']
  split
  · dsimp only
    obtain ⟨s2, h2, h2'⟩ := storeObject_ok s1 t rid.toObjId (.reply { r with prev := none, next := none })
    rw [h2, h2']; rfl
  · rename_i below b _
    dsimp only
    obtain ⟨s2, h2, h2'⟩ := storeObject_ok s1 t below.toObjId (.reply { b with next := none })
    rw [h2, h2']; dsimp only
    obtain ⟨s3, h3, h3'⟩ := storeObject_ok s2 t rid.toObjId (.reply { r with prev := none, next := none })
    rw [h3, h3']; rfl

theorem cutReplyFrameOut (rid) :
    SeLe4n.Kernel.cutReplyFrameOut (s.withPerCoreTlb t) rid =
      (SeLe4n.Kernel.cutReplyFrameOut s rid).map (·.withPerCoreTlb t) := by
  unfold SeLe4n.Kernel.cutReplyFrameOut
  simp only [getReply?, cutReplyFrameStores, severReplyFrameBelowStores]
  repeat' split
  all_goals rfl

theorem cutReplyFrameOutOrSelf (rid) :
    SeLe4n.Kernel.cutReplyFrameOutOrSelf (s.withPerCoreTlb t) rid =
      (SeLe4n.Kernel.cutReplyFrameOutOrSelf s rid).withPerCoreTlb t := by
  unfold SeLe4n.Kernel.cutReplyFrameOutOrSelf
  rw [cutReplyFrameOut]
  cases SeLe4n.Kernel.cutReplyFrameOut s rid <;> rfl

theorem cutThreadReplyFrameOut (tcb) :
    SeLe4n.Kernel.cutThreadReplyFrameOut (s.withPerCoreTlb t) tcb =
      (SeLe4n.Kernel.cutThreadReplyFrameOut s tcb).withPerCoreTlb t := by
  unfold SeLe4n.Kernel.cutThreadReplyFrameOut
  split
  · rfl
  · exact cutReplyFrameOutOrSelf s t _

/-! ## The donation return -/

theorem donationHeadOf? (i sc) :
    SeLe4n.Kernel.donationHeadOf? (s.withPerCoreTlb t) i sc = SeLe4n.Kernel.donationHeadOf? s i sc :=
  rfl
theorem replyStackOuterCaller? (i) :
    SeLe4n.Kernel.replyStackOuterCaller? (s.withPerCoreTlb t) i =
      SeLe4n.Kernel.replyStackOuterCaller? s i := rfl
theorem outerCallerAcceptable (a b o) :
    SeLe4n.Kernel.outerCallerAcceptable (s.withPerCoreTlb t) a b o =
      SeLe4n.Kernel.outerCallerAcceptable s a b o := rfl
theorem donationRecipientAcceptable (a) :
    SeLe4n.Kernel.donationRecipientAcceptable (s.withPerCoreTlb t) a =
      SeLe4n.Kernel.donationRecipientAcceptable s a := rfl
theorem replyFrameHeadContext? (rid) :
    SeLe4n.Kernel.replyFrameHeadContext? (s.withPerCoreTlb t) rid =
      SeLe4n.Kernel.replyFrameHeadContext? s rid := rfl
theorem replyFrameHeadHolder? (rid) :
    SeLe4n.Kernel.replyFrameHeadHolder? (s.withPerCoreTlb t) rid =
      SeLe4n.Kernel.replyFrameHeadHolder? s rid := rfl
theorem cancelledCallerDonation? (tid tcb) :
    Lifecycle.Suspend.cancelledCallerDonation? (s.withPerCoreTlb t) tid tcb =
      Lifecycle.Suspend.cancelledCallerDonation? s tid tcb := rfl

theorem storeDonationHeadClear (o) :
    SeLe4n.Kernel.storeDonationHeadClear o (s.withPerCoreTlb t) =
      (SeLe4n.Kernel.storeDonationHeadClear o s).map (·.withPerCoreTlb t) := by
  cases o with
  | none => rfl
  | some rid =>
    unfold SeLe4n.Kernel.storeDonationHeadClear
    simp only [getReply?]
    cases s.getReply? rid with
    | none => rfl
    | some r =>
      dsimp only
      obtain ⟨s1, h1, h1'⟩ := storeObject_ok s t rid.toObjId (.reply { r with prev := none, next := none })
      rw [h1, h1']; rfl

theorem storeReplyReHead (i o) :
    SeLe4n.Kernel.storeReplyReHead i o (s.withPerCoreTlb t) =
      (SeLe4n.Kernel.storeReplyReHead i o s).map (·.withPerCoreTlb t) := by
  cases o with
  | none => rfl
  | some rid =>
    unfold SeLe4n.Kernel.storeReplyReHead
    simp only [getReply?]
    cases s.getReply? rid with
    | none => rfl
    | some r =>
      dsimp only
      obtain ⟨s1, h1, h1'⟩ := storeObject_ok s t rid.toObjId (.reply { r with next := some (.head i) })
      rw [h1, h1']; rfl

theorem storeDonationHeadPop (i o) :
    SeLe4n.Kernel.storeDonationHeadPop i o (s.withPerCoreTlb t) =
      (SeLe4n.Kernel.storeDonationHeadPop i o s).map (·.withPerCoreTlb t) := by
  cases o with
  | none => rfl
  | some p =>
    obtain ⟨rid, r⟩ := p
    unfold SeLe4n.Kernel.storeDonationHeadPop
    dsimp only
    rw [storeDonationHeadClear]
    cases SeLe4n.Kernel.storeDonationHeadClear (some rid) s with
    | error e => rfl
    | ok s1 => exact storeReplyReHead s1 t i r.prev

theorem returnDonatedSchedContext (srv i o n) :
    SeLe4n.Kernel.returnDonatedSchedContext (s.withPerCoreTlb t) srv i o n =
      (SeLe4n.Kernel.returnDonatedSchedContext s srv i o n).map (·.withPerCoreTlb t) := by
  unfold SeLe4n.Kernel.returnDonatedSchedContext
  simp only [getSchedContext?, outerCallerAcceptable, donationRecipientAcceptable, donationHeadOf?]
  split
  · rename_i sc _
    split
    · rfl
    split
    · rfl
    split
    · rfl
    split
    · rfl
    rename_i head? _
    obtain ⟨s1, h1, h1'⟩ := storeObject_ok s t i.toObjId (.schedContext
      (donationReturnSchedContext sc o (head?.bind (fun p => p.2.prev)) n))
    rw [h1, h1']; dsimp only
    rw [storeDonationHeadPop]
    cases SeLe4n.Kernel.storeDonationHeadPop i head? s1 with
    | error e => rfl
    | ok s2 =>
      simp only [Except.map]
      rw [lookupTcb]
      cases SeLe4n.Kernel.lookupTcb s2 o with
      | none => rfl
      | some ct =>
        dsimp only
        obtain ⟨s3, h3, h3'⟩ := storeObject_ok s2 t o.toObjId (.tcb { ct with
          scBindingScCode := SchedContextBinding.scCode (donationReturnBinding i n),
          scBindingOwnerCode := SchedContextBinding.ownerCode (donationReturnBinding i n) })
        rw [h3, h3']; dsimp only
        rw [lookupTcb]
        cases SeLe4n.Kernel.lookupTcb s3 srv with
        | none => rfl
        | some st =>
          dsimp only
          obtain ⟨s4, h4, h4'⟩ := storeObject_ok s3 t srv.toObjId (.tcb { st with
            scBindingScCode := 0, scBindingOwnerCode := 0 })
          rw [h4, h4']; dsimp only
          rw [markKeyChangeFrom, markKeyChangeFrom]
  · rfl

theorem returnDonatedSchedContextResolved (srv i o) :
    SeLe4n.Kernel.returnDonatedSchedContextResolved (s.withPerCoreTlb t) srv i o =
      (SeLe4n.Kernel.returnDonatedSchedContextResolved s srv i o).map (·.withPerCoreTlb t) := by
  unfold SeLe4n.Kernel.returnDonatedSchedContextResolved
  rw [replyStackOuterCaller?]
  split
  · rfl
  · exact returnDonatedSchedContext s t _ _ _ _

theorem returnDonationToCancelledCaller (tid tcb) :
    Lifecycle.Suspend.returnDonationToCancelledCaller (s.withPerCoreTlb t) tid tcb =
      (Lifecycle.Suspend.returnDonationToCancelledCaller s tid tcb).withPerCoreTlb t := by
  unfold Lifecycle.Suspend.returnDonationToCancelledCaller
  simp only [cancelledCallerDonation?, getTcb?]
  split
  · rename_i scId holder _ _ _
    rw [returnDonatedSchedContextResolved]
    cases SeLe4n.Kernel.returnDonatedSchedContextResolved s holder scId tid <;> rfl
  · rfl

/-! ## The IPC cancel and the holder's cancel -/

theorem cancelIpcBlocking (tid tcb) :
    Lifecycle.Suspend.cancelIpcBlocking (s.withPerCoreTlb t) tid tcb =
      (Lifecycle.Suspend.cancelIpcBlocking s tid tcb).withPerCoreTlb t := by
  unfold Lifecycle.Suspend.cancelIpcBlocking
  split
  · rfl
  · rw [removeFromBlockingEndpoint, restoreToReadyCancelled]
  · rw [removeFromBlockingEndpoint, restoreToReadyCancelled]
  · rw [removeFromBlockingEndpoint, restoreToReadyCancelled]
  · rw [returnDonationToCancelledCaller, cutThreadReplyFrameOut, restoreToReadyCancelled,
      consumeReplyLink, unlinkReplyWaiterOpt]
  · rw [removeFromNotificationWaitQueue, restoreToReadyCancelled]

theorem cutHeadFrameKeepingContext (rid) :
    Lifecycle.Suspend.cutHeadFrameKeepingContext (s.withPerCoreTlb t) rid =
      (Lifecycle.Suspend.cutHeadFrameKeepingContext s rid).withPerCoreTlb t := by
  unfold Lifecycle.Suspend.cutHeadFrameKeepingContext
  simp only [replyFrameHeadContext?, getReply?]
  split
  · rfl
  rename_i scId _
  split
  · rfl
  rename_i r _
  obtain ⟨s1, h1, h1'⟩ := storeObject_ok s t rid.toObjId (.reply { r with next := none })
  rw [h1, h1']; dsimp only
  rw [updateSchedContext]
  simp only [getSchedContext?, getTcb?]
  repeat' split
  all_goals first | rfl | rw [updateTcb, markKeyChangeFrom]

theorem cutThreadHeadFrameKeepingContext (tcb) :
    Lifecycle.Suspend.cutThreadHeadFrameKeepingContext (s.withPerCoreTlb t) tcb =
      (Lifecycle.Suspend.cutThreadHeadFrameKeepingContext s tcb).withPerCoreTlb t := by
  unfold Lifecycle.Suspend.cutThreadHeadFrameKeepingContext
  split
  · rfl
  · exact cutHeadFrameKeepingContext s t _

theorem cutCancelledCallerHead (tcb) :
    Lifecycle.Suspend.cutCancelledCallerHead (s.withPerCoreTlb t) tcb =
      (Lifecycle.Suspend.cutCancelledCallerHead s tcb).withPerCoreTlb t := by
  unfold Lifecycle.Suspend.cutCancelledCallerHead
  split
  · exact cutThreadHeadFrameKeepingContext s t _
  · rfl

theorem cancelIpcKeepingContexts (tid tcb) :
    Lifecycle.Suspend.cancelIpcKeepingContexts (s.withPerCoreTlb t) tid tcb =
      (Lifecycle.Suspend.cancelIpcKeepingContexts s tid tcb).withPerCoreTlb t := by
  unfold Lifecycle.Suspend.cancelIpcKeepingContexts
  rw [cutCancelledCallerHead, cancelIpcBlocking]

theorem suspendCancelRevert (tid tcb e) :
    Lifecycle.Suspend.suspendCancelRevert (s.withPerCoreTlb t) tid tcb e =
      (Lifecycle.Suspend.suspendCancelRevert s tid tcb e).withPerCoreTlb t := by
  unfold Lifecycle.Suspend.suspendCancelRevert
  dsimp only
  rw [cancelIpcKeepingContexts]
  split
  · rw [propagatePipChainCrossCore]; rfl
  · rfl

end PerCoreTlbFrame

/-- **The holder's cancel commutes with a write of the per-core TLB views**: it
reads no view and writes none, so the views can be replaced before it or after
it alike. -/
theorem cancelReplyHolder_withPerCoreTlb (s : SystemState)
    (t : Vector TlbState Concurrency.numCores) (holder : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) :
    cancelReplyHolder (s.withPerCoreTlb t) holder executingCore =
      (cancelReplyHolder s holder executingCore).withPerCoreTlb t := by
  unfold cancelReplyHolder
  rw [PerCoreTlbFrame.lookupTcb]
  split
  · rfl
  · split
    · rfl
    · rw [PerCoreTlbFrame.suspendCancelRevert, PerCoreTlbFrame.updateTcb]

/-- The undo of a fill rewrites the TLB views alone, as a function of the views
it is handed: the rest of the state is carried through it untouched. -/
theorem tlbUndoFillOnCore_withPerCoreTlb (s s' : SystemState)
    (t : Vector TlbState Concurrency.numCores) (c : Concurrency.CoreId) (n0 : Nat) :
    Architecture.tlbUndoFillOnCore (s.withPerCoreTlb t) c n0 =
      s.withPerCoreTlb (Architecture.tlbUndoFillOnCore (s'.withPerCoreTlb t) c n0).perCoreTlb := by
  rw [Architecture.tlbUndoFillOnCore_eq, Architecture.tlbUndoFillOnCore_eq]; rfl

/-- **A fill, a step blind to the TLB views, and the fill's undo are the step
alone**: the access-time fill of core `c`'s view for `tid`'s IPC-buffer read,
undone (told how many entries the view held before it) after a step `f` that
commutes with every write of the views ran on the filled state, leaves exactly
`f` of the state the fill was handed.  This is what a syscall entry that fills
before its decode and reports a refusal after `f` committed (the long
`ReplyRecv` route's skip branch, which cancels the busy reply's holder,
`cancelReplyHolder_withPerCoreTlb`) reports. -/
theorem tlbUndoFillOnCore_fill_of_withPerCoreTlb (f : SystemState → SystemState)
    (st : SystemState) (c : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (n : Nat)
    (hf : ∀ t, f (st.withPerCoreTlb t) = (f st).withPerCoreTlb t) :
    Architecture.tlbUndoFillOnCore (f (Architecture.tlbFillIpcBufferOnCore st c tid n)) c
        (Architecture.tlbOnCore st c).entries.length = f st := by
  have hUndo := Architecture.tlbUndoFillOnCore_tlbFillIpcBufferOnCore st c tid n
  obtain ⟨T, hT⟩ := Architecture.tlbFillIpcBufferOnCore_eq_setPerCoreTlb st c tid n
  change Architecture.tlbFillIpcBufferOnCore st c tid n = st.withPerCoreTlb T at hT
  rw [hT] at hUndo ⊢
  rw [hf, tlbUndoFillOnCore_withPerCoreTlb _ st, hUndo]
  have hSelf := hf st.perCoreTlb
  change f st = (f st).withPerCoreTlb st.perCoreTlb at hSelf
  conv => rhs; rw [hSelf]

end SeLe4n.Kernel
