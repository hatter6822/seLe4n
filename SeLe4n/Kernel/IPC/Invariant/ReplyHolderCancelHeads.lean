-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.ReplyHolderCancelFrame
import SeLe4n.Kernel.IPC.Invariant.BlockedSenderPreservation
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement
import SeLe4n.Kernel.Lifecycle.Invariant.CancellationQueueShape
import SeLe4n.Kernel.Lifecycle.Invariant.CancellationNotificationShape
import SeLe4n.Kernel.Lifecycle.Invariant.CancellationReplyShape

/-!
# A reply holder's cancel keeps every endpoint head blocked

WS-SX SX4: the receive that follows a busy reply's cancel (`cancelReplyHolder`,
seL4-MCS `receiveIPC`'s `cancelIPC(replyTCB)`) wakes the head of the endpoint
queue it reads, so its proofs read `queueHeadBlockedConsistent` on the
cancelled state.  That fact needs no more than five conjuncts of
`ipcInvariantFull` on the state the cancel is handed (`QueueHeadCancelFacts`):
the queue-connectivity facts `cancelIpcBlockingArmPremises` names are what the
cancel owes for the *whole* bundle (`cancelReplyHolder_preserves_ipcInvariantFull`),
not for its heads.

A head is blocked on its endpoint, so a holder that waits on a reply or a
notification heads no endpoint queue: on those arms every endpoint keeps its
heads and every other thread its IPC state (`HeadFrameExcept`).  On an endpoint
arm the dequeue promotes the holder's successor, which `queueNextTargetBlocked`
says waits as the holder did (`sweptAndRestored_queueHeadBlockedConsistent`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- The five conjuncts of `ipcInvariantFull` a reply holder's cancel reads to
keep the endpoint heads blocked. -/
structure QueueHeadCancelFacts (st : SystemState) : Prop where
  heads : queueHeadBlockedConsistent st
  tails : endpointQueueTailBlockedConsistent st
  links : tcbQueueLinkIntegrity st
  acyclic : tcbQueueChainAcyclic st
  targets : queueNextTargetBlocked st

/-- The facts are conjuncts of the bundle. -/
theorem QueueHeadCancelFacts.of_ipcInvariantFull {st : SystemState} (h : ipcInvariantFull st) :
    QueueHeadCancelFacts st :=
  ⟨h.queueHeadBlockedConsistent, h.endpointQueueTailBlockedConsistent, h.2.1.2.1,
    h.2.1.chainAcyclic, h.queueNextTargetBlocked⟩

/-- **A step that keeps every endpoint head and every thread's IPC state but
`v`'s**: each endpoint it leaves stood where it does with the same two heads,
and each thread but `v` it leaves stood where it does in the same IPC state. -/
def HeadFrameExcept (v : SeLe4n.ThreadId) (st st' : SystemState) : Prop :=
  (∀ (k : SeLe4n.ObjId) (ep' : Endpoint), st'.objects[k]? = some (.endpoint ep') →
    ∃ ep, st.objects[k]? = some (.endpoint ep) ∧ ep.sendQ.head = ep'.sendQ.head ∧
      ep.receiveQ.head = ep'.receiveQ.head) ∧
  (∀ (y : SeLe4n.ThreadId) (t' : TCB), y ≠ v → st'.objects[y.toObjId]? = some (.tcb t') →
    ∃ t, st.objects[y.toObjId]? = some (.tcb t) ∧ t.ipcState = t'.ipcState)

namespace HeadFrameExcept

variable {v : SeLe4n.ThreadId} {st st' st'' : SystemState}

theorem refl (v : SeLe4n.ThreadId) (st : SystemState) : HeadFrameExcept v st st :=
  ⟨fun _ ep h => ⟨ep, h, rfl, rfl⟩, fun _ t _ h => ⟨t, h, rfl⟩⟩

theorem trans (h1 : HeadFrameExcept v st st') (h2 : HeadFrameExcept v st' st'') :
    HeadFrameExcept v st st'' :=
  ⟨fun k ep'' h => by
    obtain ⟨ep', h', s2, r2⟩ := h2.1 k ep'' h
    obtain ⟨ep, h0, s1, r1⟩ := h1.1 k ep' h'
    exact ⟨ep, h0, s1.trans s2, r1.trans r2⟩,
   fun y t'' hy h => by
    obtain ⟨t', h', e2⟩ := h2.2 y t'' hy h
    obtain ⟨t, h0, e1⟩ := h1.2 y t' hy h'
    exact ⟨t, h0, e1.trans e2⟩⟩

/-- A frame that keeps every endpoint and every thread's IPC state. -/
theorem of_frames (hE : ∀ (k : SeLe4n.ObjId) (ep : Endpoint), st'.objects[k]? = some (.endpoint ep) →
      st.objects[k]? = some (.endpoint ep))
    (hT : ipcStateFrame st st') : HeadFrameExcept v st st' :=
  ⟨fun k ep h => ⟨ep, hE k ep h, rfl, rfl⟩, fun y t' _ h => hT y t' h⟩

/-- **The payoff**: a step that keeps the heads and every IPC state but a
thread's that heads no endpoint queue keeps every head blocked. -/
theorem heads (hF : HeadFrameExcept v st st') (hQ : queueHeadBlockedConsistent st)
    (hNot : ∀ (k : SeLe4n.ObjId) (ep : Endpoint), st.objects[k]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some v ∧ ep.receiveQ.head ≠ some v) :
    queueHeadBlockedConsistent st' := by
  intro k ep' hd t' hE hT
  obtain ⟨ep, hE0, hs, hr⟩ := hF.1 k ep' hE
  obtain ⟨hNs, hNr⟩ := hNot k ep hE0
  have hdv : ∀ q : IntrusiveQueue, q.head = some hd → q.head ≠ some v → hd ≠ v :=
    fun _ h1 h2 e => h2 (e ▸ h1)
  constructor
  · intro hh
    obtain ⟨t, hT0, he⟩ := hF.2 hd t' (hdv _ (hr.trans hh) hNr) hT
    rw [← he]; exact (hQ k ep hd t hE0 hT0).1 (hr.trans hh)
  · intro hh
    obtain ⟨t, hT0, he⟩ := hF.2 hd t' (hdv _ (hs.trans hh) hNs) hT
    rw [← he]; exact (hQ k ep hd t hE0 hT0).2 (hs.trans hh)

end HeadFrameExcept

/-- A thread that waits on no endpoint heads no endpoint queue. -/
theorem notEndpointHead_of_notQueueBlocked {st : SystemState} {v : SeLe4n.ThreadId} {t : TCB}
    (hQ : queueHeadBlockedConsistent st) (hT : st.objects[v.toObjId]? = some (.tcb t))
    (hNE : ∀ e, t.ipcState ≠ .blockedOnSend e ∧ t.ipcState ≠ .blockedOnReceive e ∧
      t.ipcState ≠ .blockedOnCall e) :
    ∀ (k : SeLe4n.ObjId) (ep : Endpoint), st.objects[k]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some v ∧ ep.receiveQ.head ≠ some v := fun k ep hE =>
  ⟨fun h => by
    rcases (hQ k ep v t hE hT).2 h with h' | h'
    · exact (hNE k).1 h'
    · exact (hNE k).2.2 h',
   fun h => (hNE k).2.1 ((hQ k ep v t hE hT).1 h)⟩

/-- A map frame on the IPC state is an `ipcStateFrame`. -/
theorem ipcStateFrame_of_map {st st' : SystemState}
    (h : ∀ x, (st'.getTcb? x).map TCB.ipcState = (st.getTcb? x).map TCB.ipcState) :
    ipcStateFrame st st' := fun t tcb' ht => by
  have e := h t
  rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr ht] at e
  cases hs : st.getTcb? t with
  | none => rw [hs] at e; cases e
  | some x =>
    rw [hs] at e
    exact ⟨x, (SystemState.getTcb?_eq_some_iff _ _ _).mp hs, (Option.some.inj e).symm⟩

/-- A sched-context update leaves every object that is not a sched context
where it found it. -/
theorem updateSchedContext_objects_back_nonSc {st : SystemState}
    {scId : SeLe4n.SchedContextId} {f : SchedContext → SchedContext}
    (hInv : st.objects.invExt) {k : SeLe4n.ObjId} {o : KernelObject}
    (ho : ∀ sc, o ≠ .schedContext sc) (h : (st.updateSchedContext scId f).objects[k]? = some o) :
    st.objects[k]? = some o := by
  by_cases hk : scId.toObjId = k
  · subst hk
    cases hS : st.getSchedContext? scId with
    | none => rwa [SystemState.updateSchedContext_eq_self_of_none hS] at h
    | some sc =>
      rw [SystemState.updateSchedContext_eq_of_some hS] at h
      have e : (st.objects.insert scId.toObjId (.schedContext (f sc)))[scId.toObjId]? =
          some (.schedContext (f sc)) :=
        SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self _ _ _ hInv
      simp only at h
      rw [e] at h
      exact absurd (Option.some.inj h).symm (ho _)
  · rwa [SystemState.updateSchedContext_objects_ne _ _ _ _ hk hInv] at h

namespace HeadFrameExcept

/-- A write to `v`'s own TCB. -/
theorem updateTcb_self (st : SystemState) (v : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : st.objects.invExt) : HeadFrameExcept v st (st.updateTcb v f) :=
  ⟨fun _ ep h => ⟨ep, updateTcb_objects_back_nonTcb hInv (fun _ h => by cases h) h, rfl, rfl⟩,
   fun y t' hy h => ⟨t', by
      rwa [SystemState.updateTcb_objects_ne st v f _
        (fun e => hy (SeLe4n.ThreadId.toObjId_injective _ _ e).symm) hInv] at h, rfl⟩⟩

/-- The cancelled thread's restore writes its TCB alone. -/
theorem restoreToReadyCancelled (st : SystemState) (v : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    HeadFrameExcept v st (Lifecycle.Suspend.restoreToReadyCancelled st v) := by
  unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
  exact updateTcb_self st v _ hInv

/-- The priority revert writes boosts and run-queue links. -/
theorem propagatePip (v : SeLe4n.ThreadId) (st : SystemState) (s : SeLe4n.ThreadId)
    (ec : Concurrency.CoreId) (fuel : Nat) (hInv : st.objects.invExt) :
    HeadFrameExcept v st (PriorityInheritance.propagatePipChainCrossCore st s ec fuel).1 :=
  of_frames (fun k ep h => by
      rcases PriorityInheritance.propagatePipChainCrossCore_objects_pointwise fuel st s ec hInv k
        with e | ⟨_, _, _, h2, _⟩
      · rwa [e] at h
      · rw [h2] at h; cases h)
    (propagatePipChainCrossCore_ipcStateFrame st s ec fuel hInv)

/-- The cut of the caller's frame off the context it heads writes a reply, a
sched context and a binding. -/
theorem cutCancelledCallerHead (v : SeLe4n.ThreadId) (st : SystemState) (tcb : TCB)
    (hInv : st.objects.invExt) :
    HeadFrameExcept v st (Lifecycle.Suspend.cutCancelledCallerHead st tcb) := by
  refine of_frames ?_ (ipcStateFrame_of_map fun x =>
    cutCancelledCallerHead_getTcb?_map st tcb TCB.ipcState (fun _ => rfl) hInv x)
  exact (Lifecycle.Suspend.cutCancelledCallerHead_closed
    (fun s => s.objects.invExt ∧ ∀ (k : SeLe4n.ObjId) (ep : Endpoint),
      s.objects[k]? = some (.endpoint ep) → st.objects[k]? = some (.endpoint ep))
    (fun s s1 rid r scId ⟨hI, hP⟩ _ _ hS => by
      have hI1 := storeObject_preserves_objects_invExt s _ _ _ hI hS
      refine ⟨SystemState.updateSchedContext_preserves_objects_invExt _ scId _ hI1,
        fun k ep h => hP k ep ?_⟩
      have h1 := updateSchedContext_objects_back_nonSc hI1 (fun _ h => by cases h) h
      by_cases hk : k = rid.toObjId
      · subst hk; rw [storeObject_objects_eq s s1 _ _ hI hS] at h1; cases h1
      · rwa [storeObject_objects_ne s s1 rid.toObjId k _ hk hI hS] at h1)
    (fun s _ holder _ _ ⟨hI, hP⟩ _ _ _ => by
      refine ⟨by
        rw [markKeyChangeFrom_objects]
        exact SystemState.updateTcb_preserves_objects_invExt _ _ _ hI, fun k ep h => ?_⟩
      rw [markKeyChangeFrom_objects] at h
      exact hP k ep (updateTcb_objects_back_nonTcb hI (fun _ h => by cases h) h))
    st tcb ⟨hInv, fun _ _ h => h⟩).2

/-- Taking a frame off its reply stack writes replies alone. -/
theorem cutThreadReplyFrameOut (v : SeLe4n.ThreadId) (st : SystemState) (tcb : TCB)
    (hInv : st.objects.invExt) : HeadFrameExcept v st (cutThreadReplyFrameOut st tcb) :=
  of_frames (fun k ep h => by
      rcases cutThreadReplyFrameOut_cases st tcb with e | ⟨rid, _, e⟩
      · rwa [e] at h
      · rcases cutReplyFrameOut_objects_rewrite hInv e k with e2 | ⟨_, _, _, h2, _⟩
        · rwa [e2] at h
        · rw [h2] at h; cases h)
    (fun _ tcb' h => ⟨tcb', cutThreadReplyFrameOut_tcb_backward st tcb hInv _ _ h, rfl⟩)

/-- Consuming the caller's reply link writes the reply and the link codes. -/
theorem consumeReplyLink (v : SeLe4n.ThreadId) (st : SystemState) (c : SeLe4n.ThreadId)
    (tcb : TCB) (hInv : st.objects.invExt) :
    HeadFrameExcept v st (Lifecycle.Suspend.consumeReplyLink st c tcb) :=
  of_frames (fun k ep h => by
      cases hR : tcb.replyObject with
      | none => rwa [Lifecycle.Suspend.consumeReplyLink_none _ _ _ hR] at h
      | some rid =>
        rw [Lifecycle.Suspend.consumeReplyLink_some _ _ _ _ hR] at h
        exact (SystemState.consumeCallerReply_nonTcbNonReply_agree st _ c rid hInv
          (SystemState.consumeCallerReply_eq_link st c rid) k _ (fun _ h => by cases h)
          (fun _ h => by cases h)).mp h)
    (ipcStateFrame_of_map fun x =>
      consumeReplyLink_map_frame TCB.ipcState (fun _ => rfl) st c tcb hInv x)

/-- The exit from a server's reply-waiter queue writes reply-waiter links. -/
theorem unlinkReplyWaiterOpt (v : SeLe4n.ThreadId) (st : SystemState) (w : SeLe4n.ThreadId)
    (s? : Option SeLe4n.ThreadId) : HeadFrameExcept v st (st.unlinkReplyWaiterOpt w s?) := by
  have hA := SystemState.unlinkReplyWaiterOpt_objectsAgreeOffReplyLinks st w s?
  refine of_frames (fun k ep h => ?_) (fun t tcb' h => ?_)
  · have e := hA k
    rw [h] at e
    cases h0 : st.objects[k]? with
    | none => rw [h0] at e; cases e
    | some o =>
      rw [h0] at e
      exact congrArg some (KernelObject.withoutReplyLinks_eq_of_not_tcb
        (Option.some.inj e).symm (fun _ h => by cases h))
  · have e := hA t.toObjId
    rw [h] at e
    cases h0 : st.objects[t.toObjId]? with
    | none => rw [h0] at e; cases e
    | some o =>
      rw [h0] at e
      obtain ⟨t0, rfl, h2⟩ := KernelObject.withoutReplyLinks_eq_tcb (Option.some.inj e).symm
      exact ⟨t0, rfl, by simpa [TCB.withoutReplyLinks] using congrArg TCB.ipcState h2⟩

/-- The notification arm writes the notification, the holder and its two
notification-queue neighbours' notification links. -/
theorem purgedAndRestored (st : SystemState) (v : SeLe4n.ThreadId) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV) :
    HeadFrameExcept v st (SeLe4n.Kernel.purgedAndRestored st v true) :=
  ⟨fun k ep h => ⟨ep, (purgedAndRestored_nonNotification st v true tcbV hInv hLookup k _
      (fun _ h => by cases h) (fun _ h => by cases h)).mp h, rfl, rfl⟩,
   fun y t' hy h => by
    obtain ⟨t0, h0, np, nn, rfl⟩ := purgedAndRestored_tcb_backward st v true hInv _ t'
      (fun e => hy (SeLe4n.ThreadId.toObjId_injective _ _ e)) h
    exact ⟨t0, h0, rfl⟩⟩

end HeadFrameExcept

/-- **seL4-MCS `cancelIPC`'s teardown keeps every endpoint head blocked**: on an
endpoint arm the dequeue promotes a successor that waits as the holder did, and
on every other arm the holder headed no queue and nothing else moved. -/
theorem cancelIpcKeepingContexts_queueHeadBlockedConsistent (st : SystemState)
    (v : SeLe4n.ThreadId) (tcb : TCB) (hInv : st.objects.invExt)
    (hLookup : lookupTcb st v = some tcb) (F : QueueHeadCancelFacts st) :
    queueHeadBlockedConsistent (Lifecycle.Suspend.cancelIpcKeepingContexts st v tcb) := by
  have hT := lookupTcb_some_objects st v tcb hLookup
  have hCutId : (∀ e r, tcb.ipcState ≠ .blockedOnReply e r) →
      Lifecycle.Suspend.cutCancelledCallerHead st tcb = st := fun hN => by
    unfold Lifecycle.Suspend.cutCancelledCallerHead
    split
    · rename_i e r h; exact absurd h (hN e r)
    · rfl
  have hEpArm : ∀ e, (tcb.ipcState = .blockedOnSend e ∨ tcb.ipcState = .blockedOnReceive e ∨
      tcb.ipcState = .blockedOnCall e) →
      queueHeadBlockedConsistent (Lifecycle.Suspend.cancelIpcKeepingContexts st v tcb) := by
    intro e hB
    unfold Lifecycle.Suspend.cancelIpcKeepingContexts
    rw [hCutId (fun e' r h => by rcases hB with h' | h' | h' <;> rw [h'] at h <;> cases h),
      cancelIpcBlocking_endpoint_arm_eq st v tcb e hB hInv
        (endpointBoundariesOnly_of_blocked st v tcb e hT hB F.heads F.tails)]
    exact sweptAndRestored_queueHeadBlockedConsistent st v true tcb hInv F.links F.acyclic
      hLookup F.heads F.targets
  cases hIp : tcb.ipcState with
  | ready =>
    unfold Lifecycle.Suspend.cancelIpcKeepingContexts Lifecycle.Suspend.cancelIpcBlocking
    rw [hCutId (fun e r h => by rw [hIp] at h; cases h), hIp]
    exact F.heads
  | blockedOnSend e => exact hEpArm e (Or.inl hIp)
  | blockedOnReceive e => exact hEpArm e (Or.inr (Or.inl hIp))
  | blockedOnCall e => exact hEpArm e (Or.inr (Or.inr hIp))
  | blockedOnNotification n =>
    unfold Lifecycle.Suspend.cancelIpcKeepingContexts
    rw [hCutId (fun e r h => by rw [hIp] at h; cases h),
      cancelIpcBlocking_notification_arm_eq st v tcb n hIp]
    exact (HeadFrameExcept.purgedAndRestored st v tcb hInv hLookup).heads F.heads
      (notEndpointHead_of_notQueueBlocked F.heads hT fun _ => by
        rw [hIp]; refine ⟨?_, ?_, ?_⟩ <;> intro h <;> cases h)
  | blockedOnReply e r =>
    rw [Lifecycle.Suspend.cancelIpcKeepingContexts_reply_arm st v tcb e r hIp hInv]
    have hC : Lifecycle.Suspend.cutCancelledCallerHead st tcb =
        Lifecycle.Suspend.cutThreadHeadFrameKeepingContext st tcb := by
      unfold Lifecycle.Suspend.cutCancelledCallerHead; rw [hIp]
    have h1 := HeadFrameExcept.cutCancelledCallerHead v st tcb hInv
    rw [hC] at h1
    have hI1 : (Lifecycle.Suspend.cutThreadHeadFrameKeepingContext st tcb).objects.invExt := by
      rw [← hC]; exact Lifecycle.Suspend.cutCancelledCallerHead_preserves_objects_invExt st tcb hInv
    have hI2 := cutThreadReplyFrameOut_preserves_objects_invExt _ tcb hI1
    have hI3 := Lifecycle.Suspend.restoreToReadyCancelled_invExt _ v hI2
    have hI4 := Lifecycle.Suspend.consumeReplyLink_preserves_objects_invExt _ v tcb hI3
    refine ((((h1.trans (HeadFrameExcept.cutThreadReplyFrameOut v _ tcb hI1)).trans
      (HeadFrameExcept.restoreToReadyCancelled _ v hI2)).trans
      (HeadFrameExcept.consumeReplyLink v _ v tcb hI3)).trans
      (HeadFrameExcept.unlinkReplyWaiterOpt v _ v _)).heads F.heads
      (notEndpointHead_of_notQueueBlocked F.heads hT fun _ => by
        rw [hIp]; refine ⟨?_, ?_, ?_⟩ <;> intro h <;> cases h)

/-- A step that keeps every endpoint head and every thread's IPC state keeps
every head blocked. -/
theorem HeadFrameExcept.heads_of_ipcStateFrame {v : SeLe4n.ThreadId} {st st' : SystemState}
    (hF : HeadFrameExcept v st st') (hT : ipcStateFrame st st')
    (hQ : queueHeadBlockedConsistent st) : queueHeadBlockedConsistent st' := by
  intro k ep' hd t' hE hTd
  obtain ⟨ep, hE0, hs, hr⟩ := hF.1 k ep' hE
  obtain ⟨t, hT0, he⟩ := hT hd t' hTd
  rw [← he]
  exact ⟨fun hh => (hQ k ep hd t hE0 hT0).1 (hr.trans hh),
    fun hh => (hQ k ep hd t hE0 hT0).2 (hs.trans hh)⟩

/-- A TCB write that keeps the IPC state frames every IPC state. -/
theorem ipcStateFrame_updateTcb {st : SystemState} {tid : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (hf : ∀ x, (f x).ipcState = x.ipcState) :
    ipcStateFrame st (st.updateTcb tid f) := fun w t' h => by
  obtain ⟨t, ht, he⟩ := updateTcb_getTcb?_back hInv hf
    ((SystemState.getTcb?_eq_some_iff _ _ _).mpr h)
  exact ⟨t, (SystemState.getTcb?_eq_some_iff _ _ _).mp ht, he⟩

/-- **A reply holder's cancel keeps every endpoint head blocked** (WS-SX SX4):
the IPC teardown (`cancelIpcKeepingContexts_queueHeadBlockedConsistent`), then
the boost revert and the `Inactive` write, which move no endpoint and no IPC
state. -/
theorem cancelReplyHolder_queueHeadBlockedConsistent (st : SystemState)
    (holder : SeLe4n.ThreadId) (ec : Concurrency.CoreId) (hInv : st.objects.invExt)
    (F : QueueHeadCancelFacts st) :
    queueHeadBlockedConsistent (cancelReplyHolder st holder ec) := by
  rcases cancelReplyHolder_cases st holder ec with h | ⟨tcb, hL, -, h⟩
  · rw [h]; exact F.heads
  rw [h]
  have hQ1 := cancelIpcKeepingContexts_queueHeadBlockedConsistent st holder tcb hInv hL F
  have hI1 := Lifecycle.Suspend.cancelIpcKeepingContexts_preserves_objects_invExt st holder tcb hInv
  have hQ2 : queueHeadBlockedConsistent
      (Lifecycle.Suspend.suspendCancelRevert st holder tcb ec) := by
    unfold Lifecycle.Suspend.suspendCancelRevert
    dsimp only
    split
    · exact (HeadFrameExcept.propagatePip holder _ _ ec _ hI1).heads_of_ipcStateFrame
        (propagatePipChainCrossCore_ipcStateFrame _ _ ec _ hI1) hQ1
    · exact hQ1
  have hI2 : (Lifecycle.Suspend.suspendCancelRevert st holder tcb ec).objects.invExt := by
    unfold Lifecycle.Suspend.suspendCancelRevert; dsimp only; split
    · exact PriorityInheritance.propagatePipChainCrossCore_preserves_objects_invExt _ _ _ _ hI1
    · exact hI1
  exact (HeadFrameExcept.updateTcb_self _ holder _ hI2).heads_of_ipcStateFrame
    (ipcStateFrame_updateTcb hI2 fun _ => rfl) hQ2

end SeLe4n.Kernel
