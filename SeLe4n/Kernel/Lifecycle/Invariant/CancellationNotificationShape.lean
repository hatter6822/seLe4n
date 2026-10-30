-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Invariant.CancellationQueueShape

/-!
# WS-RR RR7.22 (residual) — the cancellation purge's notification shape

`cancelIpcBlocking`'s blocked-on-notification arm is
`restoreToReadyCancelled (removeFromNotificationWaitQueue st v) v`.  It is the
second of the operation's three sweeping arms, and it needs its own engine for
the same reason the endpoint arm did: the purge is a fold over the whole object
store, not a splice, so no result about either of the other arms applies to it.

## What is easier here, and what is harder

**Easier**: the purge writes *only notifications*.  Away from the swept thread
every TCB survives verbatim — there is no splice, so no neighbour is relinked —
which is why this module's pullback is an equality where the endpoint arm's is a
record rewrite, and why acyclicity transports path-for-path rather than by an
argument about what the operation added.  `ipcInvariant` itself was already
proved of the purge (`removeFromNotificationWaitQueue_preserves_ipcInvariant`);
what is new is carrying it through the restore, and the other nineteen conjuncts.

**Harder**: there is no splice to repair the swept thread's *neighbours*.  The
restore clears its `queuePrev` / `queueNext`, and a thread linked into an
endpoint chain while blocked on a notification would leave a dangling link
behind.  `ipcInvariantFull` does not forbid that — `ipcStateQueueMembershipConsistent`'s
`.blockedOnNotification` arm is `True`, `queueNextBlockingMatch`'s catch-all
admits a notification-blocked source, and `queueNextTargetBlocked` constrains a
successor only when the *source* is endpoint-blocked.  So the fact is **stated**,
as `sweptThreadOffQueueChains`, in exactly the way this arm's sibling states its
three (see `CancellationQueueShape`'s header): a caller discharges it from the
notification wait list it is cancelling out of.

What is *not* a hypothesis here is that the swept thread bounds no endpoint
queue: the two boundary conjuncts demand a blocking state a notification-blocked
thread does not have, so
`purgedAndRestored_victim_off_endpoint_boundaries` derives it.  Nor is "holds no
Reply object" — `replyObject_none_of_not_blockedOnReply` derives that from the
bundle's own reciprocity.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.RobinHood

-- ============================================================================
-- §1  The purge's pointwise readings
-- ============================================================================

/-- **`v0.35.166`: the notification unlink writes no scheduling context.**

Beside the unlink's other pointwise readings for the reason the endpoint
sweep's twin sits beside its own: WS-RR RR8.11 wrote both `private` in
`IPC/Invariant/CancellationBundle.lean`, downstream of the destroy path and of
the retype wrapper, so neither could state a reservation theorem over this
sweep. -/
theorem removeFromNotificationWaitQueue_getSchedContext?_eq (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (scId : SeLe4n.SchedContextId) :
    (removeFromNotificationWaitQueue st tid).getSchedContext? scId
      = st.getSchedContext? scId := by
  refine SystemState.getSchedContext?_eq_of_kind_iff (fun sc => ?_)
  exact removeFromNotificationWaitQueue_other_slot st tid hInv
    scId.toObjId (.schedContext sc) (fun n => fun hc => KernelObject.noConfusion hc)
    (fun t => fun hc => KernelObject.noConfusion hc)

/-- **`v0.35.166`: the notification unlink frames every thread's home core.**

The unlink rewrites a waiter's neighbours' notification-queue links and nothing
else of any TCB, so every TCB's placement (home core and run-queue links) is
unchanged. -/
theorem removeFromNotificationWaitQueue_placement_frame (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (x : SeLe4n.ThreadId) :
    ((removeFromNotificationWaitQueue st tid).getTcb? x).map TCB.placement
      = (st.getTcb? x).map TCB.placement :=
  removeFromNotificationWaitQueue_tcbField_frame TCB.placement
    (fun _ _ _ _ _ _ => rfl) st tid hInv x

/-- A notification reading after the unlink came from one at the same key, with
its `pendingBadge` untouched — the unlink rewrites only the queue ends and the
state derived from them. -/
theorem removeFromNotificationWaitQueue_notification_badge (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (k : SeLe4n.ObjId) (n : Notification)
    (h : (removeFromNotificationWaitQueue st tid).objects[k]? = some (.notification n)) :
    ∃ n0, st.objects[k]? = some (.notification n0) ∧ n.pendingBadge = n0.pendingBadge := by
  rcases (removeFromNotificationWaitQueue_reach st tid hInv).2 k with
    hEq | ⟨n0, n', hn, hn', hB, _, _⟩ | ⟨t, t', _, ht', _⟩
  · exact ⟨n, hEq ▸ h, rfl⟩
  · rw [h] at hn'; cases hn'; exact ⟨n0, hn, hB⟩
  · rw [h] at ht'; cases ht'

-- ============================================================================
-- §2  The purge-then-restore composite
-- ============================================================================

def purgedAndRestored (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) : SystemState :=
  Lifecycle.Suspend.restoreToReadyStaging (removeFromNotificationWaitQueue st v) v frame

/-- Away from the swept thread, the composite's TCB readings are the pre-state's
up to the notification-queue links of the swept thread's neighbours, which the
unlink rewrites to close the gap it leaves. -/
theorem purgedAndRestored_tcb_backward (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame)
    (hInv : st.objects.invExt) (k : SeLe4n.ObjId) (t : TCB) (hNe : k ≠ v.toObjId)
    (h : (purgedAndRestored st v frame).objects[k]? = some (.tcb t)) :
    ∃ t0, st.objects[k]? = some (.tcb t0) ∧ tcbNtfnLinkRewrite t t0 := by
  have hExt : (removeFromNotificationWaitQueue st v).objects.invExt :=
    removeFromNotificationWaitQueue_preserves_objects_invExt st v hInv
  unfold purgedAndRestored at h
  rw [restoreToReadyStaging_objects_ne _ v frame k hExt hNe] at h
  exact removeFromNotificationWaitQueue_tcb_backward st v k t hInv h

/-- At the swept thread, the composite holds the restored TCB — restored from
the record the unlink left, which is the pre-state's up to its own
notification-queue links (the restore leaves those dead links alone, as seL4's
dequeue does). -/
theorem purgedAndRestored_victim_tcb (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV) :
    ∃ t1, tcbNtfnLinkRewrite t1 tcbV ∧
      (purgedAndRestored st v frame).objects[v.toObjId]? = some (.tcb (restoredTcb t1 frame)) := by
  have hExt : (removeFromNotificationWaitQueue st v).objects.invExt :=
    removeFromNotificationWaitQueue_preserves_objects_invExt st v hInv
  obtain ⟨t1, h1, hR⟩ := removeFromNotificationWaitQueue_tcb_forward st v v.toObjId tcbV hInv
    (lookupTcb_some_objects st v tcbV hLookup)
  exact ⟨t1, hR, restoreToReadyStaging_objects_self _ v frame t1 hExt
    ((SystemState.getTcb?_eq_some_iff _ v t1).mpr h1)⟩

/-- Objects that are neither notifications nor the swept thread's TCB are
untouched. -/
theorem purgedAndRestored_nonNotification (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (k : SeLe4n.ObjId) (o : KernelObject)
    (hNotN : ∀ n, o ≠ .notification n) (hNotTcb : ∀ t, o ≠ .tcb t) :
    ((purgedAndRestored st v frame).objects[k]? = some o) ↔ (st.objects[k]? = some o) := by
  have hExt : (removeFromNotificationWaitQueue st v).objects.invExt :=
    removeFromNotificationWaitQueue_preserves_objects_invExt st v hInv
  by_cases hkv : k = v.toObjId
  · subst hkv
    obtain ⟨t1, -, hV⟩ := purgedAndRestored_victim_tcb st v frame tcbV hInv hLookup
    constructor
    · intro hx
      rw [hV] at hx
      exact absurd (Option.some.inj hx).symm (hNotTcb _)
    · intro hx
      rw [lookupTcb_some_objects st v tcbV hLookup] at hx
      exact absurd (Option.some.inj hx).symm (hNotTcb tcbV)
  · unfold purgedAndRestored
    rw [restoreToReadyStaging_objects_ne _ v frame k hExt hkv]
    exact removeFromNotificationWaitQueue_other_slot st v hInv k o hNotN hNotTcb

/-- A notification reading after the composite has the pre-state's badge. -/
theorem purgedAndRestored_notification_badge (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (k : SeLe4n.ObjId) (n : Notification)
    (h : (purgedAndRestored st v frame).objects[k]? = some (.notification n)) :
    ∃ n0, st.objects[k]? = some (.notification n0) ∧ n.pendingBadge = n0.pendingBadge := by
  have hExt : (removeFromNotificationWaitQueue st v).objects.invExt :=
    removeFromNotificationWaitQueue_preserves_objects_invExt st v hInv
  have hkv : k ≠ v.toObjId := by
    intro hEq
    obtain ⟨t1, -, hV⟩ := purgedAndRestored_victim_tcb st v frame tcbV hInv hLookup
    rw [hEq, hV] at h
    cases h
  unfold purgedAndRestored at h
  rw [restoreToReadyStaging_objects_ne _ v frame k hExt hkv] at h
  exact removeFromNotificationWaitQueue_notification_badge st v hInv k n h

/-- The composite touches no scheduler state. -/
theorem purgedAndRestored_scheduler_eq (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) :
    (purgedAndRestored st v frame).scheduler = st.scheduler := by
  unfold purgedAndRestored
  rw [Lifecycle.Suspend.restoreToReadyStaging_scheduler_eq,
    removeFromNotificationWaitQueue_scheduler_eq]

-- ============================================================================
-- §3  The coherence hypothesis, and the TCB pullback it licenses
-- ============================================================================

/-- **WS-RR RR7.22 (residual)**: the swept thread is off every `queueNext` chain.

The notification arm has no splice: the restore clears the swept thread's links
and nothing repairs its neighbours, so a thread linked into an endpoint chain
while blocked on a *notification* would leave a dangling `queueNext` behind.
`ipcInvariantFull` does not forbid that — `ipcStateQueueMembershipConsistent`'s
`.blockedOnNotification` arm is `True`, and `queueNextBlockingMatch`'s catch-all
admits a `.ready` or notification-blocked source — so the fact is stated, as the
three queue-coherence clauses of the endpoint arm are. -/
def sweptThreadOffQueueChains (st : SystemState) (tid : SeLe4n.ThreadId) : Prop :=
  ∀ tcb, lookupTcb st tid = some tcb → tcb.queuePrev = none ∧ tcb.queueNext = none

/-- The composite's TCB pullback: away from the swept thread the pre-state's TCB
up to its notification-queue links, at the swept thread the restored one. -/
theorem purgedAndRestored_tcb_pullback (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (k : SeLe4n.ObjId) (tA : TCB)
    (h : (purgedAndRestored st v frame).objects[k]? = some (.tcb tA)) :
    (k ≠ v.toObjId ∧ ∃ t0, st.objects[k]? = some (.tcb t0) ∧ tcbNtfnLinkRewrite tA t0) ∨
      (k = v.toObjId ∧ ∃ t1, tcbNtfnLinkRewrite t1 tcbV ∧ tA = restoredTcb t1 frame) := by
  by_cases hk : k = v.toObjId
  · subst hk
    obtain ⟨t1, hR, hV⟩ := purgedAndRestored_victim_tcb st v frame tcbV hInv hLookup
    rw [hV] at h
    exact Or.inr ⟨rfl, t1, hR, (KernelObject.tcb.inj (Option.some.inj h)).symm⟩
  · exact Or.inl ⟨hk, purgedAndRestored_tcb_backward st v frame hInv k tA hk h⟩

/-- The composite's TCB, read forwards away from the swept thread. -/
theorem purgedAndRestored_tcb_forward (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame)
    (hInv : st.objects.invExt) (k : SeLe4n.ObjId) (t0 : TCB) (hkv : k ≠ v.toObjId)
    (h : st.objects[k]? = some (.tcb t0)) :
    ∃ tA, (purgedAndRestored st v frame).objects[k]? = some (.tcb tA) ∧
      tcbNtfnLinkRewrite tA t0 := by
  have hExt : (removeFromNotificationWaitQueue st v).objects.invExt :=
    removeFromNotificationWaitQueue_preserves_objects_invExt st v hInv
  unfold purgedAndRestored
  rw [restoreToReadyStaging_objects_ne _ v frame k hExt hkv]
  exact removeFromNotificationWaitQueue_tcb_forward st v k t0 hInv h

/-- **The composite writes no queue link.**  Away from the swept thread the TCB
is the pre-state's; at the swept thread the restore writes `none` over fields the
hypothesis already says are `none`. -/
theorem purgedAndRestored_tcb_links (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hOff : sweptThreadOffQueueChains st v)
    (k : SeLe4n.ObjId) (tA : TCB)
    (h : (purgedAndRestored st v frame).objects[k]? = some (.tcb tA)) :
    ∃ t0, st.objects[k]? = some (.tcb t0) ∧
      tA.queuePrev = t0.queuePrev ∧ tA.queueNext = t0.queueNext := by
  rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup k tA h with
    ⟨_, t0, h0, np, nn, rfl⟩ | ⟨hk, t1, ⟨np, nn, rfl⟩, rfl⟩
  · exact ⟨t0, h0, rfl, rfl⟩
  · obtain ⟨hp, hn⟩ := hOff tcbV hLookup
    exact ⟨tcbV, by rw [hk]; exact lookupTcb_some_objects st v tcbV hLookup,
      by rw [restoredTcb_queuePrev, hp], by rw [restoredTcb_queueNext, hn]⟩

/-- ...and the reading is an equivalence, so a pre-state link reappears
unchanged. -/
theorem purgedAndRestored_tcb_links_forward (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hOff : sweptThreadOffQueueChains st v)
    (k : SeLe4n.ObjId) (t0 : TCB)
    (h : st.objects[k]? = some (.tcb t0)) :
    ∃ tA, (purgedAndRestored st v frame).objects[k]? = some (.tcb tA) ∧
      tA.queuePrev = t0.queuePrev ∧ tA.queueNext = t0.queueNext := by
  by_cases hk : k = v.toObjId
  · subst hk
    have hx : t0 = tcbV := by
      rw [lookupTcb_some_objects st v tcbV hLookup] at h
      exact (KernelObject.tcb.inj (Option.some.inj h)).symm
    obtain ⟨hp, hn⟩ := hOff tcbV hLookup
    obtain ⟨t1, ⟨np, nn, rfl⟩, hV⟩ := purgedAndRestored_victim_tcb st v frame tcbV hInv hLookup
    exact ⟨_, hV, by rw [restoredTcb_queuePrev, hx, hp],
      by rw [restoredTcb_queueNext, hx, hn]⟩
  · obtain ⟨tA, hA, np, nn, rfl⟩ := purgedAndRestored_tcb_forward st v frame hInv k t0 hk h
    exact ⟨_, hA, rfl, rfl⟩

-- ============================================================================
-- §4  The dual-queue system invariant
-- ============================================================================

/-- **WS-RR RR7.22 (residual)**: reachability in the composite is reachability in
the pre-state — indeed the *same* path, since no `queueNext` field moves. -/
theorem purgedAndRestored_path_transport
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hOff : sweptThreadOffQueueChains st v)
    {x y : SeLe4n.ThreadId} (h : QueueNextPath (purgedAndRestored st v frame) x y) :
    QueueNextPath st x y := by
  induction h with
  | single a b tcb hA hN =>
    obtain ⟨t0, h0, _, hn⟩ :=
      purgedAndRestored_tcb_links st v frame tcbV hInv hLookup hOff a.toObjId tcb hA
    exact .single a b t0 h0 (by rw [← hn]; exact hN)
  | cons a b c tcb hA hN _ ih =>
    obtain ⟨t0, h0, _, hn⟩ :=
      purgedAndRestored_tcb_links st v frame tcbV hInv hLookup hOff a.toObjId tcb hA
    exact .cons a b c t0 h0 (by rw [← hn]; exact hN) ih

/-- A notification-queue unlink keeps every slot's binding codes: it rewrites a
notification's queue and a thread's notification links, never a binding. -/
theorem ntfnUnlinkSlotRel_bindingCodes {o o' : Option KernelObject}
    (h : ntfnUnlinkSlotRel o o') : notificationBindingCodes o' = notificationBindingCodes o := by
  rcases h with rfl | ⟨n, n', rfl, rfl, -, hT, -⟩ | ⟨t, t', rfl, rfl, np, nn, rfl⟩
  · rfl
  · have e := congrArg SeLe4n.ThreadId.optCode hT
    simp only [Notification.boundTCB, SeLe4n.ThreadId.optCode_ofOptCode] at e
    simp only [notificationBindingCodes, KernelObject.bindingCodes, e]
  · rfl

/-- The composite moves no notification-binding code. -/
theorem purgedAndRestored_sameNotificationBindings
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV) :
    sameNotificationBindings st (purgedAndRestored st v frame) := by
  have hExt : (removeFromNotificationWaitQueue st v).objects.invExt :=
    removeFromNotificationWaitQueue_preserves_objects_invExt st v hInv
  intro k
  by_cases hkv : k = v.toObjId
  · subst hkv
    obtain ⟨t1, ⟨np, nn, rfl⟩, hV⟩ := purgedAndRestored_victim_tcb st v frame tcbV hInv hLookup
    rw [hV, lookupTcb_some_objects st v tcbV hLookup]
    cases frame <;> rfl
  · have hNe : (purgedAndRestored st v frame).objects[k]? =
        (removeFromNotificationWaitQueue st v).objects[k]? := by
      unfold purgedAndRestored
      exact restoreToReadyStaging_objects_ne _ v frame k hExt hkv
    rw [hNe]
    exact ntfnUnlinkSlotRel_bindingCodes ((removeFromNotificationWaitQueue_reach st v hInv).2 k)

/-- **WS-RR RR7.22 (residual)**: the composite preserves the dual-queue system
invariant.

Every component reduces to the same two facts: endpoints are untouched (the purge
writes notifications, the restore writes one TCB), and no `queueNext`/`queuePrev`
field changes anywhere — away from the swept thread because the TCB is the
pre-state's, and at the swept thread because the restore writes `none` over
fields `sweptThreadOffQueueChains` already says are `none`.  Acyclicity therefore
transports by a path-for-path correspondence rather than by an argument about
what the operation added. -/
theorem purgedAndRestored_dualQueueSystemInvariant
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hOff : sweptThreadOffQueueChains st v)
    -- **PR #897 review (`v0.35.106`)**: the strengthened head boundary carries the
    -- head's back-pointer, and the restore clears the swept thread's — so a queue
    -- that still named it as head would be left with a head that has none.  The
    -- swept thread is blocked on a *notification*, so it bounds no endpoint queue
    -- (`purgedAndRestored_victim_off_endpoint_boundaries`), but that is
    -- `queueHeadBlockedConsistent`'s fact rather than this bundle's, so it is stated
    -- here and supplied by the composite.
    (hOffEp : ∀ (k : SeLe4n.ObjId) (e : Endpoint), st.objects[k]? = some (.endpoint e) →
      e.sendQ.head ≠ some v ∧ e.receiveQ.head ≠ some v)
    (hDual : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant (purgedAndRestored st v frame) := by
  obtain ⟨hEps, hLink, hAcyc, hPPair, hHD⟩ := hDual
  have hEpIff : ∀ (k : SeLe4n.ObjId) (ep : Endpoint),
      ((purgedAndRestored st v frame).objects[k]? = some (.endpoint ep)) ↔
        (st.objects[k]? = some (.endpoint ep)) :=
    fun k ep => purgedAndRestored_nonNotification st v frame tcbV hInv hLookup k (.endpoint ep)
      (by simp) (by simp)
  have hWF : ∀ (q : IntrusiveQueue), intrusiveQueueWellFormed q st → q.head ≠ some v →
      intrusiveQueueWellFormed q (purgedAndRestored st v frame) := by
    intro q hq hqHead
    refine ⟨hq.1, ?_, ?_⟩
    · intro hd hHd
      obtain ⟨t0, h0, hp, hpp⟩ := hq.2.1 hd hHd
      have hNeV : hd.toObjId ≠ v.toObjId := by
        intro hEq
        rw [threadId_toObjId_injective hEq] at hHd
        exact absurd hHd hqHead
      obtain ⟨tA, hA, hpA, _⟩ :=
        purgedAndRestored_tcb_links_forward st v frame tcbV hInv hLookup hOff hd.toObjId t0 h0
      -- Away from the swept thread the record is the pre-state's **verbatim**, so
      -- the head's back-pointer carries with the rest of it.
      rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup hd.toObjId tA hA with
        ⟨-, t0', h0', np, nn, rfl⟩ | ⟨hv, -⟩
      · rw [h0] at h0'
        obtain rfl : t0' = t0 := (KernelObject.tcb.inj (Option.some.inj h0')).symm
        exact ⟨_, hA, hp, hpp⟩
      · exact absurd hv hNeV
    · intro tl hTl
      obtain ⟨t0, h0, hn⟩ := hq.2.2 tl hTl
      obtain ⟨tA, hA, _, hnA⟩ :=
        purgedAndRestored_tcb_links_forward st v frame tcbV hInv hLookup hOff tl.toObjId t0 h0
      exact ⟨tA, hA, by rw [hnA]; exact hn⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro epId ep hEp
    have hEp0 : st.objects[epId]? = some (.endpoint ep) := (hEpIff epId ep).mp hEp
    have h0 := hEps epId ep hEp0
    unfold dualQueueEndpointWellFormed at h0 ⊢
    rw [hEp0] at h0
    rw [hEp]
    obtain ⟨hNeS, hNeR⟩ := hOffEp epId ep hEp0
    exact ⟨hWF ep.sendQ h0.1 hNeS, hWF ep.receiveQ h0.2 hNeR⟩
  · refine ⟨?_, ?_⟩
    · intro a tcbA hA b hNext
      obtain ⟨t0a, h0a, _, hnA⟩ :=
        purgedAndRestored_tcb_links st v frame tcbV hInv hLookup hOff a.toObjId tcbA hA
      obtain ⟨t0b, h0b, hpB⟩ := hLink.1 a t0a h0a b (by rw [← hnA]; exact hNext)
      obtain ⟨tB, hB, hpBA, _⟩ :=
        purgedAndRestored_tcb_links_forward st v frame tcbV hInv hLookup hOff b.toObjId t0b h0b
      exact ⟨tB, hB, by rw [hpBA]; exact hpB⟩
    · intro b tcbB hB a hPrev
      obtain ⟨t0b, h0b, hpB, _⟩ :=
        purgedAndRestored_tcb_links st v frame tcbV hInv hLookup hOff b.toObjId tcbB hB
      obtain ⟨t0a, h0a, hnA⟩ := hLink.2 b t0b h0b a (by rw [← hpB]; exact hPrev)
      obtain ⟨tA, hA, _, hnAA⟩ :=
        purgedAndRestored_tcb_links_forward st v frame tcbV hInv hLookup hOff a.toObjId t0a h0a
      exact ⟨tA, hA, by rw [hnAA]; exact hnA⟩
  · exact fun x hPath => hAcyc x
      (purgedAndRestored_path_transport st v frame tcbV hInv hLookup hOff hPath)
  · -- WS-RR RR8.3: the pairing.  The pullback is exact here -- away from the
    -- swept thread the record is the pre-state's verbatim, and the swept thread
    -- has BOTH back-pointers cleared by the restore (`v0.35.99`: the `none` arm
    -- claims the thread is on no queue, so `queuePrev` is part of the claim).
    intro tid tcb hTcb
    rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup tid.toObjId tcb hTcb with
      ⟨_, t0, h0, _, _, rfl⟩ | ⟨_, t1, _, rfl⟩
    · exact hPPair tid t0 h0
    · exact TCB.queuePPrevAgreesWithPrev_of_pprev_none (restoredTcb_queuePPrev t1 frame)
        (restoredTcb_queuePrev t1 frame)
  · -- **PR #897 review**: the notification purge writes notifications and the
    -- restore a TCB; neither writes an endpoint, so the fifth conjunct transports.
    exact endpointQueueHeadDisjoint_of_endpointBackward
      (fun epId ep hEp => (hEpIff epId ep).mp hEp) hHD

-- ============================================================================
-- §5  The reusable frames
-- ============================================================================

theorem purgedAndRestored_sameSchedContextBindings
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV) :
    sameSchedContextBindings st (purgedAndRestored st v frame) := by
  intro tid tcb' hTcb'
  rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup tid.toObjId tcb' hTcb' with
    ⟨_, t0, h0, _, _, rfl⟩ | ⟨hk, t1, ⟨_, _, rfl⟩, rfl⟩
  · exact ⟨t0, h0, rfl⟩
  · exact ⟨tcbV, by rw [hk]; exact lookupTcb_some_objects st v tcbV hLookup,
      by rw [restoredTcb_eq]⟩

theorem purgedAndRestored_timeoutBudgetFrame
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV) :
    timeoutBudgetFrame st (purgedAndRestored st v frame) := by
  intro tid tcb' hTcb'
  rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup tid.toObjId tcb' hTcb' with
    ⟨_, t0, h0, _, _, rfl⟩ | ⟨hk, t1, ⟨_, _, rfl⟩, rfl⟩
  · exact ⟨t0, h0, rfl⟩
  · exact ⟨tcbV, by rw [hk]; exact lookupTcb_some_objects st v tcbV hLookup,
      by rw [restoredTcb_eq]⟩

theorem purgedAndRestored_donationOwnerFrame
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hNotReply : ∀ ep rt, tcbV.ipcState ≠ .blockedOnReply ep rt) :
    donationOwnerFrame st (purgedAndRestored st v frame) := by
  have hVObj : st.objects[v.toObjId]? = some (.tcb tcbV) := lookupTcb_some_objects st v tcbV hLookup
  refine ⟨?_, ?_⟩
  · intro scId sc hsc
    exact ⟨sc, (purgedAndRestored_nonNotification st v frame tcbV hInv hLookup
      scId.toObjId (.schedContext sc) (by simp) (by simp)).mpr hsc, rfl⟩
  · intro owner ownerTcb hOwner hUnbound hBlocked
    have hne : owner.toObjId ≠ v.toObjId := by
      intro hEq
      rw [hEq, hVObj] at hOwner
      have hx : ownerTcb = tcbV := (KernelObject.tcb.inj (Option.some.inj hOwner)).symm
      obtain ⟨ep, rt, hb⟩ := hBlocked
      rw [hx] at hb
      exact hNotReply ep rt hb
    obtain ⟨tA, hA, _, _, rfl⟩ :=
      purgedAndRestored_tcb_forward st v frame hInv owner.toObjId ownerTcb hne hOwner
    exact ⟨_, hA, hUnbound, hBlocked⟩

theorem purgedAndRestored_replyLinkageFrame
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hUnlinked : tcbV.replyObject = none) :
    replyLinkageFrame st (purgedAndRestored st v frame) := by
  have hVObj : st.objects[v.toObjId]? = some (.tcb tcbV) := lookupTcb_some_objects st v tcbV hLookup
  refine ⟨replyLinkageFrame.callerAgree_of_objectAgree (fun rid r => ?_), ?_, ?_⟩
  · exact purgedAndRestored_nonNotification st v frame tcbV hInv hLookup
      rid.toObjId (.reply r) (by simp) (by simp)
  · intro tid tcb' hTcb'
    rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup tid.toObjId tcb' hTcb' with
      ⟨_, t0, h0, _, _, rfl⟩ | ⟨hk, t1, ⟨_, _, rfl⟩, rfl⟩
    · exact ⟨t0, h0, rfl⟩
    · exact ⟨tcbV, by rw [hk]; exact hVObj, by rw [restoredTcb_eq]⟩
  · intro tid tcb rid hTcb hRO
    have hne : tid.toObjId ≠ v.toObjId := by
      intro hEq
      rw [hEq, hVObj] at hTcb
      have hx : tcb = tcbV := (KernelObject.tcb.inj (Option.some.inj hTcb)).symm
      rw [hx, hUnlinked] at hRO
      cases hRO
    obtain ⟨tA, hA, _, _, rfl⟩ :=
      purgedAndRestored_tcb_forward st v frame hInv tid.toObjId tcb hne hTcb
    exact ⟨_, hA, rfl, fun ep rt hb => ⟨ep, rt, hb⟩⟩

-- ============================================================================
-- §6  The conjuncts of `ipcInvariantFull`, one at a time
-- ============================================================================

theorem purgedAndRestored_ipcInvariant
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (h : ipcInvariant st) : ipcInvariant (purgedAndRestored st v frame) := by
  have hExt : (removeFromNotificationWaitQueue st v).objects.invExt :=
    removeFromNotificationWaitQueue_preserves_objects_invExt st v hInv
  intro oid ntfn hN
  have hkv : oid ≠ v.toObjId := by
    intro hEq
    obtain ⟨_, -, hV⟩ := purgedAndRestored_victim_tcb st v frame tcbV hInv hLookup
    rw [hEq, hV] at hN
    cases hN
  unfold purgedAndRestored at hN
  rw [restoreToReadyStaging_objects_ne _ v frame oid hExt hkv] at hN
  exact removeFromNotificationWaitQueue_preserves_ipcInvariant st v hInv h oid ntfn hN

theorem purgedAndRestored_badgeWellFormed
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (h : badgeWellFormed st) : badgeWellFormed (purgedAndRestored st v frame) := by
  refine ⟨?_, ?_⟩
  · intro oid ntfn badge hN hB
    obtain ⟨n0, h0, hEq⟩ :=
      purgedAndRestored_notification_badge st v frame tcbV hInv hLookup oid ntfn hN
    exact h.1 oid n0 badge h0 (by rw [← hEq]; exact hB)
  · intro oid o slot cap badge hC hL hB
    cases o with
    | tcb tA =>
      rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup oid tA hC with
        ⟨_, t0, h0, np, nn, rfl⟩ | ⟨rfl, t1, ⟨np, nn, rfl⟩, rfl⟩
      · exact h.2 oid (.tcb t0) slot cap badge h0 hL hB
      · refine h.2 v.toObjId (.tcb tcbV) slot cap badge (lookupTcb_some_objects st v tcbV hLookup) ?_ hB
        have hCells : (restoredTcb { tcbV with ntfnPrevCode := np, ntfnNextCode := nn } frame).spaceCells
            = tcbV.spaceCells := by unfold restoredTcb; cases frame <;> rfl
        simpa [KernelObject.slotCap, TCB.spaceSlotCap, hCells] using hL
    | notification _ => simp [KernelObject.slotCap] at hL
    | _ =>
      exact h.2 oid _ slot cap badge
        ((purgedAndRestored_nonNotification st v frame tcbV hInv hLookup
          oid _ (by simp) (by simp)).mp hC) hL hB

theorem purgedAndRestored_allPendingMessagesBounded
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (h : allPendingMessagesBounded st) :
    allPendingMessagesBounded (purgedAndRestored st v frame) := by
  intro tid tcb' msg hTcb' hMsg
  rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup tid.toObjId tcb' hTcb' with
    ⟨_, t0, h0, _, _, rfl⟩ | ⟨hk, t1, ⟨_, _, rfl⟩, rfl⟩
  · exact h tid t0 msg h0 hMsg
  · exact h tid tcbV msg (by rw [hk]; exact lookupTcb_some_objects st v tcbV hLookup)
      (by rw [restoredTcb_eq] at hMsg; exact hMsg)

theorem purgedAndRestored_blockedThreadsPendingMessageConsistent
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (h : blockedThreadsPendingMessageConsistent st) :
    blockedThreadsPendingMessageConsistent (purgedAndRestored st v frame) := by
  intro tid tcb' hTcb'
  rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup tid.toObjId tcb' hTcb' with
    ⟨_, t0, h0, _, _, rfl⟩ | ⟨_, t1, ⟨_, _, rfl⟩, rfl⟩
  · exact h tid t0 h0
  · rw [restoredTcb_eq]
    simp only [TCB.ipcState_setIpcState]

theorem purgedAndRestored_blockedOnReplyHasTarget
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (h : blockedOnReplyHasTarget st) :
    blockedOnReplyHasTarget (purgedAndRestored st v frame) := by
  intro tid tcb' epId rt hTcb' hBlocked
  rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup tid.toObjId tcb' hTcb' with
    ⟨_, t0, h0, _, _, rfl⟩ | ⟨_, t1, ⟨_, _, rfl⟩, rfl⟩
  · exact h tid t0 epId rt h0 hBlocked
  · rw [restoredTcb_ipcState] at hBlocked
    cases hBlocked

theorem purgedAndRestored_donationChainAcyclic
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (h : donationChainAcyclic st) :
    donationChainAcyclic (purgedAndRestored st v frame) := by
  have hBind := purgedAndRestored_sameSchedContextBindings st v frame tcbV hInv hLookup
  intro tid1 tid2 tcb1 tcb2 scId1 scId2 h1 h2 hB1 hB2
  obtain ⟨tc1, hP1, hEq1⟩ := hBind tid1 tcb1 h1
  obtain ⟨tc2, hP2, hEq2⟩ := hBind tid2 tcb2 h2
  exact h tid1 tid2 tc1 tc2 scId1 scId2 hP1 hP2
    (by rw [hEq1]; exact hB1) (by rw [hEq2]; exact hB2)

theorem purgedAndRestored_pendingReceiveReplyWellFormed
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (h : pendingReceiveReplyWellFormed st) :
    pendingReceiveReplyWellFormed (purgedAndRestored st v frame) := by
  have hPull : ∀ (tid : SeLe4n.ThreadId) (tcb' : TCB) (rid : SeLe4n.ReplyId),
      (purgedAndRestored st v frame).getTcb? tid = some tcb' →
      tcb'.pendingReceiveReply = some rid →
      ∃ t0, st.getTcb? tid = some t0 ∧ tcbNtfnLinkRewrite tcb' t0 := by
    intro tid tcb' rid hTcb' hStash
    have hObj : (purgedAndRestored st v frame).objects[tid.toObjId]? = some (.tcb tcb') :=
      (SystemState.getTcb?_eq_some_iff _ tid tcb').mp hTcb'
    rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup tid.toObjId tcb' hObj with
      ⟨_, t0, h0, hR⟩ | ⟨_, t1, ⟨_, _, rfl⟩, rfl⟩
    · exact ⟨t0, (SystemState.getTcb?_eq_some_iff _ tid t0).mpr h0, hR⟩
    · rw [restoredTcb_pendingReceiveReply] at hStash
      cases hStash
  refine ⟨?_, ?_, ?_⟩
  · intro tid tcb' rid hTcb' hStash
    obtain ⟨t0, hP, _, _, rfl⟩ := hPull tid tcb' rid hTcb' hStash
    obtain ⟨hEp, r, hr, hrc⟩ := h.1 tid t0 rid hP hStash
    refine ⟨hEp, r, ?_, hrc⟩
    exact (SystemState.getReply?_eq_some_iff (purgedAndRestored st v frame) rid r).mpr
      ((purgedAndRestored_nonNotification st v frame tcbV hInv hLookup
        rid.toObjId (.reply r) (by simp) (by simp)).mpr
        ((SystemState.getReply?_eq_some_iff st rid r).mp hr))
  · intro tid₁ tid₂ tcb₁ tcb₂ rid h1 h2 hs1 hs2
    obtain ⟨u1, hP1, _, _, rfl⟩ := hPull tid₁ tcb₁ rid h1 hs1
    obtain ⟨u2, hP2, _, _, rfl⟩ := hPull tid₂ tcb₂ rid h2 hs2
    exact h.2.1 tid₁ tid₂ u1 u2 rid hP1 hP2 hs1 hs2
  · intro tid tcb' rid hTcb' hStash
    obtain ⟨t0, hP, _, _, rfl⟩ := hPull tid tcb' rid hTcb' hStash
    obtain ⟨r, hr, hrc⟩ := h.2.2 tid t0 rid hP hStash
    refine ⟨r, ?_, hrc⟩
    exact (SystemState.getReply?_eq_some_iff (purgedAndRestored st v frame) rid r).mpr
      ((purgedAndRestored_nonNotification st v frame tcbV hInv hLookup
        rid.toObjId (.reply r) (by simp) (by simp)).mpr
        ((SystemState.getReply?_eq_some_iff st rid r).mp hr))

theorem purgedAndRestored_replyCallerLinkage
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hNotReply : ∀ ep rt, tcbV.ipcState ≠ .blockedOnReply ep rt)
    (h : replyCallerLinkage st) :
    replyCallerLinkage (purgedAndRestored st v frame) := by
  have hVObj : st.objects[v.toObjId]? = some (.tcb tcbV) := lookupTcb_some_objects st v tcbV hLookup
  have hUnlinked : tcbV.replyObject = none :=
    replyObject_none_of_not_blockedOnReply st h v tcbV hVObj hNotReply
  have hRep : ∀ (rid : SeLe4n.ReplyId) (r : Reply),
      ((purgedAndRestored st v frame).objects[rid.toObjId]? = some (.reply r)) ↔
        (st.objects[rid.toObjId]? = some (.reply r)) :=
    fun rid r => purgedAndRestored_nonNotification st v frame tcbV hInv hLookup
      rid.toObjId (.reply r) (by simp) (by simp)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro tid tcb' rid hTcb' hRO
    have hPre : ∃ t0, st.objects[tid.toObjId]? = some (.tcb t0) ∧ tcbNtfnLinkRewrite tcb' t0 := by
      rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup tid.toObjId tcb' hTcb' with
        ⟨_, h0⟩ | ⟨hk, t1, ⟨_, _, rfl⟩, hEqT⟩
      · exact h0
      · exfalso
        rw [hEqT, restoredTcb_eq] at hRO
        rw [hUnlinked] at hRO
        cases hRO
    obtain ⟨t0, hPre, _, _, rfl⟩ := hPre
    obtain ⟨r, hr, hrc⟩ := h.1.1 tid t0 rid hPre hRO
    exact ⟨r, (hRep rid r).mpr hr, hrc⟩
  · intro rid r tid hr hrc
    obtain ⟨t0, h0, hRO, ep, rt, hBlk⟩ := h.1.2 rid r tid ((hRep rid r).mp hr) hrc
    have hidv : tid.toObjId ≠ v.toObjId := by
      intro hEq
      rw [hEq, hVObj] at h0
      have hx : t0 = tcbV := (KernelObject.tcb.inj (Option.some.inj h0)).symm
      rw [hx, hUnlinked] at hRO
      cases hRO
    obtain ⟨tA, hA, _, _, rfl⟩ :=
      purgedAndRestored_tcb_forward st v frame hInv tid.toObjId t0 hidv h0
    exact ⟨_, hA, hRO, ep, rt, hBlk⟩
  · intro tid tcb' ep rt hTcb' hBlk
    rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup tid.toObjId tcb' hTcb' with
      ⟨_, t0, h0, _, _, rfl⟩ | ⟨_, t1, ⟨_, _, rfl⟩, rfl⟩
    · exact h.2 tid t0 ep rt h0 hBlk
    · rw [restoredTcb_ipcState] at hBlk
      cases hBlk

/-- The swept thread bounds no endpoint queue: both boundary conjuncts demand a
blocking state the notification-blocked thread does not have.

**WS-RR RR8.7**: this arm's instance of `notQueueBlocked_bounds_no_endpoint_queue`,
which is where the argument now lives — the reply arm asks the identical question
of a `.blockedOnReply` victim, and the discriminating fact is a parameter there so
that the two cannot answer it differently. -/
theorem purgedAndRestored_victim_off_endpoint_boundaries
    (st : SystemState) (v : SeLe4n.ThreadId) (tcbV : TCB) (nId : SeLe4n.ObjId)
    (hLookup : lookupTcb st v = some tcbV)
    (hBlocked : tcbV.ipcState = .blockedOnNotification nId)
    (hHead : queueHeadBlockedConsistent st) (hTail : endpointQueueTailBlockedConsistent st)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (hEp : st.objects[epId]? = some (.endpoint ep)) :
    ep.sendQ.head ≠ some v ∧ ep.receiveQ.head ≠ some v ∧
    ep.sendQ.tail ≠ some v ∧ ep.receiveQ.tail ≠ some v :=
  notQueueBlocked_bounds_no_endpoint_queue st v tcbV hLookup
    (fun _ h => by rw [hBlocked] at h; cases h)
    (fun _ h => by rw [hBlocked] at h; cases h)
    (fun _ h => by rw [hBlocked] at h; cases h)
    hHead hTail epId ep hEp

theorem purgedAndRestored_queueHeadBlockedConsistent
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB) (nId : SeLe4n.ObjId)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hBlocked : tcbV.ipcState = .blockedOnNotification nId)
    (hHead : queueHeadBlockedConsistent st) (hTail : endpointQueueTailBlockedConsistent st) :
    queueHeadBlockedConsistent (purgedAndRestored st v frame) := by
  intro epId ep hd tcbHd hEp hHd
  have hEp0 : st.objects[epId]? = some (.endpoint ep) :=
    (purgedAndRestored_nonNotification st v frame tcbV hInv hLookup epId (.endpoint ep)
      (by simp) (by simp)).mp hEp
  obtain ⟨hSH, hRH, _, _⟩ := purgedAndRestored_victim_off_endpoint_boundaries st v tcbV nId
    hLookup hBlocked hHead hTail epId ep hEp0
  constructor
  · intro hx
    have hdv : hd.toObjId ≠ v.toObjId := fun hEq =>
      hRH (hx.trans (congrArg some (SeLe4n.ThreadId.toObjId_injective _ _ hEq)))
    rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup hd.toObjId tcbHd hHd with
      ⟨_, t0, h0, _, _, rfl⟩ | ⟨hk, _⟩
    · exact (hHead epId ep hd _ hEp0 h0).1 hx
    · exact absurd hk hdv
  · intro hx
    have hdv : hd.toObjId ≠ v.toObjId := fun hEq =>
      hSH (hx.trans (congrArg some (SeLe4n.ThreadId.toObjId_injective _ _ hEq)))
    rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup hd.toObjId tcbHd hHd with
      ⟨_, t0, h0, _, _, rfl⟩ | ⟨hk, _⟩
    · exact (hHead epId ep hd _ hEp0 h0).2 hx
    · exact absurd hk hdv

theorem purgedAndRestored_endpointQueueTailBlockedConsistent
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB) (nId : SeLe4n.ObjId)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hBlocked : tcbV.ipcState = .blockedOnNotification nId)
    (hHead : queueHeadBlockedConsistent st) (hTail : endpointQueueTailBlockedConsistent st) :
    endpointQueueTailBlockedConsistent (purgedAndRestored st v frame) := by
  intro epId ep tl tcbTl hEp hTl
  have hEp0 : st.objects[epId]? = some (.endpoint ep) :=
    (purgedAndRestored_nonNotification st v frame tcbV hInv hLookup epId (.endpoint ep)
      (by simp) (by simp)).mp hEp
  obtain ⟨_, _, hST, hRT⟩ := purgedAndRestored_victim_off_endpoint_boundaries st v tcbV nId
    hLookup hBlocked hHead hTail epId ep hEp0
  constructor
  · intro hx
    have htv : tl.toObjId ≠ v.toObjId := fun hEq =>
      hRT (hx.trans (congrArg some (SeLe4n.ThreadId.toObjId_injective _ _ hEq)))
    rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup tl.toObjId tcbTl hTl with
      ⟨_, t0, h0, _, _, rfl⟩ | ⟨hk, _⟩
    · exact (hTail epId ep tl _ hEp0 h0).1 hx
    · exact absurd hk htv
  · intro hx
    have htv : tl.toObjId ≠ v.toObjId := fun hEq =>
      hST (hx.trans (congrArg some (SeLe4n.ThreadId.toObjId_injective _ _ hEq)))
    rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup tl.toObjId tcbTl hTl with
      ⟨_, t0, h0, _, _, rfl⟩ | ⟨hk, _⟩
    · exact (hTail epId ep tl _ hEp0 h0).2 hx
    · exact absurd hk htv

/-- No `queueNext` edge in the composite touches the swept thread: it points at
nothing (the restore cleared its link) and nothing points at it (link integrity
would give it a `queuePrev`, which the hypothesis denies). -/
theorem purgedAndRestored_edge_avoids_victim
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hLink : tcbQueueLinkIntegrity st) (hOff : sweptThreadOffQueueChains st v)
    (a b : SeLe4n.ThreadId) (tcbA : TCB)
    (hA : (purgedAndRestored st v frame).objects[a.toObjId]? = some (.tcb tcbA))
    (hNext : tcbA.queueNext = some b) :
    a.toObjId ≠ v.toObjId ∧ b.toObjId ≠ v.toObjId := by
  obtain ⟨hp, hn⟩ := hOff tcbV hLookup
  have hav : a.toObjId ≠ v.toObjId := by
    intro hEq
    obtain ⟨t1, -, hV⟩ := purgedAndRestored_victim_tcb st v frame tcbV hInv hLookup
    rw [hEq, hV] at hA
    have hx : tcbA = restoredTcb t1 frame := (KernelObject.tcb.inj (Option.some.inj hA)).symm
    rw [hx, restoredTcb_queueNext] at hNext
    cases hNext
  refine ⟨hav, ?_⟩
  intro hEq
  obtain ⟨t0, h0, _, hnA⟩ :=
    purgedAndRestored_tcb_links st v frame tcbV hInv hLookup hOff a.toObjId tcbA hA
  obtain ⟨tB, hB, hpB⟩ := hLink.1 a t0 h0 b (by rw [← hnA]; exact hNext)
  rw [hEq, lookupTcb_some_objects st v tcbV hLookup] at hB
  have hy : tB = tcbV := (KernelObject.tcb.inj (Option.some.inj hB)).symm
  rw [hy, hp] at hpB
  cases hpB

theorem purgedAndRestored_queueNextTargetBlocked
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hLink : tcbQueueLinkIntegrity st) (hOff : sweptThreadOffQueueChains st v)
    (hTgt : queueNextTargetBlocked st) :
    queueNextTargetBlocked (purgedAndRestored st v frame) := by
  intro a b tcbA tcbB hA hB hNext
  obtain ⟨hav, hbv⟩ := purgedAndRestored_edge_avoids_victim st v frame tcbV hInv hLookup hLink
    hOff a b tcbA hA hNext
  rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup a.toObjId tcbA hA with
    ⟨_, t0a, h0a, _, _, rfl⟩ | ⟨hk, _⟩
  · rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup b.toObjId tcbB hB with
      ⟨_, t0b, h0b, _, _, rfl⟩ | ⟨hk, _⟩
    · exact hTgt a b t0a t0b h0a h0b hNext
    · exact absurd hk hbv
  · exact absurd hk hav

/-- WS-ZA ZA5.4 part 27: the purge keeps every thread with a queue successor
blocked on an endpoint — a post-state edge avoids the victim, so its source is a
pre-state thread with its IPC state unchanged. -/
theorem purgedAndRestored_endpointQueueLinksOnlyBlocked
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hLink : tcbQueueLinkIntegrity st) (hOff : sweptThreadOffQueueChains st v)
    (hTgt : endpointQueueLinksOnlyBlocked st) :
    endpointQueueLinksOnlyBlocked (purgedAndRestored st v frame) := by
  intro a tcbA hA hNext
  cases hNb : tcbA.queueNext with
  | none => exact absurd hNb hNext
  | some b =>
  obtain ⟨hav, -⟩ := purgedAndRestored_edge_avoids_victim st v frame tcbV hInv hLookup hLink
    hOff a b tcbA hA hNb
  rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup a.toObjId tcbA hA with
    ⟨_, t0a, h0a, _, _, rfl⟩ | ⟨hk, _⟩
  · exact hTgt a t0a h0a hNext
  · exact absurd hk hav

theorem purgedAndRestored_queueNextBlockingConsistent
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hLink : tcbQueueLinkIntegrity st) (hOff : sweptThreadOffQueueChains st v)
    (hQNB : queueNextBlockingConsistent st) :
    queueNextBlockingConsistent (purgedAndRestored st v frame) := by
  intro a b tcbA tcbB hA hB hNext
  obtain ⟨hav, hbv⟩ := purgedAndRestored_edge_avoids_victim st v frame tcbV hInv hLookup hLink
    hOff a b tcbA hA hNext
  rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup a.toObjId tcbA hA with
    ⟨_, t0a, h0a, _, _, rfl⟩ | ⟨hk, _⟩
  · rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup b.toObjId tcbB hB with
      ⟨_, t0b, h0b, _, _, rfl⟩ | ⟨hk, _⟩
    · exact hQNB a b t0a t0b h0a h0b hNext
    · exact absurd hk hbv
  · exact absurd hk hav

theorem purgedAndRestored_endpointQueueNoDup
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hLink : tcbQueueLinkIntegrity st) (hOff : sweptThreadOffQueueChains st v)
    (hNoDup : endpointQueueNoDup st) :
    endpointQueueNoDup (purgedAndRestored st v frame) := by
  intro oid ep hEp
  have hEp0 : st.objects[oid]? = some (.endpoint ep) :=
    (purgedAndRestored_nonNotification st v frame tcbV hInv hLookup oid (.endpoint ep)
      (by simp) (by simp)).mp hEp
  refine ⟨?_, (hNoDup oid ep hEp0).2⟩
  intro tid tcb hTcb hSelf
  obtain ⟨hav, _⟩ := purgedAndRestored_edge_avoids_victim st v frame tcbV hInv hLookup hLink
    hOff tid tid tcb hTcb hSelf
  rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup tid.toObjId tcb hTcb with
    ⟨_, t0, h0, _, _, rfl⟩ | ⟨hk, _⟩
  · exact (hNoDup oid ep hEp0).1 tid _ h0 hSelf
  · exact absurd hk hav

theorem purgedAndRestored_ipcStateQueueMembershipConsistent
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hOff : sweptThreadOffQueueChains st v)
    (hMem : ipcStateQueueMembershipConsistent st) :
    ipcStateQueueMembershipConsistent (purgedAndRestored st v frame) := by
  obtain ⟨_, hvn⟩ := hOff tcbV hLookup
  intro tid tcb' hTcb'
  rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup tid.toObjId tcb' hTcb' with
    ⟨_, t0, h0, _, _, rfl⟩ | ⟨_, t1, ⟨_, _, rfl⟩, rfl⟩
  · have hPre := hMem tid t0 h0
    have hFwd : ∀ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
        st.objects[prev.toObjId]? = some (.tcb prevTcb) → TCB.queueNext prevTcb = some tid →
        ∃ (p : SeLe4n.ThreadId) (pTcb : TCB),
          (purgedAndRestored st v frame).objects[p.toObjId]? = some (.tcb pTcb) ∧
          TCB.queueNext pTcb = some tid := by
      intro prev prevTcb hPrev hPN
      have hpv : prev.toObjId ≠ v.toObjId := by
        intro hEq
        rw [hEq, lookupTcb_some_objects st v tcbV hLookup] at hPrev
        have hx : prevTcb = tcbV := (KernelObject.tcb.inj (Option.some.inj hPrev)).symm
        rw [hx, hvn] at hPN
        cases hPN
      obtain ⟨tA, hA, _, _, rfl⟩ :=
        purgedAndRestored_tcb_forward st v frame hInv prev.toObjId prevTcb hpv hPrev
      exact ⟨prev, _, hA, hPN⟩
    cases hI : t0.ipcState with
    | blockedOnSend epId =>
      rw [hI] at hPre
      obtain ⟨ep, hEp, hW⟩ := hPre
      refine ⟨ep, (purgedAndRestored_nonNotification st v frame tcbV hInv hLookup epId
        (.endpoint ep) (by simp) (by simp)).mpr hEp, ?_⟩
      rcases hW with hHd | ⟨prev, prevTcb, hPrev, hPN⟩
      · exact Or.inl hHd
      · exact Or.inr (hFwd prev prevTcb hPrev hPN)
    | blockedOnCall epId =>
      rw [hI] at hPre
      obtain ⟨ep, hEp, hW⟩ := hPre
      refine ⟨ep, (purgedAndRestored_nonNotification st v frame tcbV hInv hLookup epId
        (.endpoint ep) (by simp) (by simp)).mpr hEp, ?_⟩
      rcases hW with hHd | ⟨prev, prevTcb, hPrev, hPN⟩
      · exact Or.inl hHd
      · exact Or.inr (hFwd prev prevTcb hPrev hPN)
    | blockedOnReceive epId =>
      rw [hI] at hPre
      obtain ⟨ep, hEp, hW⟩ := hPre
      refine ⟨ep, (purgedAndRestored_nonNotification st v frame tcbV hInv hLookup epId
        (.endpoint ep) (by simp) (by simp)).mpr hEp, ?_⟩
      rcases hW with hHd | ⟨prev, prevTcb, hPrev, hPN⟩
      · exact Or.inl hHd
      · exact Or.inr (hFwd prev prevTcb hPrev hPN)
    | _ => trivial
  · rw [restoredTcb_ipcState]
    trivial

-- ============================================================================
-- §7  The keystone, and the live arm it covers
-- ============================================================================

/-- **WS-RR RR7.22 (residual) — the notification arm's keystone**: the
purge-then-restore composite preserves the whole of `ipcInvariantFull`.

One hypothesis beyond the bundle, `hOff`, this arm's one queue-coherence fact.
The operation makes a thread `.ready`, which would falsify
`blockedThreadTimeoutConsistent` for a thread with a timeout budget; a thread
blocked on a notification carries none (the conjunct's own blocked states omit
`.blockedOnNotification`), so the conjunct carries from the pre-state
(`blockedThreadTimeoutConsistent_of_rewrites`) with no budget premise.  `hNotReply` — which the reply-linkage and donation-owner
frames need — is *derived* from the blocking state, not taken. -/
theorem purgedAndRestored_preserves_ipcInvariantFull
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB) (nId : SeLe4n.ObjId)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hBlocked : tcbV.ipcState = .blockedOnNotification nId)
    (hBundle : ipcInvariantFull st)
    (hOff : sweptThreadOffQueueChains st v) :
    ipcInvariantFull (purgedAndRestored st v frame) := by
  obtain ⟨hIpc, hDual, hBnd, hBadge, hBlkMsg, hNoDup, hMem, hQNB, hQHB, hTimeout,
    hDonAcyc, hDonOwner, hDonBudget, hBlkReply, hReplyLink, hStash,
    hDonUnique, hTailBlk, hTgt, hNBR, hLinks⟩ := hBundle
  have hLink : tcbQueueLinkIntegrity st := hDual.2.1
  have hNotReply : ∀ ep rt, tcbV.ipcState ≠ .blockedOnReply ep rt := by
    intro ep rt hEq
    rw [hBlocked] at hEq
    cases hEq
  have hBind := purgedAndRestored_sameSchedContextBindings st v frame tcbV hInv hLookup
  -- The victim carries no budget: it is blocked on a notification, a state the
  -- timeout conjunct does not admit a budget in.
  have hVBudget : tcbV.timeoutBudget = none := by
    cases hb : tcbV.timeoutBudget with
    | none => rfl
    | some sc =>
      have hBlk := (hTimeout v tcbV sc (lookupTcb_some_objects st v tcbV hLookup) hb).2
      simp [hBlocked] at hBlk
  have hTimeout' : blockedThreadTimeoutConsistent (purgedAndRestored st v frame) := by
    refine blockedThreadTimeoutConsistent_of_rewrites hTimeout ?_ ?_
    · intro t tcb' scId hT hB
      rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup t.toObjId tcb' hT with
        ⟨_, t0, h0, _, _, rfl⟩ | ⟨_, t1, ⟨np, nn, rfl⟩, rfl⟩
      · exact ⟨t0, h0, hB, rfl⟩
      · have e : tcbV.timeoutBudget =
            (restoredTcb { tcbV with ntfnPrevCode := np, ntfnNextCode := nn } frame).timeoutBudget := by
          rw [restoredTcb_eq]
        rw [← e, hVBudget] at hB
        cases hB
    · intro o sc hO
      exact ⟨sc, (purgedAndRestored_nonNotification st v frame tcbV hInv hLookup o _
        (by simp) (by simp)).mpr hO⟩
  exact ⟨purgedAndRestored_ipcInvariant st v frame tcbV hInv hLookup hIpc,
    purgedAndRestored_dualQueueSystemInvariant st v frame tcbV hInv hLookup hOff
      (fun k e hE =>
        let o := purgedAndRestored_victim_off_endpoint_boundaries st v tcbV nId hLookup hBlocked
          hQHB hTailBlk k e hE
        ⟨o.1, o.2.1⟩) hDual,
    purgedAndRestored_allPendingMessagesBounded st v frame tcbV hInv hLookup hBnd,
    purgedAndRestored_badgeWellFormed st v frame tcbV hInv hLookup hBadge,
    purgedAndRestored_blockedThreadsPendingMessageConsistent st v frame tcbV hInv hLookup hBlkMsg,
    purgedAndRestored_endpointQueueNoDup st v frame tcbV hInv hLookup hLink hOff hNoDup,
    purgedAndRestored_ipcStateQueueMembershipConsistent st v frame tcbV hInv hLookup hOff hMem,
    purgedAndRestored_queueNextBlockingConsistent st v frame tcbV hInv hLookup hLink hOff hQNB,
    purgedAndRestored_queueHeadBlockedConsistent st v frame tcbV nId hInv hLookup hBlocked
      hQHB hTailBlk,
    hTimeout',
    purgedAndRestored_donationChainAcyclic st v frame tcbV hInv hLookup hDonAcyc,
    donationOwnerValid_of_frames hBind
      (purgedAndRestored_donationOwnerFrame st v frame tcbV hInv hLookup hNotReply) hDonOwner,
    donationBudgetTransfer_of_sameSchedContextBindings hBind hDonBudget,
    purgedAndRestored_blockedOnReplyHasTarget st v frame tcbV hInv hLookup hBlkReply,
    purgedAndRestored_replyCallerLinkage st v frame tcbV hInv hLookup hNotReply hReplyLink,
    purgedAndRestored_pendingReceiveReplyWellFormed st v frame tcbV hInv hLookup hStash,
    donationOwnerUnique_of_sameSchedContextBindings hBind hDonUnique,
    purgedAndRestored_endpointQueueTailBlockedConsistent st v frame tcbV nId hInv hLookup
      hBlocked hQHB hTailBlk,
    purgedAndRestored_queueNextTargetBlocked st v frame tcbV hInv hLookup hLink hOff hTgt,
    notificationBindingReciprocal.of_codes
      (purgedAndRestored_sameNotificationBindings st v frame tcbV hInv hLookup) hNBR,
    purgedAndRestored_endpointQueueLinksOnlyBlocked st v frame tcbV hInv hLookup hLink hOff
      hLinks⟩

/-- The cancellation's notification arm **is** the purge-then-restore composite —
`rfl` up to the branch, so the two cannot drift. -/
theorem cancelIpcBlocking_notification_arm_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (nId : SeLe4n.ObjId) (hBlocked : tcb.ipcState = .blockedOnNotification nId) :
    Lifecycle.Suspend.cancelIpcBlocking st tid tcb =
      purgedAndRestored st tid (some Architecture.cancelledIpcFrame) := by
  unfold Lifecycle.Suspend.cancelIpcBlocking purgedAndRestored
  rw [hBlocked]
  rfl

/-- **WS-OD OD3.5, WS-ZA ZA4.4: the notification arm's write set** is the victim,
the notification it waits on, and the victim's two notification-queue
neighbours, whose links the unlink closes over the gap (seL4's
`tcbEPDequeue`).  Every other slot reads as the pre-state's **verbatim**, which
is what licenses the arm-selected cancellation footprint
(`cancelArmSpliceNeighbors?`) to declare exactly those two neighbours' TCB
locks on this arm and no endpoint-queue neighbour. -/
theorem cancelIpcBlocking_notificationArm_objects_off (st : SystemState)
    (v : SeLe4n.ThreadId) (tcbV : TCB) (nId : SeLe4n.ObjId)
    (hInv : st.objects.invExt) (hLookup : st.getTcb? v = some tcbV)
    (hBlocked : tcbV.ipcState = .blockedOnNotification nId)
    (k : SeLe4n.ObjId) (hNe : k ≠ v.toObjId) (hNtfn : k ≠ nId)
    (hP : ∀ p, tcbV.ntfnPrev = some p → p.toObjId ≠ k)
    (hN : ∀ n, tcbV.ntfnNext = some n → n.toObjId ≠ k) :
    (Lifecycle.Suspend.cancelIpcBlocking st v tcbV).objects[k]? = st.objects[k]? := by
  rw [cancelIpcBlocking_notification_arm_eq st v tcbV nId hBlocked]
  unfold purgedAndRestored
  rw [restoreToReadyStaging_objects_ne _ v _ k
    (removeFromNotificationWaitQueue_preserves_objects_invExt st v hInv) hNe]
  exact removeFromNotificationWaitQueue_objects_off st v hInv tcbV hLookup k
    (fun oid h => by rw [hBlocked] at h; cases h; exact fun h' => hNtfn h'.symm)
    (fun _ _ h' => hNe h'.symm) hP hN

/-- **WS-RR RR7.22 (residual)**: the cancellation's notification arm preserves
`ipcInvariantFull`. -/
theorem cancelIpcBlocking_notificationArm_preserves_ipcInvariantFull
    (st : SystemState) (v : SeLe4n.ThreadId) (tcbV : TCB) (nId : SeLe4n.ObjId)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hBlocked : tcbV.ipcState = .blockedOnNotification nId)
    (hBundle : ipcInvariantFull st)
    (hOff : sweptThreadOffQueueChains st v) :
    ipcInvariantFull (Lifecycle.Suspend.cancelIpcBlocking st v tcbV) := by
  rw [cancelIpcBlocking_notification_arm_eq st v tcbV nId hBlocked]
  exact purgedAndRestored_preserves_ipcInvariantFull st v _ tcbV nId hInv hLookup hBlocked
    hBundle hOff

end SeLe4n.Kernel
