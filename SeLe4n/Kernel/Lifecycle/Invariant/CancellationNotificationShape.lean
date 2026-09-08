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
`restoreToReadyCancelled (removeFromAllNotificationWaitLists st v) v`.  It is the
second of the operation's three sweeping arms, and it needs its own engine for
the same reason the endpoint arm did: the purge is a fold over the whole object
store, not a splice, so no result about either of the other arms applies to it.

## What is easier here, and what is harder

**Easier**: the purge writes *only notifications*.  Away from the swept thread
every TCB survives verbatim — there is no splice, so no neighbour is relinked —
which is why this module's pullback is an equality where the endpoint arm's is a
record rewrite, and why acyclicity transports path-for-path rather than by an
argument about what the operation added.  `ipcInvariant` itself was already
proved of the purge (`removeFromAllNotificationWaitLists_preserves_ipcInvariant`);
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

/-- The purge writes only notifications, so a non-notification reading is the
input's, in both directions. -/
theorem removeFromAllNotificationWaitLists_nonNotification (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (k : SeLe4n.ObjId) (o : KernelObject) (hNotN : ∀ n, o ≠ .notification n) :
    ((removeFromAllNotificationWaitLists st tid).objects[k]? = some o) ↔
      (st.objects[k]? = some o) := by
  rw [removeFromAllNotificationWaitLists_eq_fold]
  exact (RHTable.fold_preserves_of_lookup st.objects st (notificationPurgeBody tid)
    (fun acc => acc.objects.invExt ∧ (acc.objects[k]? = some o ↔ st.objects[k]? = some o))
    hInv ⟨hInv, Iff.rfl⟩
    (by
      rintro acc k' v' hGet ⟨hE, hA⟩
      unfold notificationPurgeBody
      cases v' with
      | notification n =>
        simp only
        split
        · refine ⟨RHTable.insert_preserves_invExt _ _ _ hE, ?_⟩
          by_cases hK : k' = k
          · subst hK
            constructor
            · intro hx
              have hx' : (acc.objects.insert k' _).get? k' = some o := hx
              rw [RHTable.getElem?_insert_self acc.objects k' _ hE] at hx'
              exact absurd (Option.some.inj hx').symm (hNotN _)
            · intro hx
              have hx2 : st.objects.get? k' = some o := hx
              rw [hGet] at hx2
              exact absurd (Option.some.inj hx2).symm (hNotN n)
          · constructor
            · intro hx
              have hx' : (acc.objects.insert k' _).get? k = some o := hx
              rw [RHTable.getElem?_insert_ne acc.objects k' k _ (by simpa using hK) hE] at hx'
              exact hA.mp hx'
            · intro hx
              show (acc.objects.insert k' _).get? k = some o
              rw [RHTable.getElem?_insert_ne acc.objects k' k _ (by simpa using hK) hE]
              exact hA.mpr hx
        · exact ⟨hE, hA⟩
      | _ => exact ⟨hE, hA⟩)).2

/-- A notification reading after the purge came from one at the same key, with
its `pendingBadge` untouched — the filter rewrites only the wait list and the
state derived from it. -/
theorem removeFromAllNotificationWaitLists_notification_badge (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (k : SeLe4n.ObjId) (n : Notification)
    (h : (removeFromAllNotificationWaitLists st tid).objects[k]? = some (.notification n)) :
    ∃ n0, st.objects[k]? = some (.notification n0) ∧ n.pendingBadge = n0.pendingBadge := by
  rw [removeFromAllNotificationWaitLists_eq_fold] at h
  refine ((RHTable.fold_preserves_of_lookup st.objects st (notificationPurgeBody tid)
    (fun acc => acc.objects.invExt ∧ ∀ m, acc.objects[k]? = some (.notification m) →
      ∃ m0, st.objects[k]? = some (.notification m0) ∧ m.pendingBadge = m0.pendingBadge)
    hInv ⟨hInv, fun m hm => ⟨m, hm, rfl⟩⟩ ?_).2 n h)
  rintro acc k' v' hGet ⟨hE, hA⟩
  unfold notificationPurgeBody
  cases v' with
  | notification n' =>
    simp only
    split
    · refine ⟨RHTable.insert_preserves_invExt _ _ _ hE, ?_⟩
      intro m hm
      by_cases hK : k' = k
      · subst hK
        have hm' : (acc.objects.insert k' _).get? k' = some (KernelObject.notification m) := hm
        rw [RHTable.getElem?_insert_self acc.objects k' _ hE] at hm'
        have hx := KernelObject.notification.inj (Option.some.inj hm')
        exact ⟨n', hGet, by rw [← hx]⟩
      · have hm' : (acc.objects.insert k' _).get? k = some (KernelObject.notification m) := hm
        rw [RHTable.getElem?_insert_ne acc.objects k' k _ (by simpa using hK) hE] at hm'
        exact hA m hm'
    · exact ⟨hE, hA⟩
  | _ => exact ⟨hE, hA⟩

-- ============================================================================
-- §2  The purge-then-restore composite
-- ============================================================================

def purgedAndRestored (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) : SystemState :=
  Lifecycle.Suspend.restoreToReadyStaging (removeFromAllNotificationWaitLists st v) v frame

/-- Away from the swept thread, the composite's TCB readings are the pre-state's
**verbatim** — the purge writes only notifications and the restore only the swept
thread.  This is where the notification arm is simpler than the endpoint one:
there is no splice, so no neighbour is relinked. -/
theorem purgedAndRestored_tcb_iff (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame)
    (hInv : st.objects.invExt) (k : SeLe4n.ObjId) (t : TCB) (hNe : k ≠ v.toObjId) :
    ((purgedAndRestored st v frame).objects[k]? = some (.tcb t)) ↔
      (st.objects[k]? = some (.tcb t)) := by
  have hExt : (removeFromAllNotificationWaitLists st v).objects.invExt :=
    removeFromAllNotificationWaitLists_preserves_objects_invExt st v hInv
  unfold purgedAndRestored
  rw [restoreToReadyStaging_objects_ne _ v frame k hExt hNe]
  exact removeFromAllNotificationWaitLists_nonNotification st v hInv k (.tcb t) (by simp)

/-- At the swept thread, the composite holds the restored TCB. -/
theorem purgedAndRestored_victim_tcb (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV) :
    (purgedAndRestored st v frame).objects[v.toObjId]? = some (.tcb (restoredTcb tcbV frame)) := by
  have hExt : (removeFromAllNotificationWaitLists st v).objects.invExt :=
    removeFromAllNotificationWaitLists_preserves_objects_invExt st v hInv
  have h1 : (removeFromAllNotificationWaitLists st v).objects[v.toObjId]? = some (.tcb tcbV) :=
    (removeFromAllNotificationWaitLists_nonNotification st v hInv v.toObjId (.tcb tcbV)
      (by simp)).mpr (lookupTcb_some_objects st v tcbV hLookup)
  exact restoreToReadyStaging_objects_self _ v frame tcbV hExt
    ((SystemState.getTcb?_eq_some_iff _ v tcbV).mpr h1)

/-- Objects that are neither notifications nor the swept thread's TCB are
untouched. -/
theorem purgedAndRestored_nonNotification (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (k : SeLe4n.ObjId) (o : KernelObject)
    (hNotN : ∀ n, o ≠ .notification n) (hNotTcb : ∀ t, o ≠ .tcb t) :
    ((purgedAndRestored st v frame).objects[k]? = some o) ↔ (st.objects[k]? = some o) := by
  have hExt : (removeFromAllNotificationWaitLists st v).objects.invExt :=
    removeFromAllNotificationWaitLists_preserves_objects_invExt st v hInv
  by_cases hkv : k = v.toObjId
  · subst hkv
    constructor
    · intro hx
      rw [purgedAndRestored_victim_tcb st v frame tcbV hInv hLookup] at hx
      exact absurd (Option.some.inj hx).symm (hNotTcb _)
    · intro hx
      rw [lookupTcb_some_objects st v tcbV hLookup] at hx
      exact absurd (Option.some.inj hx).symm (hNotTcb tcbV)
  · unfold purgedAndRestored
    rw [restoreToReadyStaging_objects_ne _ v frame k hExt hkv]
    exact removeFromAllNotificationWaitLists_nonNotification st v hInv k o hNotN

/-- A notification reading after the composite has the pre-state's badge. -/
theorem purgedAndRestored_notification_badge (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (k : SeLe4n.ObjId) (n : Notification)
    (h : (purgedAndRestored st v frame).objects[k]? = some (.notification n)) :
    ∃ n0, st.objects[k]? = some (.notification n0) ∧ n.pendingBadge = n0.pendingBadge := by
  have hExt : (removeFromAllNotificationWaitLists st v).objects.invExt :=
    removeFromAllNotificationWaitLists_preserves_objects_invExt st v hInv
  have hkv : k ≠ v.toObjId := by
    intro hEq
    rw [hEq, purgedAndRestored_victim_tcb st v frame tcbV hInv hLookup] at h
    cases h
  unfold purgedAndRestored at h
  rw [restoreToReadyStaging_objects_ne _ v frame k hExt hkv] at h
  exact removeFromAllNotificationWaitLists_notification_badge st v hInv k n h

/-- The composite touches no scheduler state. -/
theorem purgedAndRestored_scheduler_eq (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) :
    (purgedAndRestored st v frame).scheduler = st.scheduler := by
  unfold purgedAndRestored
  rw [Lifecycle.Suspend.restoreToReadyStaging_scheduler_eq,
    removeFromAllNotificationWaitLists_scheduler_eq]

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
**verbatim**, at the swept thread the restored one. -/
theorem purgedAndRestored_tcb_pullback (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (k : SeLe4n.ObjId) (tA : TCB)
    (h : (purgedAndRestored st v frame).objects[k]? = some (.tcb tA)) :
    (k ≠ v.toObjId ∧ st.objects[k]? = some (.tcb tA)) ∨
      (k = v.toObjId ∧ tA = restoredTcb tcbV frame) := by
  by_cases hk : k = v.toObjId
  · subst hk
    rw [purgedAndRestored_victim_tcb st v frame tcbV hInv hLookup] at h
    exact Or.inr ⟨rfl, (KernelObject.tcb.inj (Option.some.inj h)).symm⟩
  · exact Or.inl ⟨hk, (purgedAndRestored_tcb_iff st v frame hInv k tA hk).mp h⟩

/-- The composite's TCB, read forwards away from the swept thread. -/
theorem purgedAndRestored_tcb_forward (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame)
    (hInv : st.objects.invExt) (k : SeLe4n.ObjId) (t0 : TCB) (hkv : k ≠ v.toObjId)
    (h : st.objects[k]? = some (.tcb t0)) :
    (purgedAndRestored st v frame).objects[k]? = some (.tcb t0) :=
  (purgedAndRestored_tcb_iff st v frame hInv k t0 hkv).mpr h

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
    ⟨_, h0⟩ | ⟨hk, rfl⟩
  · exact ⟨tA, h0, rfl, rfl⟩
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
    exact ⟨restoredTcb tcbV frame, purgedAndRestored_victim_tcb st v frame tcbV hInv hLookup,
      by rw [restoredTcb_queuePrev, hx, hp], by rw [restoredTcb_queueNext, hx, hn]⟩
  · exact ⟨t0, purgedAndRestored_tcb_forward st v frame hInv k t0 hk h, rfl, rfl⟩

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
    (hDual : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant (purgedAndRestored st v frame) := by
  obtain ⟨hEps, hLink, hAcyc⟩ := hDual
  have hEpIff : ∀ (k : SeLe4n.ObjId) (ep : Endpoint),
      ((purgedAndRestored st v frame).objects[k]? = some (.endpoint ep)) ↔
        (st.objects[k]? = some (.endpoint ep)) :=
    fun k ep => purgedAndRestored_nonNotification st v frame tcbV hInv hLookup k (.endpoint ep)
      (by simp) (by simp)
  have hWF : ∀ (q : IntrusiveQueue), intrusiveQueueWellFormed q st →
      intrusiveQueueWellFormed q (purgedAndRestored st v frame) := by
    intro q hq
    refine ⟨hq.1, ?_, ?_⟩
    · intro hd hHd
      obtain ⟨t0, h0, hp⟩ := hq.2.1 hd hHd
      obtain ⟨tA, hA, hpA, _⟩ :=
        purgedAndRestored_tcb_links_forward st v frame tcbV hInv hLookup hOff hd.toObjId t0 h0
      exact ⟨tA, hA, by rw [hpA]; exact hp⟩
    · intro tl hTl
      obtain ⟨t0, h0, hn⟩ := hq.2.2 tl hTl
      obtain ⟨tA, hA, _, hnA⟩ :=
        purgedAndRestored_tcb_links_forward st v frame tcbV hInv hLookup hOff tl.toObjId t0 h0
      exact ⟨tA, hA, by rw [hnA]; exact hn⟩
  refine ⟨?_, ?_, ?_⟩
  · intro epId ep hEp
    have hEp0 : st.objects[epId]? = some (.endpoint ep) := (hEpIff epId ep).mp hEp
    have h0 := hEps epId ep hEp0
    unfold dualQueueEndpointWellFormed at h0 ⊢
    rw [hEp0] at h0
    rw [hEp]
    exact ⟨hWF ep.sendQ h0.1, hWF ep.receiveQ h0.2⟩
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
    ⟨_, h0⟩ | ⟨hk, rfl⟩
  · exact ⟨tcb', h0, rfl⟩
  · exact ⟨tcbV, by rw [hk]; exact lookupTcb_some_objects st v tcbV hLookup,
      by rw [restoredTcb_eq]⟩

theorem purgedAndRestored_timeoutBudgetFrame
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV) :
    timeoutBudgetFrame st (purgedAndRestored st v frame) := by
  intro tid tcb' hTcb'
  rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup tid.toObjId tcb' hTcb' with
    ⟨_, h0⟩ | ⟨hk, rfl⟩
  · exact ⟨tcb', h0, rfl⟩
  · exact ⟨tcbV, by rw [hk]; exact lookupTcb_some_objects st v tcbV hLookup,
      by rw [restoredTcb_eq]⟩

theorem purgedAndRestored_passiveServerIdleFrame
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV) :
    passiveServerIdleFrame st (purgedAndRestored st v frame) := by
  have hSched := purgedAndRestored_scheduler_eq st v frame
  refine ⟨fun tid tcb' hTcb' hUnbound hNotQ hNotCur hNA => ?_⟩
  rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup tid.toObjId tcb' hTcb' with
    ⟨_, h0⟩ | ⟨_, rfl⟩
  · exact ⟨tcb', h0, hUnbound, by rw [hSched] at hNotQ; exact hNotQ,
      by rw [hSched] at hNotCur; exact hNotCur, rfl⟩
  · exact absurd (by rw [restoredTcb_ipcState]; exact Or.inl rfl) hNA

theorem purgedAndRestored_donationOwnerFrame
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hNotReply : ∀ ep rt, tcbV.ipcState ≠ .blockedOnReply ep rt) :
    donationOwnerFrame st (purgedAndRestored st v frame) := by
  have hVObj : st.objects[v.toObjId]? = some (.tcb tcbV) := lookupTcb_some_objects st v tcbV hLookup
  refine ⟨?_, ?_⟩
  · intro scId sc hsc
    exact (purgedAndRestored_nonNotification st v frame tcbV hInv hLookup
      scId.toObjId (.schedContext sc) (by simp) (by simp)).mpr hsc
  · intro owner ownerTcb hOwner hUnbound hBlocked
    have hne : owner.toObjId ≠ v.toObjId := by
      intro hEq
      rw [hEq, hVObj] at hOwner
      have hx : ownerTcb = tcbV := (KernelObject.tcb.inj (Option.some.inj hOwner)).symm
      obtain ⟨ep, rt, hb⟩ := hBlocked
      rw [hx] at hb
      exact hNotReply ep rt hb
    exact ⟨ownerTcb, purgedAndRestored_tcb_forward st v frame hInv owner.toObjId ownerTcb hne hOwner,
      hUnbound, hBlocked⟩

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
      ⟨_, h0⟩ | ⟨hk, rfl⟩
    · exact ⟨tcb', h0, rfl⟩
    · exact ⟨tcbV, by rw [hk]; exact hVObj, by rw [restoredTcb_eq]⟩
  · intro tid tcb rid hTcb hRO
    have hne : tid.toObjId ≠ v.toObjId := by
      intro hEq
      rw [hEq, hVObj] at hTcb
      have hx : tcb = tcbV := (KernelObject.tcb.inj (Option.some.inj hTcb)).symm
      rw [hx, hUnlinked] at hRO
      cases hRO
    exact ⟨tcb, purgedAndRestored_tcb_forward st v frame hInv tid.toObjId tcb hne hTcb, rfl,
      fun ep rt hb => ⟨ep, rt, hb⟩⟩

-- ============================================================================
-- §6  The conjuncts of `ipcInvariantFull`, one at a time
-- ============================================================================

theorem purgedAndRestored_ipcInvariant
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (h : ipcInvariant st) : ipcInvariant (purgedAndRestored st v frame) := by
  have hExt : (removeFromAllNotificationWaitLists st v).objects.invExt :=
    removeFromAllNotificationWaitLists_preserves_objects_invExt st v hInv
  intro oid ntfn hN
  have hkv : oid ≠ v.toObjId := by
    intro hEq
    rw [hEq, purgedAndRestored_victim_tcb st v frame tcbV hInv hLookup] at hN
    cases hN
  unfold purgedAndRestored at hN
  rw [restoreToReadyStaging_objects_ne _ v frame oid hExt hkv] at hN
  exact removeFromAllNotificationWaitLists_preserves_ipcInvariant st v hInv h oid ntfn hN

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
  · intro oid cn slot cap badge hC hL hB
    exact h.2 oid cn slot cap badge
      ((purgedAndRestored_nonNotification st v frame tcbV hInv hLookup
        oid (.cnode cn) (by simp) (by simp)).mp hC) hL hB

theorem purgedAndRestored_allPendingMessagesBounded
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (h : allPendingMessagesBounded st) :
    allPendingMessagesBounded (purgedAndRestored st v frame) := by
  intro tid tcb' msg hTcb' hMsg
  rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup tid.toObjId tcb' hTcb' with
    ⟨_, h0⟩ | ⟨hk, rfl⟩
  · exact h tid tcb' msg h0 hMsg
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
    ⟨_, h0⟩ | ⟨_, rfl⟩
  · exact h tid tcb' h0
  · rw [restoredTcb_eq]
    simp only

theorem purgedAndRestored_blockedOnReplyHasTarget
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (h : blockedOnReplyHasTarget st) :
    blockedOnReplyHasTarget (purgedAndRestored st v frame) := by
  intro tid tcb' epId rt hTcb' hBlocked
  rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup tid.toObjId tcb' hTcb' with
    ⟨_, h0⟩ | ⟨_, rfl⟩
  · exact h tid tcb' epId rt h0 hBlocked
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
      st.getTcb? tid = some tcb' := by
    intro tid tcb' rid hTcb' hStash
    have hObj : (purgedAndRestored st v frame).objects[tid.toObjId]? = some (.tcb tcb') :=
      (SystemState.getTcb?_eq_some_iff _ tid tcb').mp hTcb'
    rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup tid.toObjId tcb' hObj with
      ⟨_, h0⟩ | ⟨_, rfl⟩
    · exact (SystemState.getTcb?_eq_some_iff _ tid tcb').mpr h0
    · rw [restoredTcb_pendingReceiveReply] at hStash
      cases hStash
  refine ⟨?_, ?_⟩
  · intro tid tcb' rid hTcb' hStash
    obtain ⟨hEp, r, hr, hrc⟩ := h.1 tid tcb' rid (hPull tid tcb' rid hTcb' hStash) hStash
    refine ⟨hEp, r, ?_, hrc⟩
    exact (SystemState.getReply?_eq_some_iff (purgedAndRestored st v frame) rid r).mpr
      ((purgedAndRestored_nonNotification st v frame tcbV hInv hLookup
        rid.toObjId (.reply r) (by simp) (by simp)).mpr
        ((SystemState.getReply?_eq_some_iff st rid r).mp hr))
  · intro tid₁ tid₂ tcb₁ tcb₂ rid h1 h2 hs1 hs2
    exact h.2 tid₁ tid₂ tcb₁ tcb₂ rid (hPull tid₁ tcb₁ rid h1 hs1) (hPull tid₂ tcb₂ rid h2 hs2)
      hs1 hs2

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
    have hPre : st.objects[tid.toObjId]? = some (.tcb tcb') := by
      rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup tid.toObjId tcb' hTcb' with
        ⟨_, h0⟩ | ⟨hk, hEqT⟩
      · exact h0
      · exfalso
        rw [hEqT, restoredTcb_eq] at hRO
        rw [hUnlinked] at hRO
        cases hRO
    obtain ⟨r, hr, hrc⟩ := h.1.1 tid tcb' rid hPre hRO
    exact ⟨r, (hRep rid r).mpr hr, hrc⟩
  · intro rid r tid hr hrc
    obtain ⟨t0, h0, hRO, ep, rt, hBlk⟩ := h.1.2 rid r tid ((hRep rid r).mp hr) hrc
    have hidv : tid.toObjId ≠ v.toObjId := by
      intro hEq
      rw [hEq, hVObj] at h0
      have hx : t0 = tcbV := (KernelObject.tcb.inj (Option.some.inj h0)).symm
      rw [hx, hUnlinked] at hRO
      cases hRO
    exact ⟨t0, purgedAndRestored_tcb_forward st v frame hInv tid.toObjId t0 hidv h0, hRO,
      ep, rt, hBlk⟩
  · intro tid tcb' ep rt hTcb' hBlk
    rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup tid.toObjId tcb' hTcb' with
      ⟨_, h0⟩ | ⟨_, rfl⟩
    · exact h.2 tid tcb' ep rt h0 hBlk
    · rw [restoredTcb_ipcState] at hBlk
      cases hBlk

/-- The swept thread bounds no endpoint queue: both boundary conjuncts demand a
blocking state the notification-blocked thread does not have. -/
theorem purgedAndRestored_victim_off_endpoint_boundaries
    (st : SystemState) (v : SeLe4n.ThreadId) (tcbV : TCB) (nId : SeLe4n.ObjId)
    (hLookup : lookupTcb st v = some tcbV)
    (hBlocked : tcbV.ipcState = .blockedOnNotification nId)
    (hHead : queueHeadBlockedConsistent st) (hTail : endpointQueueTailBlockedConsistent st)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (hEp : st.objects[epId]? = some (.endpoint ep)) :
    ep.sendQ.head ≠ some v ∧ ep.receiveQ.head ≠ some v ∧
    ep.sendQ.tail ≠ some v ∧ ep.receiveQ.tail ≠ some v := by
  have hVObj : st.objects[v.toObjId]? = some (.tcb tcbV) := lookupTcb_some_objects st v tcbV hLookup
  refine ⟨fun hx => ?_, fun hx => ?_, fun hx => ?_, fun hx => ?_⟩
  · rcases (hHead epId ep v tcbV hEp hVObj).2 hx with h | h <;> rw [hBlocked] at h <;> cases h
  · have h := (hHead epId ep v tcbV hEp hVObj).1 hx
    rw [hBlocked] at h; cases h
  · rcases (hTail epId ep v tcbV hEp hVObj).2 hx with h | h <;> rw [hBlocked] at h <;> cases h
  · have h := (hTail epId ep v tcbV hEp hVObj).1 hx
    rw [hBlocked] at h; cases h

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
      ⟨_, h0⟩ | ⟨hk, _⟩
    · exact (hHead epId ep hd tcbHd hEp0 h0).1 hx
    · exact absurd hk hdv
  · intro hx
    have hdv : hd.toObjId ≠ v.toObjId := fun hEq =>
      hSH (hx.trans (congrArg some (SeLe4n.ThreadId.toObjId_injective _ _ hEq)))
    rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup hd.toObjId tcbHd hHd with
      ⟨_, h0⟩ | ⟨hk, _⟩
    · exact (hHead epId ep hd tcbHd hEp0 h0).2 hx
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
      ⟨_, h0⟩ | ⟨hk, _⟩
    · exact (hTail epId ep tl tcbTl hEp0 h0).1 hx
    · exact absurd hk htv
  · intro hx
    have htv : tl.toObjId ≠ v.toObjId := fun hEq =>
      hST (hx.trans (congrArg some (SeLe4n.ThreadId.toObjId_injective _ _ hEq)))
    rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup tl.toObjId tcbTl hTl with
      ⟨_, h0⟩ | ⟨hk, _⟩
    · exact (hTail epId ep tl tcbTl hEp0 h0).2 hx
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
    rw [hEq, purgedAndRestored_victim_tcb st v frame tcbV hInv hLookup] at hA
    have hx : tcbA = restoredTcb tcbV frame := (KernelObject.tcb.inj (Option.some.inj hA)).symm
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
    ⟨_, h0a⟩ | ⟨hk, _⟩
  · rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup b.toObjId tcbB hB with
      ⟨_, h0b⟩ | ⟨hk, _⟩
    · exact hTgt a b tcbA tcbB h0a h0b hNext
    · exact absurd hk hbv
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
    ⟨_, h0a⟩ | ⟨hk, _⟩
  · rcases purgedAndRestored_tcb_pullback st v frame tcbV hInv hLookup b.toObjId tcbB hB with
      ⟨_, h0b⟩ | ⟨hk, _⟩
    · exact hQNB a b tcbA tcbB h0a h0b hNext
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
    ⟨_, h0⟩ | ⟨hk, _⟩
  · exact (hNoDup oid ep hEp0).1 tid tcb h0 hSelf
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
    ⟨_, h0⟩ | ⟨_, rfl⟩
  · have hPre := hMem tid tcb' h0
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
      exact ⟨prev, prevTcb,
        purgedAndRestored_tcb_forward st v frame hInv prev.toObjId prevTcb hpv hPrev, hPN⟩
    cases hI : tcb'.ipcState with
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

Two hypotheses beyond the bundle.  `hAllBudgetsNone` is the same one the endpoint
arm takes, and for the same reason: the conjunct says a budget-carrying thread is
blocked, and this operation makes one `.ready`.  `hOff` is this arm's one
queue-coherence fact.  `hNotReply` — which the reply-linkage and donation-owner
frames need — is *derived* from the blocking state, not taken. -/
theorem purgedAndRestored_preserves_ipcInvariantFull
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB) (nId : SeLe4n.ObjId)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hBlocked : tcbV.ipcState = .blockedOnNotification nId)
    (hBundle : ipcInvariantFull st)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hOff : sweptThreadOffQueueChains st v) :
    ipcInvariantFull (purgedAndRestored st v frame) := by
  obtain ⟨hIpc, hDual, hBnd, hBadge, hBlkMsg, hNoDup, hMem, hQNB, hQHB, _hTimeout,
    hDonAcyc, hDonOwner, hPassive, hDonBudget, hBlkReply, hReplyLink, hStash,
    hDonUnique, hTailBlk, hTgt⟩ := hBundle
  have hLink : tcbQueueLinkIntegrity st := hDual.2.1
  have hNotReply : ∀ ep rt, tcbV.ipcState ≠ .blockedOnReply ep rt := by
    intro ep rt hEq
    rw [hBlocked] at hEq
    cases hEq
  have hBind := purgedAndRestored_sameSchedContextBindings st v frame tcbV hInv hLookup
  exact ⟨purgedAndRestored_ipcInvariant st v frame tcbV hInv hLookup hIpc,
    purgedAndRestored_dualQueueSystemInvariant st v frame tcbV hInv hLookup hOff hDual,
    purgedAndRestored_allPendingMessagesBounded st v frame tcbV hInv hLookup hBnd,
    purgedAndRestored_badgeWellFormed st v frame tcbV hInv hLookup hBadge,
    purgedAndRestored_blockedThreadsPendingMessageConsistent st v frame tcbV hInv hLookup hBlkMsg,
    purgedAndRestored_endpointQueueNoDup st v frame tcbV hInv hLookup hLink hOff hNoDup,
    purgedAndRestored_ipcStateQueueMembershipConsistent st v frame tcbV hInv hLookup hOff hMem,
    purgedAndRestored_queueNextBlockingConsistent st v frame tcbV hInv hLookup hLink hOff hQNB,
    purgedAndRestored_queueHeadBlockedConsistent st v frame tcbV nId hInv hLookup hBlocked
      hQHB hTailBlk,
    blockedThreadTimeoutConsistent_of_frame
      (purgedAndRestored_timeoutBudgetFrame st v frame tcbV hInv hLookup) hAllBudgetsNone,
    purgedAndRestored_donationChainAcyclic st v frame tcbV hInv hLookup hDonAcyc,
    donationOwnerValid_of_frames hBind
      (purgedAndRestored_donationOwnerFrame st v frame tcbV hInv hLookup hNotReply) hDonOwner,
    passiveServerIdle_of_frame
      (purgedAndRestored_passiveServerIdleFrame st v frame tcbV hInv hLookup) hPassive,
    donationBudgetTransfer_of_sameSchedContextBindings hBind hDonBudget,
    purgedAndRestored_blockedOnReplyHasTarget st v frame tcbV hInv hLookup hBlkReply,
    purgedAndRestored_replyCallerLinkage st v frame tcbV hInv hLookup hNotReply hReplyLink,
    purgedAndRestored_pendingReceiveReplyWellFormed st v frame tcbV hInv hLookup hStash,
    donationOwnerUnique_of_sameSchedContextBindings hBind hDonUnique,
    purgedAndRestored_endpointQueueTailBlockedConsistent st v frame tcbV nId hInv hLookup
      hBlocked hQHB hTailBlk,
    purgedAndRestored_queueNextTargetBlocked st v frame tcbV hInv hLookup hLink hOff hTgt⟩

/-- The cancellation's notification arm **is** the purge-then-restore composite —
`rfl` up to the branch, so the two cannot drift. -/
theorem cancelIpcBlocking_notification_arm_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (nId : SeLe4n.ObjId) (hBlocked : tcb.ipcState = .blockedOnNotification nId) :
    Lifecycle.Suspend.cancelIpcBlocking st tid tcb =
      purgedAndRestored st tid (some Architecture.cancelledIpcFrame) := by
  unfold Lifecycle.Suspend.cancelIpcBlocking purgedAndRestored
  rw [hBlocked]
  rfl

/-- **WS-RR RR7.22 (residual)**: the cancellation's notification arm preserves
`ipcInvariantFull`. -/
theorem cancelIpcBlocking_notificationArm_preserves_ipcInvariantFull
    (st : SystemState) (v : SeLe4n.ThreadId) (tcbV : TCB) (nId : SeLe4n.ObjId)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hBlocked : tcbV.ipcState = .blockedOnNotification nId)
    (hBundle : ipcInvariantFull st)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hOff : sweptThreadOffQueueChains st v) :
    ipcInvariantFull (Lifecycle.Suspend.cancelIpcBlocking st v tcbV) := by
  rw [cancelIpcBlocking_notification_arm_eq st v tcbV nId hBlocked]
  exact purgedAndRestored_preserves_ipcInvariantFull st v _ tcbV nId hInv hLookup hBlocked
    hBundle hAllBudgetsNone hOff

end SeLe4n.Kernel
