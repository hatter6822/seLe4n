/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Invariant.DonationPreservation
import SeLe4n.Kernel.IPC.Invariant.LookupCongruence
import SeLe4n.Kernel.IPC.Operations.CancelAll
import SeLe4n.Kernel.IPC.Invariant.UnheldContextPop

/-!
# A reply-blocked caller's server forgotten keeps the IPC bundle

WS-ZA ZA6.34: a thread's final delete leaves the callers waiting on its replies
reply-blocked with no server recorded (seL4-MCS's `finaliseCap` on a thread:
the callers stay `BlockedOnReply`, each reply's `replyTCB` naming its caller,
and nothing records the deleted server).  The write is one field of one TCB:
the state word set to `4` (`TCB.serverForgotten`), which keeps the caller's
reply block on the same object and drops its reply target.

No conjunct of `ipcInvariantFull` reads a reply block's target: each reads a
reply block as `∃ ep rt, ipcState = .blockedOnReply ep rt`, or not at all.  So
the bundle carries across the write (`ipcInvariantFull_of_serverForgotten`):
the structural conjuncts through the core driver, whose state agreement reads
states with their servers forgotten
(`ipcInvariantCore_of_nonBindingAgreements`), and the rest one by one.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState

/-- **What a server-forgetting write leaves of a thread**: the thread itself, or
the written one with its server forgotten. -/
def serverForgetPair (old tx ty : TCB) : Prop :=
  tx = ty ∨ (ty = old ∧ tx = old.serverForgotten)

namespace serverForgetPair

variable {old tx ty : TCB}

theorem fields (h : serverForgetPair old tx ty) :
    tx.schedContextBinding = ty.schedContextBinding ∧ tx.replyObject = ty.replyObject ∧
    tx.pendingReceiveReply = ty.pendingReceiveReply ∧ tx.queueNext = ty.queueNext ∧
    tx.queuePrev = ty.queuePrev ∧ tx.queuePPrev = ty.queuePPrev ∧
    tx.timeoutBudget = ty.timeoutBudget ∧ tx.pendingMessage = ty.pendingMessage ∧
    tx.boundNotificationCode = ty.boundNotificationCode := by
  rcases h with rfl | ⟨rfl, rfl⟩ <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The states agree once their servers are forgotten. -/
theorem forgotten {e : SeLe4n.ObjId} {r : Option SeLe4n.ThreadId}
    (hB : old.ipcState = .blockedOnReply e r) (h : serverForgetPair old tx ty) :
    tx.ipcState.serverForgotten = ty.ipcState.serverForgotten := by
  rcases h with rfl | ⟨rfl, rfl⟩
  · rfl
  · exact TCB.serverForgotten_ipcState_forgotten hB

/-- A state that is no reply block is read alike on both sides. -/
theorem nonReply {e : SeLe4n.ObjId} {r : Option SeLe4n.ThreadId}
    (hB : old.ipcState = .blockedOnReply e r) (h : serverForgetPair old tx ty)
    {s : ThreadIpcState} (hs : ∀ ep rt, s ≠ .blockedOnReply ep rt) :
    tx.ipcState = s ↔ ty.ipcState = s := by
  rcases h with rfl | ⟨rfl, rfl⟩
  · exact Iff.rfl
  · rw [TCB.serverForgotten_ipcState_of hB, hB]
    exact ⟨fun h => absurd h.symm (hs _ _), fun h => absurd h.symm (hs _ _)⟩

/-- A reply block on either side is a reply block on the other. -/
theorem reply_iff {e : SeLe4n.ObjId} {r : Option SeLe4n.ThreadId}
    (hB : old.ipcState = .blockedOnReply e r) (h : serverForgetPair old tx ty) (ep : SeLe4n.ObjId) :
    (∃ rt, tx.ipcState = .blockedOnReply ep rt) ↔ (∃ rt, ty.ipcState = .blockedOnReply ep rt) := by
  rcases h with rfl | ⟨rfl, rfl⟩
  · exact Iff.rfl
  · rw [TCB.serverForgotten_ipcState_of hB, hB]
    exact ⟨fun ⟨_, h⟩ => ⟨r, by cases h; rfl⟩, fun ⟨_, h⟩ => ⟨none, by cases h; rfl⟩⟩

theorem reply_any {e : SeLe4n.ObjId} {r : Option SeLe4n.ThreadId}
    (hB : old.ipcState = .blockedOnReply e r) (h : serverForgetPair old tx ty) :
    (∃ ep rt, tx.ipcState = .blockedOnReply ep rt) ↔ (∃ ep rt, ty.ipcState = .blockedOnReply ep rt) :=
  ⟨fun ⟨ep, h'⟩ => ⟨ep, (reply_iff hB h ep).mp h'⟩,
   fun ⟨ep, h'⟩ => ⟨ep, (reply_iff hB h ep).mpr h'⟩⟩

theorem endpointQueued {e : SeLe4n.ObjId} {r : Option SeLe4n.ThreadId}
    (hB : old.ipcState = .blockedOnReply e r) (h : serverForgetPair old tx ty) :
    ipcStateEndpointQueued tx.ipcState = ipcStateEndpointQueued ty.ipcState := by
  rcases h with rfl | ⟨rfl, rfl⟩
  · rfl
  · rw [TCB.serverForgotten_ipcState_of hB, hB]; rfl

end serverForgetPair

section
variable {st st' : SystemState} {key : SeLe4n.ObjId} {old : TCB}

private theorem serverForget_back (hPre : st.objects[key]? = some (.tcb old))
    (hAt : st'.objects[key]? = some (.tcb old.serverForgotten))
    (hFrame : ∀ (oid : SeLe4n.ObjId), oid ≠ key → st'.objects[oid]? = st.objects[oid]?)
    {oid : SeLe4n.ObjId} {tx : TCB} (h : st'.objects[oid]? = some (.tcb tx)) :
    ∃ ty, st.objects[oid]? = some (.tcb ty) ∧ serverForgetPair old tx ty := by
  by_cases hEq : oid = key
  · subst hEq; rw [hAt] at h; cases h; exact ⟨old, hPre, Or.inr ⟨rfl, rfl⟩⟩
  · rw [hFrame oid hEq] at h; exact ⟨tx, h, Or.inl rfl⟩

private theorem serverForget_fwd (hPre : st.objects[key]? = some (.tcb old))
    (hAt : st'.objects[key]? = some (.tcb old.serverForgotten))
    (hFrame : ∀ (oid : SeLe4n.ObjId), oid ≠ key → st'.objects[oid]? = st.objects[oid]?)
    {oid : SeLe4n.ObjId} {ty : TCB} (h : st.objects[oid]? = some (.tcb ty)) :
    ∃ tx, st'.objects[oid]? = some (.tcb tx) ∧ serverForgetPair old tx ty := by
  by_cases hEq : oid = key
  · subst hEq; rw [hPre] at h; cases h; exact ⟨_, hAt, Or.inr ⟨rfl, rfl⟩⟩
  · rw [← hFrame oid hEq] at h; exact ⟨ty, h, Or.inl rfl⟩

private theorem serverForget_other (hPre : st.objects[key]? = some (.tcb old))
    (hAt : st'.objects[key]? = some (.tcb old.serverForgotten))
    (hFrame : ∀ (oid : SeLe4n.ObjId), oid ≠ key → st'.objects[oid]? = st.objects[oid]?)
    (oid : SeLe4n.ObjId) (k : KernelObject) (hk : ∀ t, k ≠ .tcb t) :
    st'.objects[oid]? = some k ↔ st.objects[oid]? = some k := by
  by_cases hEq : oid = key
  · subst hEq; rw [hAt, hPre]
    exact ⟨fun h => absurd (Option.some.inj h).symm (hk _),
      fun h => absurd (Option.some.inj h).symm (hk _)⟩
  · rw [hFrame oid hEq]

end

/-- **The IPC bundle carries across one reply-blocked thread's server forgotten**:
a state that rewrites the thread at `key`, blocked on a reply, to the same
thread with its server forgotten (`TCB.serverForgotten`), and leaves every other
object alone.  The structural conjuncts come from the core driver, whose state
agreement reads states with their servers forgotten; every other conjunct reads
a reply block whatever server it records, or reads none. -/
theorem ipcInvariantFull_of_serverForgotten (st st' : SystemState) (key : SeLe4n.ObjId)
    (old : TCB) {e : SeLe4n.ObjId} {r : Option SeLe4n.ThreadId}
    (hInv : ipcInvariantFull st)
    (hPre : st.objects[key]? = some (.tcb old))
    (hAt : st'.objects[key]? = some (.tcb old.serverForgotten))
    (hFrame : ∀ (oid : SeLe4n.ObjId), oid ≠ key → st'.objects[oid]? = st.objects[oid]?)
    (hB : old.ipcState = .blockedOnReply e r) :
    ipcInvariantFull st' := by
  have hBk : ∀ {oid : SeLe4n.ObjId} {tx : TCB}, st'.objects[oid]? = some (.tcb tx) →
      ∃ ty, st.objects[oid]? = some (.tcb ty) ∧ serverForgetPair old tx ty :=
    fun h => serverForget_back hPre hAt hFrame h
  have hFw : ∀ {oid : SeLe4n.ObjId} {ty : TCB}, st.objects[oid]? = some (.tcb ty) →
      ∃ tx, st'.objects[oid]? = some (.tcb tx) ∧ serverForgetPair old tx ty :=
    fun h => serverForget_fwd hPre hAt hFrame h
  have hNT := serverForget_other hPre hAt hFrame
  have hRep : ∀ (rid : SeLe4n.ObjId) (rp : Reply),
      st'.objects[rid]? = some (.reply rp) ↔ st.objects[rid]? = some (.reply rp) :=
    fun rid rp => hNT rid _ (fun _ => by exact KernelObject.noConfusion)
  have hSc : ∀ (oid : SeLe4n.ObjId) (sc : SchedContext),
      st'.objects[oid]? = some (.schedContext sc) ↔ st.objects[oid]? = some (.schedContext sc) :=
    fun oid sc => hNT oid _ (fun _ => by exact KernelObject.noConfusion)
  have hCore : ipcInvariantCore st' := by
    refine ipcInvariantCore_of_nonBindingAgreements st st'
      (ipcInvariantCoreNonDonation_of_exceptDonationOwner
        (ipcInvariantFullExceptDonationOwner_of_full default hInv))
      (fun s k hk _ _ => hNT s k hk) (fun s sc h => ⟨sc, (hSc s sc).mpr h⟩)
      (fun s tx h => ?_) (fun s ty h => ?_) ?_ ?_ ?_ ?_
    · obtain ⟨ty, hy, hp⟩ := hBk h
      obtain ⟨-, -, -, e4, e5, e6, e7, e8, -⟩ := hp.fields
      exact ⟨ty, hy, hp.forgotten hB, by rw [e8]; exact pendingMessageReadAgrees_refl _,
        e4, e5, e6, e7⟩
    · obtain ⟨tx, hx, hp⟩ := hFw h
      obtain ⟨-, -, -, e4, e5, e6, e7, e8, -⟩ := hp.fields
      exact ⟨tx, hx, hp.forgotten hB, by rw [e8]; exact pendingMessageReadAgrees_refl _,
        e4, e5, e6, e7⟩
    · refine badgedSlotsBack.of_slotCap_back fun oid o' h => ?_
      by_cases hEq : oid = key
      · subst hEq; rw [hAt] at h; cases h; exact ⟨_, hPre, rfl⟩
      · rw [hFrame oid hEq] at h; exact ⟨o', h, rfl⟩
    · intro t1 t2 tcb1 tcb2 s1 s2 h1 h2 hB1 hB2
      obtain ⟨y1, hy1, p1⟩ := hBk h1
      obtain ⟨y2, hy2, p2⟩ := hBk h2
      exact hInv.donationChainAcyclic t1 t2 y1 y2 s1 s2 hy1 hy2 (p1.fields.1 ▸ hB1)
        (p2.fields.1 ▸ hB2)
    · intro t tcb s owner hT hBind
      obtain ⟨ty, hy, p⟩ := hBk hT
      obtain ⟨⟨sc, hScAt, hBound⟩, ownerTcb, hOwner, hOwnerUnbound, hOwnerBlk⟩ :=
        hInv.donationOwnerValid t ty s owner hy (p.fields.1 ▸ hBind)
      obtain ⟨ox, hox, po⟩ := hFw hOwner
      exact ⟨⟨sc, (hSc _ sc).mpr hScAt, hBound⟩, ox, hox, po.fields.1.trans hOwnerUnbound,
        (po.reply_any hB).mpr hOwnerBlk⟩
    · intro t1 t2 tcb1 tcb2 s h1 h2 hNe hS1 hS2
      obtain ⟨y1, hy1, p1⟩ := hBk h1
      obtain ⟨y2, hy2, p2⟩ := hBk h2
      exact hInv.donationBudgetTransfer t1 t2 y1 y2 s hy1 hy2 hNe (p1.fields.1 ▸ hS1)
        (p2.fields.1 ▸ hS2)
  refine ipcInvariantFull_of_core_replyCallerLinkage hCore ⟨⟨?_, ?_⟩, ?_⟩ ⟨?_, ?_, ?_⟩ ?_
    ?_ ?_ (.of_codes ?_ hInv.notificationBindingReciprocal) ?_
  -- replyCallerLinkageReciprocal, thread to reply.
  · intro tid tcb rid hT hRO
    obtain ⟨ty, hy, p⟩ := hBk hT
    obtain ⟨rp, hR, hC⟩ := hInv.replyCallerLinkage.1.1 tid ty rid hy (p.fields.2.1 ▸ hRO)
    exact ⟨rp, (hRep _ _).mpr hR, hC⟩
  -- replyCallerLinkageReciprocal, reply to thread.
  · intro rid rp tid hR hC
    obtain ⟨ty, hy, hRO, hBlk⟩ := hInv.replyCallerLinkage.1.2 rid rp tid ((hRep _ _).mp hR) hC
    obtain ⟨tx, hx, p⟩ := hFw hy
    exact ⟨tx, hx, p.fields.2.1.trans hRO, (p.reply_any hB).mpr hBlk⟩
  -- blockedOnReplyHasReplyObject.
  · intro tid tcb ep rt hT hBlk
    obtain ⟨ty, hy, p⟩ := hBk hT
    obtain ⟨rt', hy'⟩ := (p.reply_iff hB ep).mp ⟨rt, hBlk⟩
    obtain ⟨rid, hRid⟩ := hInv.replyCallerLinkage.2 tid ty ep rt' hy hy'
    exact ⟨rid, p.fields.2.1.trans hRid⟩
  -- pendingReceiveReplyWellFormed: the stash's receiver is receiving, its reply free.
  · intro tid tcb rid hT hStash
    rw [getTcb?_eq_some_iff] at hT
    obtain ⟨ty, hy, p⟩ := hBk hT
    obtain ⟨⟨ep, hEp⟩, rp, hR, hC⟩ := hInv.pendingReceiveReplyWellFormed.1 tid ty rid
      ((getTcb?_eq_some_iff st tid ty).mpr hy) (p.fields.2.2.1 ▸ hStash)
    rw [getReply?_eq_some_iff] at hR
    exact ⟨⟨ep, (p.nonReply hB (fun _ _ => by exact ThreadIpcState.noConfusion)).mpr hEp⟩, rp,
      (getReply?_eq_some_iff _ rid rp).mpr ((hRep _ _).mpr hR), hC⟩
  -- ...the stash is injective.
  · intro tid₁ tid₂ tcb₁ tcb₂ rid hT₁ hT₂ hS₁ hS₂
    rw [getTcb?_eq_some_iff] at hT₁ hT₂
    obtain ⟨y₁, hy₁, p₁⟩ := hBk hT₁
    obtain ⟨y₂, hy₂, p₂⟩ := hBk hT₂
    exact hInv.pendingReceiveReplyWellFormed.2.1 tid₁ tid₂ y₁ y₂ rid
      ((getTcb?_eq_some_iff st tid₁ y₁).mpr hy₁) ((getTcb?_eq_some_iff st tid₂ y₂).mpr hy₂)
      (p₁.fields.2.2.1 ▸ hS₁) (p₂.fields.2.2.1 ▸ hS₂)
  -- ...every stash is recorded on its reply.
  · intro tid tcb rid hT hStash
    rw [getTcb?_eq_some_iff] at hT
    obtain ⟨ty, hy, p⟩ := hBk hT
    obtain ⟨rp, hR, hRec⟩ := hInv.pendingReceiveReplyWellFormed.2.2 tid ty rid
      ((getTcb?_eq_some_iff st tid ty).mpr hy) (p.fields.2.2.1 ▸ hStash)
    rw [getReply?_eq_some_iff] at hR
    exact ⟨rp, (getReply?_eq_some_iff _ rid rp).mpr ((hRep _ _).mpr hR), hRec⟩
  -- donationOwnerUnique.
  · intro t1 t2 tcb1 tcb2 s1 s2 owner h1 h2 hB1 hB2
    obtain ⟨y1, hy1, p1⟩ := hBk h1
    obtain ⟨y2, hy2, p2⟩ := hBk h2
    exact hInv.donationOwnerUnique t1 t2 y1 y2 s1 s2 owner hy1 hy2 (p1.fields.1 ▸ hB1)
      (p2.fields.1 ▸ hB2)
  -- endpointQueueTailBlockedConsistent.
  · intro epId ep tl tcb hEp hT
    obtain ⟨ty, hy, p⟩ := hBk hT
    obtain ⟨hRecv, hSend⟩ := hInv.endpointQueueTailBlockedConsistent epId ep tl ty
      ((hNT _ _ (fun _ => by exact KernelObject.noConfusion)).mp hEp) hy
    refine ⟨fun h => (p.nonReply hB (fun _ _ => by exact ThreadIpcState.noConfusion)).mpr
      (hRecv h), fun h => ?_⟩
    rcases hSend h with h' | h'
    · exact Or.inl ((p.nonReply hB (fun _ _ => by exact ThreadIpcState.noConfusion)).mpr h')
    · exact Or.inr ((p.nonReply hB (fun _ _ => by exact ThreadIpcState.noConfusion)).mpr h')
  -- queueNextTargetBlocked.
  · intro a b tcbA tcbB hA hBb hNext
    obtain ⟨yA, hyA, pA⟩ := hBk hA
    obtain ⟨yB, hyB, pB⟩ := hBk hBb
    obtain ⟨hRecv, hSend⟩ :=
      hInv.queueNextTargetBlocked a b yA yB hyA hyB (pA.fields.2.2.2.1 ▸ hNext)
    have nr : ∀ {tx ty : TCB}, serverForgetPair old tx ty →
        ∀ s : ThreadIpcState, (∀ ep rt, s ≠ .blockedOnReply ep rt) →
        (tx.ipcState = s ↔ ty.ipcState = s) := fun h s hs => h.nonReply hB hs
    refine ⟨fun ep h => (nr pB _ (fun _ _ => by exact ThreadIpcState.noConfusion)).mpr
      (hRecv ep ((nr pA _ (fun _ _ => by exact ThreadIpcState.noConfusion)).mp h)),
      fun ep h => ?_⟩
    have h' : yA.ipcState = .blockedOnSend ep ∨ yA.ipcState = .blockedOnCall ep := by
      rcases h with h | h
      · exact Or.inl ((nr pA _ (fun _ _ => by exact ThreadIpcState.noConfusion)).mp h)
      · exact Or.inr ((nr pA _ (fun _ _ => by exact ThreadIpcState.noConfusion)).mp h)
    rcases hSend ep h' with h'' | h''
    · exact Or.inl ((nr pB _ (fun _ _ => by exact ThreadIpcState.noConfusion)).mpr h'')
    · exact Or.inr ((nr pB _ (fun _ _ => by exact ThreadIpcState.noConfusion)).mpr h'')
  -- notificationBindingReciprocal: the binding codes are kept.
  · intro oid
    by_cases hEq : oid = key
    · subst hEq; rw [hAt, hPre]; rfl
    · rw [hFrame oid hEq]
  -- endpointQueueLinksOnlyBlocked.
  · intro a tcbA hA hNext
    obtain ⟨yA, hyA, pA⟩ := hBk hA
    rw [pA.endpointQueued hB]
    exact hInv.endpointQueueLinksOnlyBlocked a yA hyA (pA.fields.2.2.2.1 ▸ hNext)

/-- **...so across the in-place write of a reply-blocked thread's server
forgotten** (`mapTcbInPlace` with `TCB.serverForgotten`). -/
theorem ipcInvariantFull_mapTcbInPlace_serverForgotten {st : SystemState}
    {w : SeLe4n.ThreadId} {t : TCB} {e : SeLe4n.ObjId} {r : Option SeLe4n.ThreadId}
    (hInv : ipcInvariantFull st) (hT : st.getTcb? w = some t)
    (hB : t.ipcState = .blockedOnReply e r) :
    ipcInvariantFull (st.mapTcbInPlace w TCB.serverForgotten) := by
  have hPre := (getTcb?_eq_some_iff st w t).mp hT
  refine ipcInvariantFull_of_serverForgotten st _ w.toObjId t hInv hPre ?_ ?_ hB
  · rw [objects_mapTcbInPlace, if_pos (beq_self_eq_true _), hPre]; rfl
  · intro oid hNe
    rw [objects_mapTcbInPlace, if_neg (by simpa using fun h => hNe h.symm)]

/-- **A caller whose server code names `x` is reply-blocked on `x`.** -/
theorem replyCallerServerCode_blocked {t : TCB} {x : SeLe4n.ThreadId}
    (h : replyCallerServerCode t = x.val + 1) :
    t.blockingServer? = some x ∧ ∃ e, t.ipcState = .blockedOnReply e (some x) := by
  unfold replyCallerServerCode at h
  cases hb : t.blockingServer? with
  | none => rw [hb] at h; cases h
  | some s =>
    rw [hb] at h
    have hsx : s = x := by cases s; cases x; simp only [Nat.add_right_cancel_iff] at h; subst h; rfl
    subst hsx
    refine ⟨rfl, ?_⟩
    unfold TCB.blockingServer? at hb
    split at hb
    · rename_i e _ hI; cases hb; exact ⟨e, hI⟩
    · cases hb

/-- **The orphan step keeps the IPC bundle**: the caller's server forgotten
(`ipcInvariantFull_mapTcbInPlace_serverForgotten`), then its unlink, which writes
reply-waiter links alone (`ipcInvariantFull_of_objectsAgreeOffRunLinks`). -/
theorem orphanReplyWaiter_preserves_ipcInvariantFull {st : SystemState}
    {w x : SeLe4n.ThreadId} {t : TCB} (hFull : ipcInvariantFull st)
    (hT : st.getTcb? w = some t) (hS : replyCallerServerCode t = x.val + 1) :
    ipcInvariantFull (orphanReplyWaiter st w x) := by
  obtain ⟨-, e, hB⟩ := replyCallerServerCode_blocked hS
  exact ipcInvariantFull_of_objectsAgreeOffRunLinks
    (SystemState.unlinkReplyWaiter_objectsAgreeOffRunLinks _ w x)
    (ipcInvariantFull_mapTcbInPlace_serverForgotten hFull hT hB)

/-- **The orphan step's reply views**: the caller names no server and leaves
`x`'s queue. -/
theorem orphanReplyWaiter_replyViews (st : SystemState) (w x : SeLe4n.ThreadId) :
    (orphanReplyWaiter st w x).replyViews =
      ReplyViews.unlink (ReplyViews.setServer st.replyViews w none) w x := by
  unfold orphanReplyWaiter
  rw [SystemState.replyViews_unlinkReplyWaiter,
    SystemState.replyViews_mapTcbInPlace _ w (gv := fun v => { v with server := none })
      (fun _ => rfl)]
  rfl

/-- **The orphan step is an unlink of the views**: the caller, reply-blocked on
`x`, leaves `x`'s queue and names no server. -/
theorem orphanReplyWaiter_unlinkStep {st : SystemState} {w x : SeLe4n.ThreadId} {t : TCB}
    (hc : st.replyWaitersConsistent) (hT : st.getTcb? w = some t)
    (hS : replyCallerServerCode t = x.val + 1) :
    ∃ vs0, ReplyViews.UnlinkStep st.replyViews (orphanReplyWaiter st w x).replyViews w x
      t.replyView vs0 := by
  obtain ⟨hB, -⟩ := replyCallerServerCode_blocked hS
  have hW0 : st.replyViews w.toObjId = some t.replyView :=
    SystemState.replyViews_of_tcb ((getTcb?_eq_some_iff _ _ _).mp hT)
  obtain ⟨vs0, hS0⟩ := hc.2.1 w t.replyView x hW0 hB
  rw [orphanReplyWaiter_replyViews]
  exact ⟨vs0, ReplyViews.unlinkStep_of_unlink hc hW0 hB hS0⟩

/-- ...so it keeps the reply-waiter queues consistent. -/
theorem orphanReplyWaiter_replyWaitersConsistent {st : SystemState} {w x : SeLe4n.ThreadId}
    {t : TCB} (hc : st.replyWaitersConsistent) (hT : st.getTcb? w = some t)
    (hS : replyCallerServerCode t = x.val + 1) :
    (orphanReplyWaiter st w x).replyWaitersConsistent :=
  let ⟨_, U⟩ := orphanReplyWaiter_unlinkStep hc hT hS
  U.consistent hc

/-- The server-forget write maps each object to the same image whether or not
it has been applied: forgetting twice is forgetting once. -/
theorem mapTcbInPlace_serverForgotten_agree (st : SystemState) (w : SeLe4n.ThreadId)
    (k : SeLe4n.ObjId) :
    ((st.mapTcbInPlace w TCB.serverForgotten).objects[k]?).map
        (KernelObject.mapTcb TCB.serverForgotten) =
      (st.objects[k]?).map (KernelObject.mapTcb TCB.serverForgotten) := by
  rw [objects_mapTcbInPlace]
  split
  · cases st.objects[k]? with
    | none => rfl
    | some o => cases o <;> rfl
  · rfl

/-- **Forgetting a blocked caller's server is a run-queue stage**: it writes the
caller's state word alone, which keeps the caller blocked on its reply (so not
ready, as before) and every run link, yield code, refill view and scheduler
slot as it was. -/
theorem mapTcbInPlace_serverForgotten_runQueueStage {st : SystemState} {w : SeLe4n.ThreadId}
    {t : TCB} {e : SeLe4n.ObjId} {r : Option SeLe4n.ThreadId} (hT : st.getTcb? w = some t)
    (hB : t.ipcState = .blockedOnReply e r) :
    RunQueueStage st (st.mapTcbInPlace w TCB.serverForgotten) := by
  have hL : ∀ c y, (st.mapTcbInPlace w TCB.serverForgotten).runLinkOn c y = st.runLinkOn c y :=
    fun c y => by
      rw [runLinkOn_mapTcbInPlace_map st w TCB.serverForgotten c id (fun _ => rfl) rfl y]
      try (split <;> rfl)
  have hG : ∀ y, (st.mapTcbInPlace w TCB.serverForgotten).getTcb? y =
      if w.toObjId = y.toObjId then (st.getTcb? y).map TCB.serverForgotten else st.getTcb? y :=
    fun y => by
      split
      · rename_i h
        rw [← ThreadId.toObjId_injective _ _ h, mapTcbInPlace_getTcb?_self]
      · rename_i h; exact mapTcbInPlace_getTcb?_ne _ _ _ _ h
  have hM : StateMono st (st.mapTcbInPlace w TCB.serverForgotten) := by
    refine StateMono.of_pointwise (fun y x hx => ?_) (fun y x' hx' hc => ?_)
      (fun y x' hx' hn => ?_)
    · rw [hG y]; split
      · rename_i h
        rw [hx]
        refine ⟨_, rfl, fun hr => ?_, id, rfl⟩
        rw [← ThreadId.toObjId_injective _ _ h, hT] at hx
        cases hx; rw [hB] at hr; cases hr
      · exact ⟨x, hx, fun h => h, id, rfl⟩
    · rw [hG y] at hx'; split at hx'
      · rename_i h
        obtain rfl := ThreadId.toObjId_injective _ _ h
        rw [hT] at hx'
        cases hx'
        rcases hc t hT with hr | ha
        · rw [hB] at hr; cases hr
        · exact Or.inr ha
      · exact hc x' hx'
    · rw [hG y] at hx'; split at hx' <;> simp [hn] at hx'
  exact ⟨.of_frames
      (fun h q => ⟨mapTcbInPlace_objects_invExt _ _ _ h,
        mapTcbInPlace_runQueueRefined_of_runLinks _ _ (fun _ _ => rfl) q⟩)
      (fun _ => releaseStateAgree.mapTcbInPlace _ _ _)
      (fun _ => Kernel.RefillViewsKept.of_map (KernelObject.mapTcb TCB.serverForgotten)
        (fun o => by cases o <;> rfl) (mapTcbInPlace_serverForgotten_agree st w))
      (fun _ => Kernel.YieldLinksKept.of_map (KernelObject.mapTcb TCB.serverForgotten)
        (fun o => by cases o <;> rfl) (mapTcbInPlace_serverForgotten_agree st w)),
    fun _ _ _ _ d => currentDequeuedUniqueExcept_of_eq (by rw [mapTcbInPlace_scheduler]) hL hM d, fun _ _ => hM⟩

/-- **The orphan step is a run-queue stage**: the server-forget write, then the
reply-waiter unlink, which writes reply-waiter links alone. -/
theorem orphanReplyWaiter_runQueueStage {st : SystemState} {w x : SeLe4n.ThreadId} {t : TCB}
    (hT : st.getTcb? w = some t) (hS : replyCallerServerCode t = x.val + 1) :
    RunQueueStage st (orphanReplyWaiter st w x) :=
  let ⟨_, _, hB⟩ := replyCallerServerCode_blocked hS
  (mapTcbInPlace_serverForgotten_runQueueStage hT hB).trans
    (SystemState.unlinkReplyWaiter_runQueueStage _ w x)

/-- **The donation-stack head pop is a run-queue stage**: at most two replies
stored over replies. -/
theorem storeDonationHeadPop_runQueueStage {st st' : SystemState} {scId : SeLe4n.SchedContextId}
    {head? : Option (SeLe4n.ReplyId × Reply)}
    (h : storeDonationHeadPop scId head? st = .ok st') : RunQueueStage st st' := by
  rcases storeDonationHeadPop_cases h with ⟨_, rfl⟩ | ⟨rid, rh, s1, _, hClear, hReHead⟩
  · exact .refl _
  · have f1 : RunQueueStage st s1 := by
      rcases storeDonationHeadClear_cases hClear with rfl | ⟨rid0, r0, _, hRead, hS0⟩
      · exact .refl _
      · exact RunQueueStage.storeObject_nonTcb hS0 hRead (fun _ e => by cases e)
          (fun _ e => by cases e)
    have f2 : RunQueueStage s1 st' := by
      rcases storeReplyReHead_cases hReHead with rfl | ⟨below, b, _, hReadB, hS2⟩
      · exact .refl _
      · exact RunQueueStage.storeObject_nonTcb hS2 hReadB (fun _ e => by cases e)
          (fun _ e => by cases e)
    exact f1.trans f2

/-- **The unheld pop is a run-queue frame stage off the context it rebinds**:
the context stored over itself with a new holder and head, the head pop, the
recipient's binding codes, and the key-change flags. -/
theorem returnUnheldSchedContext_runQueueFrameStage {st st' : SystemState}
    {scId : SeLe4n.SchedContextId} {owner : SeLe4n.ThreadId} {newOwner? : Option SeLe4n.ThreadId}
    (h : returnUnheldSchedContext st scId owner newOwner? = .ok st') :
    SystemState.RunQueueFrameStage (· = scId) st st' := by
  obtain ⟨sc, head?, ot, s1, s2, s3, hSc, -, -, -, -, hS1, hS2, hL, hS3, hEq⟩ :=
    returnUnheldSchedContext_ok_storeChain st st' scId owner newOwner? h
  have f1 : SystemState.RunQueueFrameStage (· = scId) st s1 := by
    have f := SystemState.RunQueueFrameStage.storeObject hS1 (fun c => by rw [hSc]; rfl)
      (by rw [hSc]; simp [objStateMono, objTcb?])
      (hR := fun c => by rw [hSc]; rfl) (hY := by rw [hSc]; rfl)
    exact f.mono (fun x e => e.trans rfl)
  have f2 := storeDonationHeadPop_runQueueStage hS2
  have hO2 : s2.objects[owner.toObjId]? = some (.tcb ot) := lookupTcb_some_objects s2 owner ot hL
  have f3 : RunQueueStage s2 s3 := RunQueueStage.storeObject_tcb hS3 hO2 (fun _ => rfl)
  rw [hEq]
  exact (f1.trans (f2.toFrame _)).trans ((f3.trans (markKeyChangeFrom_runQueueStage st s3 owner)).toFrame _)

/-- **A finalised reply's pop off an unheld context, and its settle, is a
run-queue stage**: the pop a frame stage off the context
(`returnUnheldSchedContext_runQueueFrameStage`), closed by the settle
(`settleReturnedContext_runQueueStage`) on a context whose refills the pop kept,
so well formed. -/
theorem finaliseReplyUnheldPop_runQueueStage (st : SystemState) (r : Reply) (c : SeLe4n.ThreadId) :
    RunQueueStage st (finaliseReplyUnheldPop st r c) := by
  unfold finaliseReplyUnheldPop
  split
  · split
    · rename_i hOk
      unfold returnUnheldSchedContextResolved at hOk
      split at hOk
      · cases hOk
      · refine SchedContextOps.settleReturnedContext_runQueueStage
          (returnUnheldSchedContext_runQueueFrameStage hOk) ?_
        intro S hS hInv hSnd _ a ha
        obtain ⟨sc, _, _, hSc, -, -, -, -, -, hSc', -⟩ := returnUnheldSchedContext_objects hInv hOk
        rw [(SystemState.getSchedContext?_eq_some_iff _ _ _).mp ha] at hSc'
        cases hSc'
        exact schedContextWellFormed_of_refillsView rfl
          (hSnd.1 _ sc hS ((SystemState.getSchedContext?_eq_some_iff _ _ _).mpr hSc))
    · exact .refl _
  · exact .refl _

/-- **The pop at an unheld head is a run-queue stage** (WS-ZA ZA6.34): the
unheld pop a frame stage off the context, closed by the settle on a context
whose refills the pop kept. -/
theorem popUnheldReplyHead_runQueueStage {st st' : SystemState} {rid : SeLe4n.ReplyId}
    {target : SeLe4n.ThreadId} {home : Concurrency.CoreId}
    (h : popUnheldReplyHead st rid target home = .ok st') : RunQueueStage st st' := by
  rcases popUnheldReplyHead_objects_frame h with ⟨-, rfl⟩ | ⟨scId, _, st1, -, -, hOk, rfl⟩
  · exact .refl _
  · refine SchedContextOps.settleReturnedContext_runQueueStage
      (returnUnheldSchedContext_runQueueFrameStage hOk) ?_
    intro S hS hInv hSnd _ a ha
    obtain ⟨sc, _, _, hSc, -, -, -, -, -, hSc', -⟩ := returnUnheldSchedContext_objects hInv hOk
    rw [(SystemState.getSchedContext?_eq_some_iff _ _ _).mp ha] at hSc'
    cases hSc'
    exact schedContextWellFormed_of_refillsView rfl
      (hSnd.1 _ sc hS ((SystemState.getSchedContext?_eq_some_iff _ _ _).mpr hSc))

end SeLe4n.Kernel
