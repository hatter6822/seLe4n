-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.API
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.ReplyHolderCancel

/-!
# A reply holder's cancel keeps the IPC bundle and frees the reply

WS-SX SX4: a receive whose reply is busy cancels the reply's holder first
(`cancelRecvBusyReply`, seL4-MCS `receiveIPC`'s `cancelIPC(replyTCB)`), and
commits that cancel before the reply resolution's defensive refusal
(`resolveRecvReplyId`'s `replyCapInvalid`).  This module proves the two facts
that design rests on:

* **the cancel keeps `ipcInvariantFull`** (`cancelReplyHolder_preserves_ipcInvariantFull`):
  the head cut (`cutCancelledCallerHead_preserves_ipcInvariantFull`), the
  teardown (`cancelIpcBlocking_preserves_ipcInvariantFull`), the priority revert
  and the `Inactive` write.  The teardown's queue-connectivity premises at the
  holder are taken as a hypothesis (`replyHolderCancelPremises`), exactly as
  `cancelIpcBlockingOnCore_preserves_ipcInvariantFull` takes them: nothing in
  the tree derives them from the invariants;
* **after the cancel the reply resolution refuses nothing**
  (`resolveRecvReplyId_cancelRecvBusyReply`): under the same premises the reply
  the receive names has no caller and no live stash once its holder is
  cancelled (`cancelReplyHolder_frees_reply`), so the refusal the cancel
  commits before cannot fire.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The head cut keeps the IPC bundle**: the cut frame's upward link is a
stack link (`storeObject_reply_stackLinks_preserves_ipcInvariantFull`), the
context's head and origin are content the bundle does not read
(`insertObjects_schedContextContentUpdate_preserves_ipcInvariantFull`), and a
holder's loan made its own is `updateTcb_ownerCleared_preserves_ipcInvariantFull`. -/
theorem cutCancelledCallerHead_preserves_ipcInvariantFull (st : SystemState) (tcb : TCB)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st) :
    ipcInvariantFull (Lifecycle.Suspend.cutCancelledCallerHead st tcb) ∧
      (Lifecycle.Suspend.cutCancelledCallerHead st tcb).objects.invExt :=
  Lifecycle.Suspend.cutCancelledCallerHead_closed
    (fun s => ipcInvariantFull s ∧ s.objects.invExt)
    (fun s s1 rid r scId ⟨hI, hO⟩ _ hR hS => by
      have hO1 := storeObject_preserves_objects_invExt s _ _ _ hO hS
      have hI1 := storeObject_reply_stackLinks_preserves_ipcInvariantFull
        (a' := { r with next := none }) hO hI hR rfl rfl hS
      refine ⟨?_, SystemState.updateSchedContext_preserves_objects_invExt _ scId _ hO1⟩
      cases hSc : s1.getSchedContext? scId with
      | none => rw [SystemState.updateSchedContext_eq_self_of_none hSc]; exact hI1
      | some sc =>
        rw [SystemState.updateSchedContext_eq_of_some hSc]
        exact insertObjects_schedContextContentUpdate_preserves_ipcInvariantFull s1 _ sc _ hO1 hI1
          ((SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc) rfl)
    (fun s scId holder ht o ⟨hI, hO⟩ _ hT hB =>
      ⟨ipcInvariantFull_of_objects_eq (markKeyChangeFrom_objects _ _ _)
          (updateTcb_ownerCleared_preserves_ipcInvariantFull s holder ht scId o hO hI hT hB),
        by rw [markKeyChangeFrom_objects]; exact SystemState.updateTcb_preserves_objects_invExt _ _ _ hO⟩)
    st tcb ⟨hInv, hObjInv⟩

/-- **What a reply holder's cancel owes for the whole bundle**: the holder
reads on the cut state the TCB it was cancelled with, and the teardown's
queue-connectivity premises hold of it there (`cancelIpcBlockingArmPremises`).
Vacuous for a holder that resolves to no TCB, whose cancel is the identity. -/
def replyHolderCancelPremises (st : SystemState) (holder : SeLe4n.ThreadId) : Prop :=
  ∀ tcb, lookupTcb st holder = some tcb →
    lookupTcb (Lifecycle.Suspend.cutCancelledCallerHead st tcb) holder = some tcb ∧
    cancelIpcBlockingArmPremises (Lifecycle.Suspend.cutCancelledCallerHead st tcb) holder tcb

/-- **A reply holder's cancel keeps `ipcInvariantFull`** (seL4-MCS
`cancelIPC(replyTCB)`): the identity on a holder that is not blocked; otherwise
the head cut, the teardown on the cut state, the priority revert (which writes
boosts and run-queue links alone) and the `Inactive` write (a field no
conjunct reads). -/
theorem cancelReplyHolder_preserves_ipcInvariantFull (st : SystemState)
    (holder : SeLe4n.ThreadId) (ec : Concurrency.CoreId)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hBudgets : allTimeoutBudgetsNone st) (hP : replyHolderCancelPremises st holder) :
    ipcInvariantFull (cancelReplyHolder st holder ec) := by
  rcases cancelReplyHolder_cases st holder ec with h | ⟨tcb, hL, -, h⟩
  · rw [h]; exact hInv
  rw [h]
  obtain ⟨hLc, hArms⟩ := hP tcb hL
  obtain ⟨hIc, hOc⟩ := cutCancelledCallerHead_preserves_ipcInvariantFull st tcb hObjInv hInv
  have hBc : allTimeoutBudgetsNone (Lifecycle.Suspend.cutCancelledCallerHead st tcb) := by
    intro y t hy
    have e := cutCancelledCallerHead_getTcb?_map st tcb TCB.timeoutBudget (fun _ => rfl) hObjInv y
    rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hy] at e
    cases hs : st.getTcb? y with
    | none => rw [hs] at e; cases e
    | some t0 =>
      rw [hs] at e
      rw [Option.some.inj e]
      exact hBudgets y t0 ((SystemState.getTcb?_eq_some_iff _ _ _).mp hs)
  have hK : ipcInvariantFull (Lifecycle.Suspend.cancelIpcKeepingContexts st holder tcb) := by
    unfold Lifecycle.Suspend.cancelIpcKeepingContexts
    exact cancelIpcBlocking_preserves_ipcInvariantFull _ holder tcb hOc hLc hIc hBc hArms
  have hOK := Lifecycle.Suspend.cancelIpcKeepingContexts_preserves_objects_invExt st holder tcb hObjInv
  have hR : ipcInvariantFull (Lifecycle.Suspend.suspendCancelRevert st holder tcb ec) ∧
      (Lifecycle.Suspend.suspendCancelRevert st holder tcb ec).objects.invExt := by
    unfold Lifecycle.Suspend.suspendCancelRevert; dsimp only; split
    · exact ⟨propagatePipChainCrossCore_preserves_ipcInvariantFull _ _ ec _ hOK hK,
        PriorityInheritance.propagatePipChainCrossCore_preserves_objects_invExt _ _ _ _ hOK⟩
    · exact ⟨hK, hOK⟩
  cases hT : (Lifecycle.Suspend.suspendCancelRevert st holder tcb ec).getTcb? holder with
  | none => rw [SystemState.updateTcb_eq_self_of_none hT]; exact hR.1
  | some t =>
    rw [SystemState.updateTcb_eq_of_some hT]
    exact insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull _ holder t _ hR.2 hR.1
      ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- **The stash test a reply's record is re-checked with**
(`SystemState.replyStashedAt`) passes exactly on a thread blocked receiving with
that reply stashed. -/
theorem TCB.stashTest_eq_true_iff (t : TCB) (rid : SeLe4n.ReplyId) :
    (t.ipcStateCode == 1 && t.pendingReceiveReplyCode == rid.val + 1) = true ↔
      (∃ ep, t.ipcState = .blockedOnReceive ep) ∧ t.pendingReceiveReply = some rid := by
  have hs : t.ipcStateCode = t.ipcState.stateCode := by
    unfold TCB.ipcState; rw [ThreadIpcState.stateCode_ofCodes]
  have hp : (t.pendingReceiveReplyCode == rid.val + 1) = (t.pendingReceiveReply == some rid) := by
    unfold TCB.pendingReceiveReply SeLe4n.ReplyId.ofOptCode
    rcases t.pendingReceiveReplyCode with _ | k
    · simp
    · rcases rid with ⟨v⟩
      by_cases hkv : k = v
      · subst hkv; simp
      · rw [beq_eq_false_iff_ne.mpr (by simp only [ne_eq]; omega), beq_eq_false_iff_ne.mpr
          (fun e => hkv (congrArg SeLe4n.ReplyId.val (Option.some.inj e)))]
  rw [hs, hp]
  cases t.ipcState <;> simp [ThreadIpcState.stateCode]

/-- The readings the reply's freedom is decided on, which the cancel moves on
no thread but the holder. -/
private theorem replyReadings_cancelBlind :
    TcbReadingCancelBlind (fun t : TCB => (t.ipcState, t.replyObject, t.pendingReceiveReply)) :=
  ⟨fun _ _ _ _ _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

/-- **A busy reply's holder, cancelled, leaves the reply free** (seL4-MCS
`cancelIPC(replyTCB)` running `reply_remove_tcb` or `reply_unlink`): the reply
is still a reply, names no caller, and its recorded stasher no longer stashes
it.  A caller the cancelled state's reply named would be reply-blocked on it
(`replyCallerLinkage`), so another thread already its caller before the
cancel, or the holder, which the cancel leaves `.ready`; a live stasher would be
the holder, now `.ready`, or another thread already stashing it, which
`pendingReceiveReplyWellFormed` refutes: a stashed reply has no caller, and a
reply has one stasher. -/
theorem cancelReplyHolder_frees_reply (st : SystemState) (tid holder : SeLe4n.ThreadId)
    (ec : Concurrency.CoreId) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hBudgets : allTimeoutBudgetsNone st) (hNotRes : ¬ holder.isReserved)
    (hP : replyHolderCancelPremises st holder)
    (hBusy : busyReplyHolderCode st tid rid = holder.val + 1) :
    ∃ r, (cancelReplyHolder st holder ec).getReply? rid = some r ∧ r.caller = none ∧
      (cancelReplyHolder st holder ec).replyStashedAt rid r = false := by
  have hHid : (⟨holder.val⟩ : SeLe4n.ThreadId) = holder := rfl
  unfold busyReplyHolderCode at hBusy
  cases hR0 : st.getReply? rid with
  | none => rw [hR0] at hBusy; simp at hBusy
  | some r0 =>
  rw [hR0] at hBusy
  simp only at hBusy
  have hShape : r0.caller = some holder ∨
      (r0.caller = none ∧ st.replyStashedAt rid r0 = true ∧ r0.stasherCode = holder.val + 1) := by
    cases hc : r0.caller with
    | some c =>
      rw [hc] at hBusy
      by_cases hct : c = tid
      · simp [hct] at hBusy
      · simp only [hct, if_false] at hBusy
        left
        have : c.val = holder.val := by omega
        cases c; cases holder; simp_all
    | none =>
      rw [hc] at hBusy
      cases hS : st.replyStashedAt rid r0
      · simp [hS] at hBusy
      · simp only [hS, if_true] at hBusy
        by_cases hst : r0.stasherCode = tid.val + 1
        · simp [hst] at hBusy
        · simp only [hst, if_false] at hBusy
          exact .inr ⟨rfl, rfl, hBusy⟩
  -- The holder, blocked before the cancel.
  obtain ⟨tH, hTH, hNR⟩ : ∃ t, st.getTcb? holder = some t ∧ t.ipcState ≠ .ready := by
    rcases hShape with hc | ⟨-, hS, hCode⟩
    · obtain ⟨t, ht, -, ep, rt, hb⟩ := hInv.replyCallerLinkage.1.2 rid r0 holder
        ((SystemState.getReply?_eq_some_iff _ _ _).mp hR0) hc
      exact ⟨t, (SystemState.getTcb?_eq_some_iff _ _ _).mpr ht, by rw [hb]; intro h; cases h⟩
    · unfold SystemState.replyStashedAt at hS
      rw [hCode] at hS
      simp only [hHid] at hS
      cases ht : st.getTcb? holder with
      | none => rw [ht] at hS; cases hS
      | some t =>
        rw [ht] at hS
        obtain ⟨⟨ep, he⟩, -⟩ := (TCB.stashTest_eq_true_iff t rid).mp hS
        exact ⟨t, rfl, by rw [he]; intro h; cases h⟩
  have hL : lookupTcb st holder = some tH :=
    lookupTcb_of_objects_of_not_reserved st holder tH
      ((SystemState.getTcb?_eq_some_iff _ _ _).mp hTH) hNotRes
  have hF : cancelReplyHolder st holder ec =
      (Lifecycle.Suspend.suspendCancelRevert st holder tH ec).updateTcb holder
        (fun t => { t with threadState := .Inactive }) := by
    have hcond : ¬ ((tH.ipcStateCode == 0 && tH.ipcObjectCode == 0) = true) := by
      intro hc
      apply hNR
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact (TCB.ipcState_eq_iff_codes tH .ready).mpr
        ⟨by rw [hc.2]; rfl, by rw [hc.1]; rfl⟩
    unfold cancelReplyHolder
    split
    · rename_i h; rw [hL] at h; cases h
    · rename_i tcb h
      rw [hL] at h
      cases h
      split
      · rename_i hB; exact absurd hB hcond
      · rfl
  have hI2 : (Lifecycle.Suspend.suspendCancelRevert st holder tH ec).objects.invExt := by
    have hI1 := Lifecycle.Suspend.cancelIpcKeepingContexts_preserves_objects_invExt st holder tH hObjInv
    unfold Lifecycle.Suspend.suspendCancelRevert; dsimp only; split
    · exact PriorityInheritance.propagatePipChainCrossCore_preserves_objects_invExt _ _ _ _ hI1
    · exact hI1
  -- The holder, `.ready` after it.
  have hReady : ∀ t', (cancelReplyHolder st holder ec).getTcb? holder = some t' →
      t'.ipcState = .ready := by
    intro t' ht'
    rw [hF] at ht'
    obtain ⟨t, ht, he⟩ := updateTcb_getTcb?_back (tid := holder)
      (f := fun t => { t with threadState := .Inactive }) hI2 (fun _ => rfl) ht'
    rw [← he]
    exact suspendCancelRevert_holder_ready st holder tH ec hObjInv hL t ht
  have hIF := cancelReplyHolder_preserves_ipcInvariantFull st holder ec hObjInv hInv hBudgets hP
  have hK := cancelReplyHolder_tcbReadingKeptExcept replyReadings_cancelBlind st holder ec hObjInv
  have back : ∀ (y : SeLe4n.ThreadId) (t' : TCB), y ≠ holder →
      (cancelReplyHolder st holder ec).getTcb? y = some t' →
      ∃ t, st.getTcb? y = some t ∧ t.ipcState = t'.ipcState ∧ t.replyObject = t'.replyObject ∧
        t.pendingReceiveReply = t'.pendingReceiveReply := by
    intro y t' hy ht'
    have e := hK y hy
    rw [ht'] at e
    cases hs : st.getTcb? y with
    | none => rw [hs] at e; cases e
    | some t =>
      rw [hs] at e
      have e' := Option.some.inj e
      simp only [Prod.mk.injEq] at e'
      exact ⟨t, rfl, e'.1.symm, e'.2.1.symm, e'.2.2.symm⟩
  have hR0o := (SystemState.getReply?_eq_some_iff _ _ _).mp hR0
  -- The reply, still a reply.
  obtain ⟨r, hRF⟩ : ∃ r, (cancelReplyHolder st holder ec).getReply? rid = some r := by
    rcases (cancelReplyHolder_finaliseFrameAny st holder ec hObjInv).write rid.toObjId with
      e | ⟨pre, post, hp, hq, ht, -, -⟩
    · exact ⟨r0, (SystemState.getReply?_eq_some_iff _ _ _).mpr (e.trans hR0o)⟩
    · rw [hR0o] at hp
      cases hp
      cases post with
      | reply r => exact ⟨r, (SystemState.getReply?_eq_some_iff _ _ _).mpr hq⟩
      | _ => simp [KernelObject.objectType] at ht
  -- No caller.
  have hCaller : r.caller = none := by
    cases hc : r.caller with
    | none => rfl
    | some x =>
      exfalso
      obtain ⟨tx, htx, hro, ep, rt, hb⟩ := hIF.replyCallerLinkage.1.2 rid r x
        ((SystemState.getReply?_eq_some_iff _ _ _).mp hRF) hc
      have htx' := (SystemState.getTcb?_eq_some_iff _ _ _).mpr htx
      by_cases hx : x = holder
      · subst hx; rw [hReady tx htx'] at hb; cases hb
      · obtain ⟨t0, ht0, -, hro0, -⟩ := back x tx hx htx'
        obtain ⟨r1, hr1, hc1⟩ := hInv.replyCallerLinkage.1.1 x t0 rid
          ((SystemState.getTcb?_eq_some_iff _ _ _).mp ht0) (hro0.trans hro)
        rw [hR0o] at hr1
        cases hr1
        rcases hShape with h1 | ⟨h1, -⟩ <;> rw [h1] at hc1
        · exact hx (Option.some.inj hc1).symm
        · cases hc1
  refine ⟨r, hRF, hCaller, ?_⟩
  -- No live stash.
  cases hst : (cancelReplyHolder st holder ec).replyStashedAt rid r with
  | false => rfl
  | true =>
    exfalso
    unfold SystemState.replyStashedAt at hst
    split at hst
    · cases hst
    · rename_i k _
      split at hst
      · rename_i t hT
        obtain ⟨⟨ep, he⟩, hSr⟩ := (TCB.stashTest_eq_true_iff t rid).mp hst
        by_cases hk : (⟨k⟩ : SeLe4n.ThreadId) = holder
        · rw [hk] at hT; rw [hReady t hT] at he; cases he
        · obtain ⟨t0, ht0, -, -, hpr⟩ := back _ t hk hT
          have hS0 : t0.pendingReceiveReply = some rid := hpr.trans hSr
          rcases hShape with h1 | ⟨-, hS1, hCode⟩
          · obtain ⟨-, r2, hr2, hc2⟩ := hInv.pendingReceiveReplyWellFormed.1 _ t0 rid ht0 hS0
            rw [hR0] at hr2
            cases hr2
            rw [h1] at hc2
            cases hc2
          · unfold SystemState.replyStashedAt at hS1
            rw [hCode] at hS1
            simp only [hHid, hTH] at hS1
            obtain ⟨-, hHs⟩ := (TCB.stashTest_eq_true_iff tH rid).mp hS1
            exact hk (hInv.pendingReceiveReplyWellFormed.2.1 _ _ t0 tH rid ht0 hTH hS0 hHs)
      · cases hst

/-- **After the cancel a receive commits, its reply resolution refuses
nothing** (seL4-MCS `receiveIPC`: `cancelIPC(replyTCB)` and then the receive
on the freed reply).  When the receive names a busy reply it may cancel the
holder of (`recvBusyReplyHolderCode`), the cancel it commits first
(`cancelRecvBusyReply`) leaves that reply free, so the reply capability
resolves to it on the cancelled state and the defensive `replyCapInvalid`
refusal cannot fire, under the premises the cancel's bundle theorem takes. -/
theorem resolveRecvReplyId_cancelRecvBusyReply (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (decoded : SyscallDecodeResult) (ec : Concurrency.CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hBudgets : allTimeoutBudgetsNone st)
    (hP : ∀ holder, busyReplyHolder? st tid (recvReplyLookup? gate decoded st) = some holder →
      ¬ holder.isReserved ∧ replyHolderCancelPremises st holder)
    (hBusy : recvBusyReplyHolderCode ctx tid gate decoded st ≠ 0) :
    ∃ rid, resolveRecvReplyId gate decoded (cancelRecvBusyReply ctx tid gate decoded ec st) =
      .ok (some rid) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hBusy
  obtain ⟨hNR, hPk⟩ := hP ⟨k⟩ (recvBusyReplyHolderCode_succ hk)
  have hC : cancelRecvBusyReply ctx tid gate decoded ec st = cancelReplyHolder st ⟨k⟩ ec := by
    unfold cancelRecvBusyReply; rw [hk]
  rw [hC]
  unfold recvBusyReplyHolderCode at hk
  unfold resolveRecvReplyId
  by_cases h0 : (decoded.msgInfo.length == 0) = true
  · simp [h0] at hk
  simp only [h0, Bool.false_eq_true, ↓reduceIte] at hk ⊢
  cases hA : Architecture.SyscallArgDecode.decodeRecvArgs decoded with
  | error e => rw [hA] at hk; simp at hk
  | ok rargs =>
  rw [hA] at hk
  simp only at hk ⊢
  rw [lookupReplyCap_congr_getCNode? _ _ st (cancelReplyHolder_getCNode? st ⟨k⟩ ec hObjInv)]
  cases hLk : lookupReplyCap { gate with capAddr := rargs.replyCPtr } st with
  | error e => rw [hLk] at hk; simp at hk
  | ok p =>
  obtain ⟨cap, rid⟩ := p
  rw [hLk] at hk
  simp only at hk ⊢
  have hCode : busyReplyHolderCode st tid rid = k + 1 := by
    split at hk
    · omega
    · split at hk
      · exact hk
      · omega
  obtain ⟨r, hr, hc, hs⟩ :=
    cancelReplyHolder_frees_reply st tid ⟨k⟩ ec rid hObjInv hInv hBudgets hNR hPk hCode
  exact ⟨rid, by rw [hr]; simp [hc, hs]⟩

end SeLe4n.Kernel
