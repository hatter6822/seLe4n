-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ReschedulePendingArms.Scheduling
import SeLe4n.Kernel.IPC.Invariant.CancellationBundle

/-!
# IPC cancellation and the donation return cover

The KSC-1 / HAL-3 row of `docs/REGISTERED_DEBT.md`, PR B2.  The donation return
rebinds two threads and ends in a key hook for each; every other step of the IPC
teardown (`cancelIpcBlocking`) moves no key input and no scheduler slot.  The
suspend and retype arms and the reply path compose these.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId SgiKind)

/-! ### Reading the key inputs off the two typed lookups -/

/-- **Equal key fields at every TCB and equal deadlines at every scheduling
context are equal key inputs.**  Every object slot is some thread's and some
context's slot, so the two typed readings decide what the slot contributes. -/
theorem keyInputsEq_of_lookups {pre post : SystemState}
    (hT : ∀ t, (post.getTcb? t).map tcbKeyFields = (pre.getTcb? t).map tcbKeyFields)
    (hS : ∀ s, (post.getSchedContext? s).map (·.deadline) =
      (pre.getSchedContext? s).map (·.deadline)) :
    keyInputsEq pre post := by
  intro oid
  have hT' := hT (SeLe4n.ThreadId.ofNat oid.toNat)
  have hS' := hS (SeLe4n.SchedContextId.ofNat oid.toNat)
  have hTo : (SeLe4n.ThreadId.ofNat oid.toNat).toObjId = oid := rfl
  have hSo : (SeLe4n.SchedContextId.ofNat oid.toNat).toObjId = oid := rfl
  unfold SystemState.getTcb? at hT'
  unfold SystemState.getSchedContext? at hS'
  rw [hTo] at hT'
  rw [hSo] at hS'
  cases hq : post.objects[oid]? with
  | none =>
    cases hp : pre.objects[oid]? with
    | none => rfl
    | some o => rw [hq, hp] at hT' hS'; cases o <;> simp_all [keyInputsOf]
  | some oq =>
    cases hp : pre.objects[oid]? with
    | none => rw [hq, hp] at hT' hS'; cases oq <;> simp_all [keyInputsOf]
    | some op =>
      rw [hq, hp] at hT' hS'
      cases oq <;> cases op <;> simp_all [keyInputsOf, tcbKeyFields]

/-- Whole-lookup equalities, the form most frame lemmas state. -/
theorem keyInputsEq_of_lookups_eq {pre post : SystemState}
    (hT : ∀ t, post.getTcb? t = pre.getTcb? t)
    (hS : ∀ s, post.getSchedContext? s = pre.getSchedContext? s) :
    keyInputsEq pre post :=
  keyInputsEq_of_lookups (fun t => by rw [hT]) (fun s => by rw [hS])

/-- A TCB stored over `tid`'s TCB moves no key input but `tid`'s. -/
theorem keyInputsEqExcept_storeObject_tcb {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {t t' : TCB} (hInv : st.objects.invExt)
    (hPre : st.objects[tid.toObjId]? = some (.tcb t))
    (hStore : storeObject tid.toObjId (.tcb t') st = .ok ((), st')) :
    keyInputsEqExcept tid st st' :=
  ⟨fun oid hne => (by rw [storeObject_objects_ne st st' tid.toObjId oid _ hne hInv hStore]),
   fun sc h => (by rw [hPre] at h; cases h),
   fun sc h => (by rw [storeObject_objects_eq st st' _ _ hInv hStore] at h; cases h)⟩

/-! ### The binding writers' pair of hooks -/

/-- **Two key writes ended in their two hooks cover.**  A step that rebinds `a`
and `b`, moves no other thread's key and no scheduler field, then runs the hook
for each against its pre-state, covers: each moved key is flagged by its own
hook (the second hook moves no slot and no key, so `a`'s flags survive it). -/
theorem stepCovers_markKeyChangeFrom_pair {e : CoreId} {pre m : SystemState}
    {a b : SeLe4n.ThreadId}
    (hKeys : ∀ t, t ≠ a → t ≠ b → schedKeyView m t = schedKeyView pre t)
    (hSched : m.scheduler = pre.scheduler) :
    stepCovers e pre (markKeyChangeFrom pre (markKeyChangeFrom pre m a) b) := by
  refine ⟨reschedulePendingCovers_of_keyChangeFlagged (fun t => ?_)
    (fun c _ => Or.inr ⟨fun t ht => ?_, ?_⟩), fun c _ h => ?_⟩
  · by_cases hb : t = b
    · subst hb; exact Or.inr (markKeyChangeFrom_flagged _ _ _)
    by_cases ha : t = a
    · subst ha
      refine Or.inr (keyChangeFlagged_of_flagOnly (markKeyChangeFrom_flagged pre m t)
        (fun c => ?_) (fun c => ?_) (fun t' => ?_)
        (fun c h => markKeyChangeFrom_reschedulePendingOnCore_mono _ _ _ _ h))
      · simp only [markKeyChangeFrom_runQueueOnCore]
      · simp only [markKeyChangeFrom_currentOnCore]
      · simp only [schedKeyView_markKeyChangeFrom]
    · left; simp only [schedKeyView_markKeyChangeFrom]; exact hKeys t ha hb
  · simp only [markKeyChangeFrom_runQueueOnCore] at ht; rw [hSched] at ht; exact ht
  · simp only [markKeyChangeFrom_currentOnCore]; rw [hSched]
  · apply markKeyChangeFrom_reschedulePendingOnCore_mono
    apply markKeyChangeFrom_reschedulePendingOnCore_mono
    rw [hSched]; exact h

/-! ### The donation return -/

/-- The reply-stack pop moves no key input. -/
theorem storeDonationHeadPop_keyInputsEq {scId : SeLe4n.SchedContextId}
    {head? : Option (SeLe4n.ReplyId × Reply)} {st st' : SystemState}
    (hInv : st.objects.invExt) (h : storeDonationHeadPop scId head? st = .ok st') :
    keyInputsEq st st' := by
  rcases storeDonationHeadPop_cases h with ⟨_, rfl⟩ | ⟨rid, r, s1, _, hC, hR⟩
  · exact keyInputsEq_refl _
  · have hInv1 := storeDonationHeadClear_preserves_objects_invExt hInv hC
    exact keyInputsEq_trans
      (keyInputsEq_of_lookups_eq (storeDonationHeadClear_getTcb?_eq hInv hC)
        (storeDonationHeadClear_getSchedContext?_eq hInv hC))
      (keyInputsEq_of_lookups_eq (storeReplyReHead_getTcb?_eq hInv1 hR)
        (storeReplyReHead_getSchedContext?_eq hInv1 hR))

/-- The return's store chain moves no key but the two rebound threads', and no
scheduler field. -/
theorem returnStoreChain_keys {st s1 s2 s3 s4 : SystemState} {scId : SeLe4n.SchedContextId}
    {sc sc' : SchedContext} {head? : Option (SeLe4n.ReplyId × Reply)}
    {owner server : SeLe4n.ThreadId} {ct ct' stcb stcb' : TCB}
    (hInv : st.objects.invExt)
    (hObj : st.objects[scId.toObjId]? = some (.schedContext sc))
    (hDl : sc'.deadline = sc.deadline)
    (hS1 : storeObject scId.toObjId (.schedContext sc') st = .ok ((), s1))
    (hS2 : storeDonationHeadPop scId head? s1 = .ok s2)
    (hL1 : lookupTcb s2 owner = some ct)
    (hS3 : storeObject owner.toObjId (.tcb ct') s2 = .ok ((), s3))
    (hL2 : lookupTcb s3 server = some stcb)
    (hS4 : storeObject server.toObjId (.tcb stcb') s3 = .ok ((), s4)) :
    (∀ t, t ≠ owner → t ≠ server → schedKeyView s4 t = schedKeyView st t) ∧
      s4.scheduler = st.scheduler ∧ s4.objects.invExt := by
  have hInv1 := storeObject_preserves_objects_invExt _ _ _ _ hInv hS1
  have hInv2 := storeDonationHeadPop_preserves_objects_invExt hInv1 hS2
  have hInv3 := storeObject_preserves_objects_invExt _ _ _ _ hInv2 hS3
  have k1 : keyInputsEq st s1 :=
    keyInputsEq_storeObject hInv hS1 (by rw [hObj]; simp only [keyInputsOf, hDl])
  have k2 := keyInputsEq_trans k1 (storeDonationHeadPop_keyInputsEq hInv1 hS2)
  have k3 := keyInputsEqExcept_storeObject_tcb hInv2 (lookupTcb_some_objects _ _ _ hL1) hS3
  have k4 := keyInputsEqExcept_storeObject_tcb hInv3 (lookupTcb_some_objects _ _ _ hL2) hS4
  refine ⟨fun t ho hs => ?_, ?_, storeObject_preserves_objects_invExt _ _ _ _ hInv3 hS4⟩
  · rw [schedKeyView_eq_of_keyInputsEqExcept k4 hs, schedKeyView_eq_of_keyInputsEqExcept k3 ho,
      schedKeyView_eq_of_keyInputsEq k2]
  · rw [storeObject_scheduler_eq _ _ _ _ hS4, storeObject_scheduler_eq _ _ _ _ hS3,
      storeDonationHeadPop_scheduler_eq hS2, storeObject_scheduler_eq _ _ _ _ hS1]

/-- **The donation return covers**: it rebinds the context's holder and its
recipient and ends in a key hook for each. -/
theorem returnDonatedSchedContext_stepCovers (e : CoreId) {st st' : SystemState}
    {serverTid : SeLe4n.ThreadId} {scId : SeLe4n.SchedContextId}
    {originalOwner : SeLe4n.ThreadId} {newOwner? : Option SeLe4n.ThreadId}
    (hInv : st.objects.invExt)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    stepCovers e st st' ∧ st'.objects.invExt := by
  unfold returnDonatedSchedContext SystemState.getSchedContext? at h
  revert h
  cases hObj : st.objects[scId.toObjId]? with
  | none => intro h; cases h
  | some obj => cases obj with
    | schedContext sc =>
      simp only []
      split
      · intro h; cases h
      cases outerCallerAcceptable st serverTid originalOwner newOwner? with
      | false => simp only [Bool.not_false, if_true]; intro h; cases h
      | true =>
      simp only [Bool.not_true, Bool.false_eq_true, if_false]
      cases donationRecipientAcceptable st originalOwner with
      | false => simp only [Bool.not_false, if_true]; intro h; cases h
      | true =>
      simp only [Bool.not_true, Bool.false_eq_true, if_false]
      cases donationHeadOf? st scId sc with
      | error _ => intro h; cases h
      | ok head? =>
        simp only []
        cases hS1 : storeObject scId.toObjId
            (.schedContext (donationReturnSchedContext sc originalOwner
              (head?.bind (fun p => p.2.prev)) newOwner?)) st with
        | error _ => intro h; cases h
        | ok p1 =>
          simp only []
          cases hS2 : storeDonationHeadPop scId head? p1.2 with
          | error _ => intro h; cases h
          | ok s2 =>
            simp only []
            cases hL1 : lookupTcb s2 originalOwner with
            | none => intro h; cases h
            | some clientTcb =>
              simp only []
              cases hS3 : storeObject originalOwner.toObjId
                  (.tcb { clientTcb with
                            schedContextBinding := donationReturnBinding scId newOwner? }) s2 with
              | error _ => intro h; cases h
              | ok p3 =>
                simp only []
                cases hL2 : lookupTcb p3.2 serverTid with
                | none => intro h; cases h
                | some serverTcb =>
                  simp only []
                  cases hS4 : storeObject serverTid.toObjId
                      (.tcb { serverTcb with schedContextBinding := .unbound }) p3.2 with
                  | error _ => intro h; cases h
                  | ok p4 =>
                    simp only []
                    intro h
                    cases h
                    obtain ⟨hK, hS, hI⟩ := returnStoreChain_keys
                      (sc' := donationReturnSchedContext sc originalOwner
                        (head?.bind (fun p => p.2.prev)) newOwner?) hInv hObj rfl
                      (by rw [← hS1]) hS2 hL1 (by rw [← hS3]) hL2 (by rw [← hS4])
                    exact ⟨stepCovers_markKeyChangeFrom_pair
                      (fun t ho hs => hK t ho hs) hS,
                      by simp only [markKeyChangeFrom_objects]; exact hI⟩
    | _ => intro h; cases h

/-- The resolved return covers. -/
theorem returnDonatedSchedContextResolved_stepCovers (e : CoreId) {st st' : SystemState}
    {serverTid : SeLe4n.ThreadId} {scId : SeLe4n.SchedContextId}
    {originalOwner : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : returnDonatedSchedContextResolved st serverTid scId originalOwner = .ok st') :
    stepCovers e st st' ∧ st'.objects.invExt :=
  returnDonatedSchedContextResolved_lift (P := fun s => stepCovers e st s ∧ s.objects.invExt) h
    (fun _ _ hPop => returnDonatedSchedContext_stepCovers e hInv hPop)

/-- **Slot refinement up to the key fields is equal key inputs**: every TCB
survives with its key fields and every scheduling context with its deadline, and
neither kind appears where it was not. -/
theorem keyInputsEq_of_slots {pre post : SystemState}
    (hTf : ∀ (a : SeLe4n.ObjId) (t : TCB), pre.objects[a]? = some (.tcb t) →
      ∃ t', post.objects[a]? = some (.tcb t') ∧ tcbKeyFields t' = tcbKeyFields t)
    (hTb : ∀ (a : SeLe4n.ObjId) (t' : TCB), post.objects[a]? = some (.tcb t') →
      ∃ t, pre.objects[a]? = some (.tcb t))
    (hSf : ∀ (a : SeLe4n.ObjId) (sc : SchedContext), pre.objects[a]? = some (.schedContext sc) →
      ∃ sc', post.objects[a]? = some (.schedContext sc') ∧ sc'.deadline = sc.deadline)
    (hSb : ∀ (a : SeLe4n.ObjId) (sc' : SchedContext), post.objects[a]? = some (.schedContext sc') →
      ∃ sc, pre.objects[a]? = some (.schedContext sc)) :
    keyInputsEq pre post := by
  intro oid
  have hPost : (∀ t, pre.objects[oid]? ≠ some (.tcb t)) →
      (∀ sc, pre.objects[oid]? ≠ some (.schedContext sc)) →
      keyInputsOf post.objects[oid]? = none := by
    intro hNT hNS
    cases hq : post.objects[oid]? with
    | none => rfl
    | some oq =>
      cases oq with
      | tcb t' => obtain ⟨t, h⟩ := hTb oid t' hq; exact absurd h (hNT t)
      | schedContext sc' => obtain ⟨sc, h⟩ := hSb oid sc' hq; exact absurd h (hNS sc)
      | _ => rfl
  cases hp : pre.objects[oid]? with
  | none => exact hPost (fun _ h => by rw [hp] at h; cases h) (fun _ h => by rw [hp] at h; cases h)
  | some op =>
    cases op with
    | tcb t =>
      obtain ⟨t', hq, hk⟩ := hTf oid t hp
      rw [hq]; simp only [tcbKeyFields, Prod.mk.injEq] at hk; simp only [keyInputsOf, hk]
    | schedContext sc =>
      obtain ⟨sc', hq, hd⟩ := hSf oid sc hp
      rw [hq]; simp only [keyInputsOf, hd]
    | _ => exact hPost (fun _ h => by rw [hp] at h; cases h) (fun _ h => by rw [hp] at h; cases h)

/-! ### The teardown's object-only steps -/

/-- The restore clears IPC fields and stages a frame: no key field. -/
theorem restoreToReadyStaging_keyInputsEq (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (hInv : st.objects.invExt) :
    keyInputsEq st (Lifecycle.Suspend.restoreToReadyStaging st tid frame) := by
  unfold Lifecycle.Suspend.restoreToReadyStaging
  exact keyInputsEq_updateTcb hInv (fun t => by
    cases frame <;> simp [tcbKeyFields, TCB.withReturnFrame])

/-- The endpoint-queue removal rewrites queue links only. -/
theorem endpointQueueRemove_keyInputsEq {epId : SeLe4n.ObjId} {isRecvQ : Bool}
    {tid : SeLe4n.ThreadId} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : endpointQueueRemove epId isRecvQ tid st = .ok st') :
    keyInputsEq st st' := by
  have hLF : ∀ (t : TCB) qp qpp qn,
      tcbKeyFields { t with queuePrev := qp, queuePPrev := qpp, queueNext := qn } =
        tcbKeyFields t := fun _ _ _ _ => rfl
  refine keyInputsEq_of_slots (fun a t ha => ?_) (fun a t' ha => ?_)
    (fun a sc ha => ⟨sc, endpointQueueRemove_schedContext_forward _ _ _ _ _ hInv h a sc ha, rfl⟩)
    (fun a sc ha => ⟨sc, endpointQueueRemove_schedContext_backward _ _ _ _ _ hInv h a sc ha⟩)
  · rw [RHTable_getElem?_eq_get?] at ha
    obtain ⟨t', h', hk⟩ := endpointQueueRemove_getTcb_upToField tcbKeyFields hLF _ _ _ _ _ hInv h a t ha
    rw [← RHTable_getElem?_eq_get?] at h'
    exact ⟨t', h', hk.symm⟩
  · obtain ⟨t, h', _⟩ :=
      endpointQueueRemove_getTcb_backward_upToField tcbKeyFields hLF _ _ _ _ _ hInv h a t' ha
    exact ⟨t, h'⟩

/-- The holder's abort removes it from its endpoint queue and readies it: no
key field. -/
theorem abortHolderPendingIpc_keyInputsEq (st : SystemState) (holder : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    keyInputsEq st (Lifecycle.Suspend.abortHolderPendingIpc st holder) := by
  unfold Lifecycle.Suspend.abortHolderPendingIpc
  cases lookupTcb st holder with
  | none => exact keyInputsEq_refl _
  | some holderTcb =>
    simp only []
    split
    all_goals first
      | exact keyInputsEq_refl _
      | (split
         · rename_i st' hAb
           unfold abortPendingIpcOnEndpoint at hAb
           split at hAb
           · cases hAb
           · rename_i st1 hEQR
             have hInv1 := endpointQueueRemove_preserves_objects_invExt _ _ _ _ _ hInv hEQR
             split at hAb
             · cases hAb
             · rename_i tcb hLook
               dsimp only at hAb
               split at hAb
               · cases hAb
               · rename_i hS
                 cases hAb
                 refine keyInputsEq_trans (endpointQueueRemove_keyInputsEq hInv hEQR)
                   (keyInputsEq_storeObject hInv1 hS ?_)
                 rw [lookupTcb_some_objects _ _ _ hLook]
                 simp [keyInputsOf, TCB.withReturnFrame]
         · exact keyInputsEq_refl _)

/-- The caller-link teardown consumes a Reply and clears the caller's reply
object: no key field. -/
theorem consumeCallerReply_keyInputsEq {st st' : SystemState} {caller : SeLe4n.ThreadId}
    {rid : SeLe4n.ReplyId} (hInv : st.objects.invExt)
    (h : SystemState.consumeCallerReply caller rid st = .ok ((), st')) :
    keyInputsEq st st' := by
  unfold SystemState.consumeCallerReply at h
  cases hC : SystemState.consumeReply rid st with
  | error e => rw [hC] at h; cases h
  | ok p =>
    obtain ⟨⟨⟩, st1⟩ := p
    rw [hC] at h
    have k1 : keyInputsEq st st1 ∧ st1.objects.invExt := by
      unfold SystemState.consumeReply at hC
      cases hR : st.getReply? rid with
      | none => rw [hR] at hC; cases hC; exact ⟨keyInputsEq_refl _, hInv⟩
      | some r =>
        rw [hR] at hC
        exact ⟨keyInputsEq_storeObject hInv hC
            (by rw [(SystemState.getReply?_eq_some_iff st rid r).mp hR]; rfl),
          storeObject_preserves_objects_invExt _ _ _ _ hInv hC⟩
    simp only [] at h
    cases hT : st1.getTcb? caller with
    | none => rw [hT] at h; cases h; exact k1.1
    | some tcb =>
      rw [hT] at h
      exact keyInputsEq_trans k1.1 (keyInputsEq_storeObject k1.2 h
        (by rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp hT]; rfl))

theorem consumeReplyLink_keyInputsEq (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : st.objects.invExt) :
    keyInputsEq st (Lifecycle.Suspend.consumeReplyLink st tid tcb) := by
  unfold Lifecycle.Suspend.consumeReplyLink
  cases tcb.replyObject with
  | none => exact keyInputsEq_refl _
  | some rid => exact consumeCallerReply_keyInputsEq hInv (SystemState.consumeCallerReply_eq_link st tid rid)

theorem spliceThreadReplyFrameOut_keyInputsEq (st : SystemState) (tcb : TCB)
    (hInv : st.objects.invExt) : keyInputsEq st (spliceThreadReplyFrameOut st tcb) :=
  keyInputsEq_of_lookups_eq (spliceThreadReplyFrameOut_getTcb?_eq st tcb hInv)
    (spliceThreadReplyFrameOut_getSchedContext?_eq st tcb hInv)

theorem removeFromAllEndpointQueues_keyInputsEq (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : keyInputsEq st (removeFromAllEndpointQueues st tid) :=
  keyInputsEq_of_lookups
    (fun t => by
      rw [removeFromAllEndpointQueues_getTcb?_eq_splice st tid hInv t]
      exact spliceOutMidQueueNode_tcbField_frame tcbKeyFields (fun _ _ _ _ => rfl) st tid hInv t)
    (fun s => by rw [removeFromAllEndpointQueues_getSchedContext?_eq st tid hInv s])

theorem removeFromAllNotificationWaitLists_keyInputsEq (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : keyInputsEq st (removeFromAllNotificationWaitLists st tid) :=
  keyInputsEq_of_lookups_eq (removeFromAllNotificationWaitLists_getTcb?_eq st tid hInv)
    (removeFromAllNotificationWaitLists_getSchedContext?_eq st tid hInv)

/-! ### The teardown covers -/

/-- An object-only step that moves no key input covers. -/
theorem stepCovers_of_keys_sched {e : CoreId} {pre post : SystemState}
    (hKeys : keyInputsEq pre post) (hSched : post.scheduler = pre.scheduler) :
    stepCovers e pre post :=
  stepCovers_of_scheduler_eq hKeys hSched

/-- **The cancelled caller's reclaim covers**: the holder's abort is object-only
and moves no key, and the return ends in its two hooks. -/
theorem returnDonationToCancelledCaller_stepCovers (e : CoreId) (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hInv : st.objects.invExt) :
    stepCovers e st (Lifecycle.Suspend.returnDonationToCancelledCaller st tid tcb) := by
  unfold Lifecycle.Suspend.returnDonationToCancelledCaller
  split
  · rename_i scId holder _ _ _
    have hA := Lifecycle.Suspend.abortHolderPendingIpc_preserves_objects_invExt st holder hInv
    split
    · rename_i st' hRet
      exact stepCovers_trans
        (stepCovers_of_keys_sched (abortHolderPendingIpc_keyInputsEq st holder hInv)
          (Lifecycle.Suspend.abortHolderPendingIpc_scheduler_eq st holder))
        (returnDonatedSchedContextResolved_stepCovers e hA hRet).1
    · exact stepCovers_refl e st
  · exact stepCovers_refl e st

/-- **The IPC teardown covers**: every arm but the reply arm is object-only and
moves no key; the reply arm's reclaim ends in its hooks, and what follows it is
object-only again. -/
theorem cancelIpcBlocking_stepCovers (e : CoreId) (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (hInv : st.objects.invExt) :
    stepCovers e st (Lifecycle.Suspend.cancelIpcBlocking st tid tcb) := by
  have hRestore : ∀ s : SystemState, s.objects.invExt →
      stepCovers e s (Lifecycle.Suspend.restoreToReadyCancelled s tid) := fun s hs =>
    stepCovers_of_keys_sched (restoreToReadyStaging_keyInputsEq s tid _ hs)
      (Lifecycle.Suspend.restoreToReadyCancelled_scheduler_eq s tid)
  have hEp : stepCovers e st (Lifecycle.Suspend.restoreToReadyCancelled
      (removeFromAllEndpointQueues st tid) tid) :=
    stepCovers_trans
      (stepCovers_of_keys_sched (removeFromAllEndpointQueues_keyInputsEq st tid hInv)
        (removeFromAllEndpointQueues_scheduler_eq st tid))
      (hRestore _ (removeFromAllEndpointQueues_preserves_objects_invExt st tid hInv))
  unfold Lifecycle.Suspend.cancelIpcBlocking
  cases tcb.ipcState with
  | ready => exact stepCovers_refl e st
  | blockedOnSend _ => exact hEp
  | blockedOnReceive _ => exact hEp
  | blockedOnCall _ => exact hEp
  | blockedOnNotification _ =>
    exact stepCovers_trans
      (stepCovers_of_keys_sched (removeFromAllNotificationWaitLists_keyInputsEq st tid hInv)
        (removeFromAllNotificationWaitLists_scheduler_eq st tid))
      (hRestore _ (removeFromAllNotificationWaitLists_preserves_objects_invExt st tid hInv))
  | blockedOnReply _ _ =>
    have h1 := Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt
      st tid tcb hInv
    have h2 := spliceThreadReplyFrameOut_preserves_objects_invExt _ tcb h1
    have h3 := Lifecycle.Suspend.restoreToReadyStaging_invExt _ tid (some Architecture.cancelledIpcFrame) h2
    refine stepCovers_trans (returnDonationToCancelledCaller_stepCovers e st tid tcb hInv)
      (stepCovers_trans (stepCovers_of_keys_sched (spliceThreadReplyFrameOut_keyInputsEq _ tcb h1)
        (spliceThreadReplyFrameOut_scheduler_eq _ tcb))
      (stepCovers_trans (hRestore _ h2)
        (stepCovers_of_keys_sched (consumeReplyLink_keyInputsEq _ tid tcb h3)
          (Lifecycle.Suspend.consumeReplyLink_scheduler_eq _ tid tcb))))

/-! ### The donation cancellations -/

/-- **One key write ended in its hook covers**: the write moved no other key
and no run-queue or current slot, and lowered no flag. -/
theorem stepCovers_markKeyChangeFrom {e : CoreId} {pre m : SystemState} {a : SeLe4n.ThreadId}
    (hKeys : ∀ t, t ≠ a → schedKeyView m t = schedKeyView pre t)
    (hRq : ∀ c, m.scheduler.runQueueOnCore c = pre.scheduler.runQueueOnCore c)
    (hCur : ∀ c, m.scheduler.currentOnCore c = pre.scheduler.currentOnCore c)
    (hFl : ∀ c, pre.scheduler.reschedulePendingOnCore c = true →
      m.scheduler.reschedulePendingOnCore c = true) :
    stepCovers e pre (markKeyChangeFrom pre m a) := by
  refine ⟨reschedulePendingCovers_of_keyChangeFlagged (fun t => ?_)
    (fun c _ => Or.inr ⟨fun t ht => ?_, ?_⟩), fun c _ h => ?_⟩
  · by_cases ha : t = a
    · subst ha; exact Or.inr (markKeyChangeFrom_flagged _ _ _)
    · left; simp only [schedKeyView_markKeyChangeFrom]; exact hKeys t ha
  · simp only [markKeyChangeFrom_runQueueOnCore] at ht; rw [hRq] at ht; exact ht
  · simp only [markKeyChangeFrom_currentOnCore]; exact hCur c
  · exact markKeyChangeFrom_reschedulePendingOnCore_mono _ _ _ _ (hFl c h)

/-- A context write that keeps the deadline moves no key input. -/
theorem updateSchedContext_keyInputsEq (st : SystemState) (scId : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext) (hInv : st.objects.invExt)
    (hF : ∀ sc, (f sc).deadline = sc.deadline) :
    keyInputsEq st (st.updateSchedContext scId f) :=
  keyInputsEq_of_lookups (fun t => by rw [SystemState.updateSchedContext_getTcb? st scId f hInv t])
    (fun s => by
      by_cases h : scId.toObjId = s.toObjId
      · obtain rfl := SeLe4n.SchedContextId.toObjId_injective _ _ h
        rw [SystemState.updateSchedContext_getSchedContext?_self st scId f hInv]
        cases st.getSchedContext? scId <;> simp [hF]
      · rw [SystemState.updateSchedContext_getSchedContext?_ne st scId f hInv s h])

/-- A TCB update keeps every other thread's key. -/
theorem schedKeyView_updateTcb_ne (s : SystemState) (tid : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : s.objects.invExt) {t : SeLe4n.ThreadId} (ht : t ≠ tid) :
    schedKeyView (s.updateTcb tid f) t = schedKeyView s t := by
  cases hT : s.getTcb? tid with
  | none => rw [SystemState.updateTcb_eq_self_of_none hT]
  | some _ =>
    exact schedKeyView_eq_of_keyInputsEqExcept (keyInputsEqExcept_updateTcb hInv (by rw [hT]; rfl)) ht

/-- **The bound unbind covers**: the context write keeps its deadline, the purge
writes a replenish queue, and the victim's rebind ends in its hook. -/
theorem cancelBoundDonationOnCore_stepCovers (e : CoreId) {st st' : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB} {rqCore : CoreId} (hInv : st.objects.invExt)
    (h : cancelBoundDonationOnCore st tid tcb rqCore = .ok st') :
    stepCovers e st st' ∧ st'.objects.invExt := by
  unfold cancelBoundDonationOnCore at h
  split at h
  · rename_i scId _
    injection h with h
    subst h
    have hInv1 := SystemState.updateSchedContext_preserves_objects_invExt st scId
      (fun sc => { sc with boundThread := none, isActive := false, donationOrigin := none }) hInv
    have k1 := updateSchedContext_keyInputsEq st scId
      (fun sc => { sc with boundThread := none, isActive := false, donationOrigin := none }) hInv
      (fun _ => rfl)
    have hS1 := SystemState.updateSchedContext_scheduler st scId
      (fun sc => { sc with boundThread := none, isActive := false, donationOrigin := none })
    refine ⟨stepCovers_markKeyChangeFrom (fun t ht => ?_) (fun c => ?_) (fun c => ?_)
      (fun c hc => ?_), ?_⟩
    · rw [schedKeyView_updateTcb_ne _ tid _ ?_ ht]
      · exact (schedKeyView_eq_of_keyInputsEq (keyInputsEq_of_objects_eq rfl) t).trans
          (schedKeyView_eq_of_keyInputsEq k1 t)
      · exact hInv1
    · rw [SystemState.updateTcb_scheduler]; simp only [SchedulerState.setReplenishQueueOnCore_runQueueOnCore]; rw [hS1]
    · rw [SystemState.updateTcb_scheduler]; simp only [SchedulerState.setReplenishQueueOnCore_currentOnCore]; rw [hS1]
    · rw [SystemState.updateTcb_scheduler]; simp only [SchedulerState.setReplenishQueueOnCore_reschedulePendingOnCore]; rw [hS1]; exact hc
    · simp only [markKeyChangeFrom_objects]
      exact SystemState.updateTcb_preserves_objects_invExt _ tid _ hInv1
  · cases h

/-- The donated cleanup is the return or the identity. -/
theorem cleanupDonatedSchedContext_stepCovers (e : CoreId) {st st' : SystemState}
    {tid : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : cleanupDonatedSchedContext st tid = .ok st') :
    stepCovers e st st' ∧ st'.objects.invExt := by
  unfold cleanupDonatedSchedContext at h
  split at h
  · cases h; exact ⟨stepCovers_refl e _, hInv⟩
  · split at h
    · exact returnDonatedSchedContextResolved_stepCovers e hInv h
    · cases h; exact ⟨stepCovers_refl e _, hInv⟩

/-- **The donated cancellation covers**: the return, then the replenishment
migration, which moves no slot. -/
theorem cancelDonatedDonationOnCore_stepCovers (e : CoreId) {st st' : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB} (hInv : st.objects.invExt)
    (h : cancelDonatedDonationOnCore st tid tcb = .ok st') :
    stepCovers e st st' ∧ st'.objects.invExt := by
  unfold cancelDonatedDonationOnCore at h
  split at h
  · split at h
    · cases h
    · rename_i sMid hC
      cases h
      obtain ⟨h1, hI⟩ := cleanupDonatedSchedContext_stepCovers e hInv hC
      exact ⟨stepCovers_trans h1 (migrateSchedContextReplenishment_stepCovers e _ _ _ _),
        by rw [migrateSchedContextReplenishment_objects]; exact hI⟩
  · cases h

end SeLe4n.Kernel
