/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Operations.Endpoint

/-!
# seL4-MCS's `reply_pop` on a context no thread holds

A server's finalisation unbinds the context it holds, bound or on loan, and
returns it to no one (seL4-MCS's `finaliseCap` → `schedContext_unbindTCB`).  A
context lent to that server keeps heading the lender's reply, so the lender —
left blocked on its reply with no server recorded — gets the context back when
that reply is removed or answered: seL4-MCS's `reply_remove` runs `reply_pop`
at the head, sets the context's head to the frame below (`sc->scReply = prev`)
and, the caller holding no context, donates it to the caller
(`schedContext_donate`, which here takes it from no thread).

This module states that pop (`returnUnheldSchedContext`): the donation pop of
`returnDonatedSchedContext` with no holder to unbind.  The context goes to its
caller as the binding the frame below owes (`donationReturnBinding`: the
caller's own at the bottom of the stack, the outer caller's loan above it), the
popped head's links are cleared and the frame below re-headed.  Its refusals are
decided on the pre-state (`unheldReturnCommits`,
`returnUnheldSchedContextResolved_ok_of_commits`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The pop of a context no thread holds, back to `owner`** (seL4-MCS's
`reply_pop` after `schedContext_unbindTCB`): the context, bound to no thread,
is rebound to `owner` with the frame below its head as its new head; the popped
head's links are cleared and the frame below re-headed
(`storeDonationHeadPop`); and `owner`'s binding becomes the one the frame below
owes (`donationReturnBinding`).  Refused, before any write, on a context bound
to a thread, an outer caller or a recipient the donation pop would refuse
(`outerCallerAcceptable`, `donationRecipientAcceptable`), and a head that does
not name the context back. -/
def returnUnheldSchedContext (st : SystemState) (scId : SeLe4n.SchedContextId)
    (owner : SeLe4n.ThreadId) (newOwner? : Option SeLe4n.ThreadId) :
    Except KernelError SystemState :=
  match st.getSchedContext? scId with
  | some sc =>
    if sc.boundThreadCode != 0 then .error .illegalState
    else
    if !outerCallerAcceptable st owner owner newOwner? then .error .invalidArgument
    else
    if !donationRecipientAcceptable st owner then .error .invalidArgument
    else
    match donationHeadOf? st scId sc with
    | .error e => .error e
    | .ok head? =>
      let sc' := donationReturnSchedContext sc owner (head?.bind (fun p => p.2.prev)) newOwner?
      match storeObject scId.toObjId (.schedContext sc') st with
      | .error e => .error e
      | .ok ((), st1) =>
        match storeDonationHeadPop scId head? st1 with
        | .error e => .error e
        | .ok st2 =>
          match lookupTcb st2 owner with
          | none => .error .objectNotFound
          | some ot =>
            let ot' := { ot with
              scBindingScCode := SchedContextBinding.scCode (donationReturnBinding scId newOwner?),
              scBindingOwnerCode := SchedContextBinding.ownerCode (donationReturnBinding scId newOwner?) }
            match storeObject owner.toObjId (.tcb ot') st2 with
            | .error e => .error e
            | .ok ((), st3) =>
              -- The reschedule-SGI accumulator (KSC-1): the recipient's binding
              -- moved, so its key may have.
              .ok (markKeyChangeFrom st st3 owner)
  | none => .error .objectNotFound

/-- **The unheld pop, its outer caller resolved off the reply stack**
(`replyStackOuterCaller?`), as `returnDonatedSchedContextResolved` resolves
it. -/
def returnUnheldSchedContextResolved (st : SystemState) (scId : SeLe4n.SchedContextId)
    (owner : SeLe4n.ThreadId) : Except KernelError SystemState :=
  match replyStackOuterCaller? st scId with
  | .error e => .error e
  | .ok newOwner? => returnUnheldSchedContext st scId owner newOwner?

/-- **Whether the unheld pop commits, read on the state it runs on**: the
reply-stack resolver answers, the context is bound to no thread, the outer
caller and the recipient are acceptable, and the recipient is a stored thread.
Each read is `O(1)`. -/
def unheldReturnCommits (st : SystemState) (scId : SeLe4n.SchedContextId)
    (owner : SeLe4n.ThreadId) : Bool :=
  match replyStackOuterCaller? st scId with
  | .error _ => false
  | .ok newOwner? =>
    match st.getSchedContext? scId with
    | none => false
    | some sc =>
      sc.boundThreadCode == 0 &&
        outerCallerAcceptable st owner owner newOwner? &&
        donationRecipientAcceptable st owner &&
        (lookupTcb st owner).isSome

/-- **What a successful unheld pop is**: the context it read, bound to no thread;
the outer caller and the recipient it accepted; the head it validated; and its
three stores — the context, the head pop, the recipient's binding — then the
reschedule hook. -/
theorem returnUnheldSchedContext_ok_storeChain
    (st st' : SystemState) (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnUnheldSchedContext st scId owner newOwner? = .ok st') :
    ∃ (sc : SchedContext) (head? : Option (SeLe4n.ReplyId × Reply)) (ot : TCB)
      (s1 s2 s3 : SystemState),
      st.objects[scId.toObjId]? = some (.schedContext sc) ∧ sc.boundThreadCode = 0 ∧
      outerCallerAcceptable st owner owner newOwner? = true ∧
      donationRecipientAcceptable st owner = true ∧
      donationHeadOf? st scId sc = .ok head? ∧
      storeObject scId.toObjId
        (.schedContext (donationReturnSchedContext sc owner
          (head?.bind (fun p => p.2.prev)) newOwner?)) st = .ok ((), s1) ∧
      storeDonationHeadPop scId head? s1 = .ok s2 ∧
      lookupTcb s2 owner = some ot ∧
      storeObject owner.toObjId
        (.tcb { ot with
          scBindingScCode := SchedContextBinding.scCode (donationReturnBinding scId newOwner?),
          scBindingOwnerCode := SchedContextBinding.ownerCode (donationReturnBinding scId newOwner?) })
        s2 = .ok ((), s3) ∧
      st' = markKeyChangeFrom st s3 owner := by
  unfold returnUnheldSchedContext SystemState.getSchedContext? at h
  revert h
  cases hObj : st.objects[scId.toObjId]? with
  | none => intro h; cases h
  | some obj => cases obj with
    | schedContext sc =>
      simp only []
      cases hB : sc.boundThreadCode with
      | succ _ => simp only [bne_iff_ne, ne_eq, Nat.add_one_ne_zero, not_false_eq_true, ↓reduceIte]; intro h; cases h
      | zero =>
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      cases hOuterOk : outerCallerAcceptable st owner owner newOwner? with
      | false => simp only [Bool.not_false, if_true]; intro h; cases h
      | true =>
      simp only [Bool.not_true, Bool.false_eq_true, if_false]
      cases hRecipOk : donationRecipientAcceptable st owner with
      | false => simp only [Bool.not_false, if_true]; intro h; cases h
      | true =>
      simp only [Bool.not_true, Bool.false_eq_true, if_false]
      cases hHead : donationHeadOf? st scId sc with
      | error _ => intro h; cases h
      | ok head? =>
        simp only []
        cases hS1 : storeObject scId.toObjId
            (.schedContext (donationReturnSchedContext sc owner
              (head?.bind (fun p => p.2.prev)) newOwner?)) st with
        | error _ => intro h; cases h
        | ok p1 =>
          simp only []
          cases hS2 : storeDonationHeadPop scId head? p1.2 with
          | error _ => intro h; cases h
          | ok s2 =>
            simp only []
            cases hL1 : lookupTcb s2 owner with
            | none => intro h; cases h
            | some ot =>
              simp only []
              cases hS3 : storeObject owner.toObjId
                  (.tcb { ot with
                    scBindingScCode := SchedContextBinding.scCode (donationReturnBinding scId newOwner?),
                    scBindingOwnerCode := SchedContextBinding.ownerCode (donationReturnBinding scId newOwner?) })
                  s2 with
              | error _ => intro h; cases h
              | ok p3 =>
                simp only []
                intro h
                cases h
                exact ⟨sc, head?, ot, p1.2, s2, p3.2, rfl, hB, trivial, trivial, hHead, by rw [← hS1], hS2,
                  hL1, by rw [← hS3], rfl⟩
    | _ => intro h; cases h

/-- **The unheld pop commits on every state `unheldReturnCommits` admits**
(checks before writes): the admission is the pop's whole refusal surface,
decided on its pre-state. -/
theorem returnUnheldSchedContextResolved_ok_of_commits {st : SystemState}
    {scId : SeLe4n.SchedContextId} {owner : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : unheldReturnCommits st scId owner = true) :
    ∃ st', returnUnheldSchedContextResolved st scId owner = .ok st' := by
  unfold unheldReturnCommits at h
  unfold returnUnheldSchedContextResolved
  cases hRes : replyStackOuterCaller? st scId with
  | error e => rw [hRes] at h; cases h
  | ok newOwner? =>
    rw [hRes] at h
    simp only []
    cases hSc : st.getSchedContext? scId with
    | none => rw [hSc] at h; cases h
    | some sc =>
      rw [hSc] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨hB, hOut⟩, hRcp⟩, hOw⟩ := h
      unfold returnUnheldSchedContext
      rw [hSc]
      simp only [hB, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hOut, hRcp, Bool.not_true]
      have hScO := (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc
      have hHead : ∃ head?, donationHeadOf? st scId sc = .ok head? ∧
          ∀ rid r, head? = some (rid, r) →
            st.objects[rid.toObjId]? = some (.reply r) ∧
            ∀ p, r.prev = some p → ∃ b, st.objects[p.toObjId]? = some (.reply b) := by
        unfold replyStackOuterCaller? at hRes
        rw [hSc] at hRes
        simp only [] at hRes
        cases hH : donationHeadOf? st scId sc with
        | error e => rw [hH] at hRes; cases hRes
        | ok head? =>
          refine ⟨head?, rfl, fun rid r hEq => ?_⟩
          subst hEq
          rw [hH] at hRes
          simp only [] at hRes
          have hHeadAt : st.objects[rid.toObjId]? = some (.reply r) := by
            unfold donationHeadOf? at hH
            revert hH
            cases sc.scReply with
            | none => intro hH; cases hH
            | some rid' =>
              simp only []
              cases hG : st.getReply? rid' with
              | none => intro hH; cases hH
              | some r' =>
                simp only []
                split
                · intro hH; cases hH
                · intro hH; cases hH
                  exact (SystemState.getReply?_eq_some_iff _ _ _).mp hG
          refine ⟨hHeadAt, fun p hP => ?_⟩
          rw [hP] at hRes
          simp only [] at hRes
          cases hGb : st.getReply? p with
          | none => rw [hGb] at hRes; cases hRes
          | some b => exact ⟨b, (SystemState.getReply?_eq_some_iff _ _ _).mp hGb⟩
      obtain ⟨head?, hH, hHeadFacts⟩ := hHead
      rw [hH]
      simp only []
      obtain ⟨st1, hS1⟩ : ∃ st1, storeObject scId.toObjId (.schedContext
          (donationReturnSchedContext sc owner (head?.bind (fun p => p.2.prev)) newOwner?))
          st = .ok ((), st1) := ⟨_, rfl⟩
      rw [hS1]
      simp only []
      have hInv1 := storeObject_preserves_objects_invExt st st1 _ _ hInv hS1
      obtain ⟨ow, hOwL⟩ := Option.isSome_iff_exists.mp hOw
      have hOwNR := lookupTcb_some_not_reserved _ _ _ hOwL
      have hOwO : st.objects[owner.toObjId]? = some (.tcb ow) :=
        (SystemState.getTcb?_eq_some_iff _ _ _).mp (by
          unfold lookupTcb at hOwL; rw [if_neg hOwNR] at hOwL; exact hOwL)
      have keep1 : ∀ (k : SeLe4n.ObjId) (t : TCB), st.objects[k]? = some (KernelObject.tcb t) →
          st1.objects[k]? = some (KernelObject.tcb t) := by
        intro k t hk
        have hne : k ≠ scId.toObjId := by
          intro e; subst e; rw [hScO] at hk; cases hk
        rw [storeObject_objects_ne st st1 _ _ _ hne hInv hS1]; exact hk
      obtain ⟨st2, hS2, keep2⟩ : ∃ st2, storeDonationHeadPop scId head? st1 = .ok st2 ∧
          ∀ (k : SeLe4n.ObjId) (t : TCB), st1.objects[k]? = some (KernelObject.tcb t) →
            st2.objects[k]? = some (KernelObject.tcb t) := by
        cases hHd : head? with
        | none => exact ⟨st1, rfl, fun _ _ h => h⟩
        | some pr =>
          obtain ⟨rid, r⟩ := pr
          obtain ⟨hHeadAt, hPrev⟩ := hHeadFacts rid r hHd
          have hne : rid.toObjId ≠ scId.toObjId := by
            intro e; rw [e, hScO] at hHeadAt; cases hHeadAt
          have hHeadAt1 : st1.objects[rid.toObjId]? = some (.reply r) := by
            rw [storeObject_objects_ne st st1 _ _ _ hne hInv hS1]; exact hHeadAt
          have hPrev1 : ∀ p, r.prev = some p → ∃ b, st1.objects[p.toObjId]? = some (.reply b) := by
            intro p hp
            obtain ⟨b, hb⟩ := hPrev p hp
            have hne' : p.toObjId ≠ scId.toObjId := by
              intro e; rw [e, hScO] at hb; cases hb
            exact ⟨b, by rw [storeObject_objects_ne st st1 _ _ _ hne' hInv hS1]; exact hb⟩
          obtain ⟨st2, h2, hk⟩ := storeDonationHeadPop_ok_of (scId := scId) hInv1 hHeadAt1 hPrev1
          exact ⟨st2, h2, fun k t hkt => hk k _ hkt (fun _ h => by cases h)⟩
      rw [hS2]
      simp only []
      have hOw2 : lookupTcb st2 owner = some ow := by
        unfold lookupTcb; rw [if_neg hOwNR]
        exact (SystemState.getTcb?_eq_some_iff _ _ _).mpr (keep2 _ _ (keep1 _ _ hOwO))
      rw [hOw2]
      exact ⟨_, rfl⟩

end SeLe4n.Kernel
