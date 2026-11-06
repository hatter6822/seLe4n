/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Operations.Endpoint
import SeLe4n.Kernel.SchedContext.ReturnSettle

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

/-- **seL4-MCS's `reply_pop` at a reply heading a context no thread holds**,
keyed on the reply `rid` and the caller `target` it answers (WS-ZA ZA6.34).  A
server's finalisation unbinds the context it held and returns it to no one, so
the reply its lender is blocked on keeps heading that context; answering or
removing that reply pops the head (`sc->scReply = prev`) and, the caller
holding no context, donates it to the caller (`schedContext_donate`), whose
replenishments the settle places on `home`.  The identity where the reply heads
no context; the pop's own refusal otherwise (it refuses a context bound to a
thread, so this arm is the unheld one).  The recipient is the answered caller,
as in `reply_pop`. -/
def popUnheldReplyHead (st : SystemState) (rid : SeLe4n.ReplyId) (target : SeLe4n.ThreadId)
    (home : Concurrency.CoreId) : Except KernelError SystemState :=
  match replyFrameHeadContext? st rid with
  | none => .ok st
  | some scId =>
    match returnUnheldSchedContextResolved st scId target with
    | .error e => .error e
    | .ok st' => .ok (SchedContextOps.settleReturnedContext st' home scId)

/-- A reply heading no context pops nothing. -/
@[simp] theorem popUnheldReplyHead_of_no_head (st : SystemState) (rid : SeLe4n.ReplyId)
    (target : SeLe4n.ThreadId) (home : Concurrency.CoreId) (h : replyFrameHeadContext? st rid = none) :
    popUnheldReplyHead st rid target home = .ok st := by
  unfold popUnheldReplyHead; rw [h]

/-- **What a successful pop at an unheld head is**: the identity where the reply
heads no context, or the unheld pop of the context it heads, settled on `home`. -/
theorem popUnheldReplyHead_ok_cases {st st' : SystemState} {rid : SeLe4n.ReplyId}
    {target : SeLe4n.ThreadId} {home : Concurrency.CoreId}
    (h : popUnheldReplyHead st rid target home = .ok st') :
    (replyFrameHeadContext? st rid = none ∧ st' = st) ∨
    ∃ (scId : SeLe4n.SchedContextId) (st1 : SystemState),
      replyFrameHeadContext? st rid = some scId ∧
      returnUnheldSchedContextResolved st scId target = .ok st1 ∧
      st' = SchedContextOps.settleReturnedContext st1 home scId := by
  unfold popUnheldReplyHead at h
  cases hH : replyFrameHeadContext? st rid with
  | none => rw [hH] at h; exact .inl ⟨rfl, (Except.ok.inj h).symm⟩
  | some scId =>
    rw [hH] at h
    simp only [] at h
    cases hR : returnUnheldSchedContextResolved st scId target with
    | error e => rw [hR] at h; cases h
    | ok st1 => rw [hR] at h; exact .inr ⟨scId, st1, rfl, hR, (Except.ok.inj h).symm⟩

/-- The unheld pop writes no machine state. -/
theorem returnUnheldSchedContext_machine_eq {st st' : SystemState}
    {scId : SeLe4n.SchedContextId} {owner : SeLe4n.ThreadId}
    {newOwner? : Option SeLe4n.ThreadId}
    (h : returnUnheldSchedContext st scId owner newOwner? = .ok st') :
    st'.machine = st.machine := by
  obtain ⟨_, _, _, s1, s2, s3, _, _, _, _, _, h1, h2, _, h3, hEq⟩ :=
    returnUnheldSchedContext_ok_storeChain st st' scId owner newOwner? h
  rw [hEq, markKeyChangeFrom_machine, SeLe4n.Model.storeObject_machine_eq s2 s3 _ _ h3,
    storeDonationHeadPop_machine_eq h2, SeLe4n.Model.storeObject_machine_eq st s1 _ _ h1]

theorem returnUnheldSchedContextResolved_machine_eq {st st' : SystemState}
    {scId : SeLe4n.SchedContextId} {owner : SeLe4n.ThreadId}
    (h : returnUnheldSchedContextResolved st scId owner = .ok st') :
    st'.machine = st.machine := by
  unfold returnUnheldSchedContextResolved at h
  split at h
  · cases h
  · exact returnUnheldSchedContext_machine_eq h

/-- The pop at an unheld head writes no machine state. -/
theorem popUnheldReplyHead_machine_eq {st st' : SystemState} {rid : SeLe4n.ReplyId}
    {target : SeLe4n.ThreadId} {home : Concurrency.CoreId}
    (h : popUnheldReplyHead st rid target home = .ok st') : st'.machine = st.machine := by
  rcases popUnheldReplyHead_ok_cases h with ⟨_, rfl⟩ | ⟨scId, st1, _, hR, rfl⟩
  · rfl
  · rw [SchedContextOps.settleReturnedContext_machine]
    exact returnUnheldSchedContextResolved_machine_eq hR

/-- **The resolved unheld pop, decomposed**: the reply stack's outer caller it
resolved, and the pop at it. -/
theorem returnUnheldSchedContextResolved_ok_decompose {st st' : SystemState}
    {scId : SeLe4n.SchedContextId} {owner : SeLe4n.ThreadId}
    (h : returnUnheldSchedContextResolved st scId owner = .ok st') :
    ∃ newOwner?, replyStackOuterCaller? st scId = .ok newOwner? ∧
      returnUnheldSchedContext st scId owner newOwner? = .ok st' := by
  unfold returnUnheldSchedContextResolved at h
  split at h
  · cases h
  · next n hN => exact ⟨n, hN, h⟩

/-- The unheld pop keeps the object store's extended invariant: three stores. -/
theorem returnUnheldSchedContext_objects_invExt {st st' : SystemState}
    {scId : SeLe4n.SchedContextId} {owner : SeLe4n.ThreadId}
    {newOwner? : Option SeLe4n.ThreadId} (hObjInv : st.objects.invExt)
    (h : returnUnheldSchedContext st scId owner newOwner? = .ok st') :
    st'.objects.invExt := by
  obtain ⟨_, _, _, s1, s2, s3, _, _, _, _, _, h1, h2, _, h3, hEq⟩ :=
    returnUnheldSchedContext_ok_storeChain st st' scId owner newOwner? h
  have i1 := storeObject_preserves_objects_invExt st s1 _ _ hObjInv h1
  have i2 := storeDonationHeadPop_preserves_objects_invExt i1 h2
  have i3 := storeObject_preserves_objects_invExt s2 s3 _ _ i2 h3
  rw [hEq, markKeyChangeFrom_objects]; exact i3

/-- The pop at an unheld head keeps the object store's extended invariant. -/
theorem popUnheldReplyHead_objects_invExt {st st' : SystemState} {rid : SeLe4n.ReplyId}
    {target : SeLe4n.ThreadId} {home : Concurrency.CoreId} (hObjInv : st.objects.invExt)
    (h : popUnheldReplyHead st rid target home = .ok st') : st'.objects.invExt := by
  rcases popUnheldReplyHead_ok_cases h with ⟨_, rfl⟩ | ⟨scId, st1, _, hR, rfl⟩
  · exact hObjInv
  · obtain ⟨_, _, hP⟩ := returnUnheldSchedContextResolved_ok_decompose hR
    exact SchedContextOps.settleReturnedContext_objects_invExt _ _ _
      (returnUnheldSchedContext_objects_invExt hObjInv hP)

/-- The unheld pop holds the release queues: its context store keeps the
release fields, and its other stores are a reply's and a thread's. -/
theorem returnUnheldSchedContext_releaseStateAgree {st st' : SystemState}
    {scId : SeLe4n.SchedContextId} {owner : SeLe4n.ThreadId}
    {newOwner? : Option SeLe4n.ThreadId} (hObjInv : st.objects.invExt)
    (h : returnUnheldSchedContext st scId owner newOwner? = .ok st') :
    SystemState.releaseStateAgree st' st := by
  obtain ⟨_, _, ot, s1, s2, s3, hSc, _, _, _, _, h1, hClear, hL3, h3, hEq⟩ :=
    returnUnheldSchedContext_ok_storeChain st st' scId owner newOwner? h
  have i1 := storeObject_preserves_objects_invExt st s1 _ _ hObjInv h1
  have i2 := storeDonationHeadPop_preserves_objects_invExt i1 hClear
  have a1 := SystemState.releaseStateAgree.storeObject hObjInv h1 fun _ => by rw [hSc]; rfl
  have a2 : SystemState.releaseStateAgree s2 s1 :=
    .of_getSchedContext? (storeDonationHeadPop_getSchedContext?_eq i1 hClear)
      (by rw [storeDonationHeadPop_scheduler_eq hClear])
  have a3 := SystemState.releaseStateAgree.storeObject_tcb i2 h3
    (lookupTcb_some_objects _ _ _ hL3)
  have a4 : SystemState.releaseStateAgree st' s3 :=
    .of_objects_eq (by rw [hEq, markKeyChangeFrom_objects])
      (by rw [hEq, markKeyChangeFrom_releaseSlots])
  exact a4.trans (a3.trans (a2.trans a1))

/-- The unheld pop writes no replenish queue: its stores are objects, and its
reschedule hook raises flags. -/
theorem returnUnheldSchedContext_replenishQueueOnCore {st st' : SystemState}
    {scId : SeLe4n.SchedContextId} {owner : SeLe4n.ThreadId}
    {newOwner? : Option SeLe4n.ThreadId}
    (h : returnUnheldSchedContext st scId owner newOwner? = .ok st') (c : Concurrency.CoreId) :
    st'.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  obtain ⟨_, _, _, s1, s2, s3, _, _, _, _, _, h1, h2, _, h3, hEq⟩ :=
    returnUnheldSchedContext_ok_storeChain st st' scId owner newOwner? h
  rw [hEq, markKeyChangeFrom_replenishQueueOnCore, SeLe4n.Model.storeObject_scheduler_eq s2 s3 _ _ h3,
    storeDonationHeadPop_scheduler_eq h2, SeLe4n.Model.storeObject_scheduler_eq st s1 _ _ h1]

/-- The unheld pop writes the scheduler's reschedule flags alone. -/
theorem returnUnheldSchedContext_scheduler_eq {st st' : SystemState}
    {scId : SeLe4n.SchedContextId} {owner : SeLe4n.ThreadId}
    {newOwner? : Option SeLe4n.ThreadId}
    (h : returnUnheldSchedContext st scId owner newOwner? = .ok st') :
    st'.scheduler = { st.scheduler with reschedulePending := st'.scheduler.reschedulePending } := by
  obtain ⟨_, _, _, s1, s2, s3, _, _, _, _, _, h1, h2, _, h3, hEq⟩ :=
    returnUnheldSchedContext_ok_storeChain st st' scId owner newOwner? h
  have e3 : s3.scheduler = st.scheduler := by
    rw [SeLe4n.Model.storeObject_scheduler_eq s2 s3 _ _ h3, storeDonationHeadPop_scheduler_eq h2,
      SeLe4n.Model.storeObject_scheduler_eq st s1 _ _ h1]
  subst hEq
  have e := markKeyChangeFrom_extract_frame
    (fun s => ({ s.scheduler with
      reschedulePending := (markKeyChangeFrom st s3 owner).scheduler.reschedulePending } :
        SchedulerState)) st s3 owner (fun _ _ => rfl)
  rw [← e3]; exact e

/-- The unheld pop is a kind-preserving write: a context for a context, a reply
for a reply, a thread for a thread. -/
theorem returnUnheldSchedContext_kindPreservingWrite {st st' : SystemState}
    {scId : SeLe4n.SchedContextId} {owner : SeLe4n.ThreadId}
    {newOwner? : Option SeLe4n.ThreadId} (hObjInv : st.objects.invExt)
    (h : returnUnheldSchedContext st scId owner newOwner? = .ok st') :
    kindPreservingWrite st st' := by
  obtain ⟨_, _, ot, s1, s2, s3, hSc, _, _, _, _, hS1, hClear, hL, hS3, hEq⟩ :=
    returnUnheldSchedContext_ok_storeChain st st' scId owner newOwner? h
  have hW1 : kindPreservingWrite st s1 :=
    storeObject_kindPreservingWrite hObjInv hS1 hSc rfl (by simp [KernelObject.objectType])
  have hInv1 := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hW2 : kindPreservingWrite s1 s2 := storeDonationHeadPop_kindPreservingWrite hInv1 hClear
  have hInv2 := storeDonationHeadPop_preserves_objects_invExt hInv1 hClear
  have hW3 : kindPreservingWrite s2 s3 :=
    storeObject_kindPreservingWrite hInv2 hS3 (lookupTcb_some_objects s2 owner ot hL) rfl
      (by simp [KernelObject.objectType])
  have hLast : kindPreservingWrite s3 st' :=
    kindPreservingWrite.of_objects_eq (by rw [hEq, markKeyChangeFrom_objects])
  exact ((hW1.trans hW2).trans hW3).trans hLast

/-- The unheld pop writes no capability derivation edge. -/
theorem returnUnheldSchedContext_cdt_eq {st st' : SystemState}
    {scId : SeLe4n.SchedContextId} {owner : SeLe4n.ThreadId}
    {newOwner? : Option SeLe4n.ThreadId}
    (h : returnUnheldSchedContext st scId owner newOwner? = .ok st') : st'.cdt = st.cdt := by
  obtain ⟨_, _, _, s1, s2, s3, _, _, _, _, _, h1, h2, _, h3, hEq⟩ :=
    returnUnheldSchedContext_ok_storeChain st st' scId owner newOwner? h
  rw [hEq, markKeyChangeFrom_cdt, SeLe4n.Model.storeObject_cdt_eq s2 s3 _ _ h3,
    storeDonationHeadPop_cdt_eq h2, SeLe4n.Model.storeObject_cdt_eq st s1 _ _ h1]

/-- The pop at an unheld head keeps every object off the scheduler links of the
unheld pop it commits, or the whole store where the reply heads nothing. -/
theorem popUnheldReplyHead_objects_frame {st st' : SystemState}
    {rid : SeLe4n.ReplyId} {target : SeLe4n.ThreadId} {home : Concurrency.CoreId}
    (h : popUnheldReplyHead st rid target home = .ok st') :
    (replyFrameHeadContext? st rid = none ∧ st' = st) ∨
    ∃ (scId : SeLe4n.SchedContextId) (newOwner? : Option SeLe4n.ThreadId) (st1 : SystemState),
      replyFrameHeadContext? st rid = some scId ∧
      replyStackOuterCaller? st scId = .ok newOwner? ∧
      returnUnheldSchedContext st scId target newOwner? = .ok st1 ∧
      st' = SchedContextOps.settleReturnedContext st1 home scId := by
  rcases popUnheldReplyHead_ok_cases h with hId | ⟨scId, st1, hH, hR, hEq⟩
  · exact .inl hId
  · obtain ⟨n, hN, hP⟩ := returnUnheldSchedContextResolved_ok_decompose hR
    exact .inr ⟨scId, n, st1, hH, hN, hP, hEq⟩

end SeLe4n.Kernel
