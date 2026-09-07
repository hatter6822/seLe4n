import SeLe4n.Kernel.IPC.Invariant.QueueSplicePreservation
import SeLe4n.Kernel.IPC.Operations.Timeout

/-!
# WS-OD OD1.3 — the timeout abort's bundle carriage

`abortPendingIpcOnEndpoint` (`IPC/Operations/Timeout.lean`) is the object-only
prefix of `timeoutThread`: an endpoint-queue splice followed by one TCB rewrite.
This module is its `ipcInvariantFull` carriage, and it is a *composition* rather
than a fresh twenty-conjunct proof:

* the splice's half comes from
  `endpointQueueRemove_establishes_ipcInvariantFullExceptMembership`
  (`QueueSplicePreservation` §18), which is itself the dual removal's surface
  transferred through the two removals' agreement;
* the rewrite's half is `storeTcbReceiveComplete_closes_exceptMembership` (§7)
  with the timeout increment staged on top (§19).

The module lives apart from both because it is the first place in the tree that
needs the IPC invariant surface *and* the timeout operation: `Timeout.lean` sits
below the invariant modules and must stay there.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- WS-OD OD1.3: what a successful abort **is** — the splice, the thread it
leaves behind, and the one TCB store that rewrites it.

A consumer never unfolds `abortPendingIpcOnEndpoint` again: the two halves'
carriage is stated against these three equations. -/
theorem abortPendingIpcOnEndpoint_shape
    {endpointId : SeLe4n.ObjId} {isReceiveQ : Bool} {tid : SeLe4n.ThreadId}
    {st st' : SystemState}
    (hStep : abortPendingIpcOnEndpoint endpointId isReceiveQ tid st = .ok st') :
    ∃ (st1 : SystemState) (tcb1 : TCB),
      endpointQueueRemove endpointId isReceiveQ tid st = .ok st1 ∧
      lookupTcb st1 tid = some tcb1 ∧
      storeObject tid.toObjId
        (.tcb (TCB.withReturnFrame
          ({ tcb1 with
             ipcState := .ready
             pendingMessage := none
             timeoutBudget := none
             threadState := .Ready
             timedOut := true
             pendingReceiveReply := none }) Architecture.timeoutFrame)) st1
        = .ok ((), st') := by
  unfold abortPendingIpcOnEndpoint at hStep
  cases hRem : endpointQueueRemove endpointId isReceiveQ tid st with
  | error e => rw [hRem] at hStep; cases hStep
  | ok st1 =>
    rw [hRem] at hStep
    simp only [] at hStep
    cases hT : lookupTcb st1 tid with
    | none => rw [hT] at hStep; cases hStep
    | some tcb1 =>
      rw [hT] at hStep
      simp only [] at hStep
      refine ⟨st1, tcb1, rfl, hT, ?_⟩
      unfold storeObject at hStep ⊢
      simp only [Except.ok.injEq] at hStep ⊢
      exact hStep.symm ▸ rfl

/-- WS-OD OD1.3: the abort's post-splice detachment obligation.

`storeTcbReceiveComplete_closes_exceptMembership` consumes three readings of one
fact — *the rewritten thread is out of every endpoint queue*: it heads none,
tails none, and nothing's `queueNext` points at it.  `QueueSplicePreservation`
§8 discharges all three for a receive-side splice.  The abort runs on send- and
call-blocked threads too, and there `ipcInvariantFull` does not entail it: the
bundle constrains a queue only at its boundaries and says nothing about a
thread's membership in *other* endpoints' queues.  So the abort states it,
exactly as `sweptThreadQueueCoherent` is stated for the cancellation arms — and
a caller that swept, or that knows the thread was queued on one endpoint only,
discharges it. -/
def spliceLeavesThreadDetached (st : SystemState) (tid : SeLe4n.ThreadId) : Prop :=
  (∀ (epId : SeLe4n.ObjId) (ep : Endpoint), st.getEndpoint? epId = some ep →
      ep.receiveQ.head ≠ some tid ∧ ep.sendQ.head ≠ some tid) ∧
  (∀ (epId : SeLe4n.ObjId) (ep : Endpoint), st.getEndpoint? epId = some ep →
      ep.receiveQ.tail ≠ some tid ∧ ep.sendQ.tail ≠ some tid) ∧
  (∀ (a : SeLe4n.ThreadId) (tcbA : TCB), st.getTcb? a = some tcbA →
      tcbA.queueNext ≠ some tid)

/-- **WS-OD OD1.3 — the abort's object-only prefix carries the whole bundle.**

`abortPendingIpcOnEndpoint` is the splice followed by one TCB rewrite, and this
composes the two halves rather than re-proving twenty conjuncts:

* the splice leaves `ipcInvariantFullExceptMembership` at the removed thread
  (`endpointQueueRemove_establishes_ipcInvariantFullExceptMembership` — itself
  the dual removal's surface transferred through the two removals' agreement);
* the rewrite is the receive-completing store
  (`storeTcbReceiveComplete_closes_exceptMembership`) with the timeout increment
  staged on top (`abortStagedTcb_eq`,
  `timeoutStaging_preserves_ipcInvariantFull`).

The single store the operation performs and the two-step composition the proof
reasons about write the same object to the same key, so they agree pointwise and
the bundle transfers between them.  That is why the operation is *not* rewritten
to perform two stores: the split is a way of reading one record update, not a
second one. -/
theorem abortPendingIpcOnEndpoint_preserves_ipcInvariantFull
    {st st' : SystemState} {endpointId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId}
    (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st)
    (hAllNone : allTimeoutBudgetsNone st)
    (hNotReply : ∀ (tcb : TCB), st.getTcb? tid = some tcb →
      ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt)
    (hEnabled : dualRemovalEnabled endpointId isReceiveQ tid st)
    (hTailLast : spliceRemovedIsTailWhenLast isReceiveQ endpointId st tid)
    (hPred : splicePredecessorBlocked isReceiveQ endpointId st tid)
    (hDetached : ∀ st1, endpointQueueRemove endpointId isReceiveQ tid st = .ok st1 →
      spliceLeavesThreadDetached st1 tid)
    (hStep : abortPendingIpcOnEndpoint endpointId isReceiveQ tid st = .ok st') :
    ipcInvariantFull st' := by
  obtain ⟨st1, tcb1, hRem, hT1, hStore⟩ := abortPendingIpcOnEndpoint_shape hStep
  have hI1 : st1.objects.invExt :=
    endpointQueueRemove_preserves_objects_invExt endpointId isReceiveQ tid st st1 hObjInv hRem
  have hExcept : ipcInvariantFullExceptMembership st1 tid :=
    endpointQueueRemove_establishes_ipcInvariantFullExceptMembership hObjInv hInv hEnabled
      hTailLast hPred hRem
  obtain ⟨stD, hDual⟩ := hEnabled
  obtain ⟨stS, hRem', hAgree⟩ :=
    endpointQueueRemove_agrees_with_dual hObjInv hInv hTailLast hDual
  have hEqS : stS = st1 := by rw [hRem'] at hRem; exact Except.ok.inj hRem
  rw [hEqS] at hAgree
  -- Two frames the dual carries, read through the agreement.
  have hAllNone1 : allTimeoutBudgetsNone st1 := by
    intro t tcbT hT
    rw [hAgree] at hT
    obtain ⟨tcb0, h0, hEq⟩ :=
      endpointQueueRemoveDual_timeoutBudgetFrame st stD endpointId isReceiveQ tid hObjInv
        hDual t tcbT hT
    rw [← hEq]; exact hAllNone t tcb0 h0
  have hNotReply1 : ∀ (tcbX : TCB), st1.getTcb? tid = some tcbX →
      ∀ ep rt, tcbX.ipcState ≠ .blockedOnReply ep rt := by
    intro tcbX hX ep rt hc
    have hXRaw := (SystemState.getTcb?_eq_some_iff st1 tid tcbX).mp hX
    rw [hAgree] at hXRaw
    obtain ⟨tcb0, h0, hEq⟩ :=
      endpointQueueRemoveDual_ipcStateFrame st stD endpointId isReceiveQ tid hObjInv hDual
        tid tcbX hXRaw
    exact hNotReply tcb0 ((SystemState.getTcb?_eq_some_iff st tid tcb0).mpr h0) ep rt
      (hEq.trans hc)
  obtain ⟨hNoHead, hNoTail, hNoIncoming⟩ := hDetached st1 hRem
  -- Step 1 of the two-step reading: the receive-completing store.
  obtain ⟨sRc, hStoreRc⟩ : ∃ s, storeObject tid.toObjId
      (.tcb ({ tcb1 with
               ipcState := .ready
               pendingMessage := none
               pendingReceiveReply := none })) st1 = .ok ((), s) := ⟨_, rfl⟩
  have hRc : storeTcbReceiveComplete st1 tid none = .ok sRc := by
    unfold storeTcbReceiveComplete
    rw [hT1]
    simp only []
    rw [hStoreRc]
  have hFullRc : ipcInvariantFull sRc :=
    storeTcbReceiveComplete_closes_exceptMembership st1 sRc tid none hI1
      (fun _ hm => by cases hm) hAllNone1
      (fun tcbX hX => hNotReply1 tcbX ((SystemState.getTcb?_eq_some_iff st1 tid tcbX).mpr hX))
      (fun epId ep hEp =>
        hNoHead epId ep ((SystemState.getEndpoint?_eq_some_iff st1 epId ep).mpr hEp))
      (fun epId ep hEp =>
        hNoTail epId ep ((SystemState.getEndpoint?_eq_some_iff st1 epId ep).mpr hEp))
      (fun a tcbA hA => hNoIncoming a tcbA ((SystemState.getTcb?_eq_some_iff st1 a tcbA).mpr hA))
      hExcept hRc
  have hIRc : sRc.objects.invExt :=
    storeObject_preserves_objects_invExt st1 sRc tid.toObjId _ hI1 hStoreRc
  have hRcTcb : sRc.getTcb? tid = some ({ tcb1 with
      ipcState := .ready
      pendingMessage := none
      pendingReceiveReply := none }) :=
    (SystemState.getTcb?_eq_some_iff sRc tid _).mpr
      (storeObject_objects_eq st1 sRc tid.toObjId _ hI1 hStoreRc)
  have hAllNoneRc : allTimeoutBudgetsNone sRc := by
    intro t tcbT hT
    by_cases hk : t.toObjId = tid.toObjId
    · rw [hk, storeObject_objects_eq st1 sRc tid.toObjId _ hI1 hStoreRc] at hT
      obtain rfl := KernelObject.tcb.inj (Option.some.inj hT)
      exact hAllNone1 tid tcb1 (lookupTcb_some_objects st1 tid tcb1 hT1)
    · rw [storeObject_objects_ne st1 sRc tid.toObjId t.toObjId _ hk hI1 hStoreRc] at hT
      exact hAllNone1 t tcbT hT
  -- Step 2: the timeout increment, staged on top.
  obtain ⟨sStage, hStage⟩ : ∃ s, storeObject tid.toObjId
      (.tcb (timeoutStagedTcb ({ tcb1 with
              ipcState := .ready
              pendingMessage := none
              pendingReceiveReply := none }))) sRc = .ok ((), s) := ⟨_, rfl⟩
  have hFullStage : ipcInvariantFull sStage :=
    timeoutStaging_preserves_ipcInvariantFull hIRc hRcTcb rfl hAllNoneRc hStage hFullRc
  -- The two-step reading and the operation's single store agree pointwise.
  have hAgree2 : objectStoreAgrees sStage st' := by
    intro k
    by_cases hk : k = tid.toObjId
    · subst hk
      rw [storeObject_objects_eq st1 st' tid.toObjId _ hI1 hStore,
        storeObject_objects_eq sRc sStage tid.toObjId _ hIRc hStage, abortStagedTcb_eq]
    · rw [storeObject_objects_ne st1 st' tid.toObjId k _ hk hI1 hStore,
        storeObject_objects_ne sRc sStage tid.toObjId k _ hk hIRc hStage,
        storeObject_objects_ne st1 sRc tid.toObjId k _ hk hI1 hStoreRc]
  have hSched2 : st'.scheduler = sStage.scheduler := by
    rw [storeObject_scheduler_eq st1 st' tid.toObjId _ hStore,
      storeObject_scheduler_eq sRc sStage tid.toObjId _ hStage,
      storeObject_scheduler_eq st1 sRc tid.toObjId _ hStoreRc]
  exact ipcInvariantFull_of_storeAgrees_of_scheduler_eq hAgree2 hSched2 hFullStage

end SeLe4n.Kernel
