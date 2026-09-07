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

/-- WS-OD OD1.4: the abort preserves the identity registry's well-formedness.

Its splice half leaves the registry literally unchanged
(`endpointQueueRemove_objectIndexSet_eq`) and its store half extends it through
`storeObject`, which preserves it.  Needed by the cancellation reclaim's
information-flow argument, whose store chain runs on the *aborted* state. -/
theorem abortPendingIpcOnEndpoint_preserves_objectIndexSet_invExt
    (epId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState) (hObjSetInv : st.objectIndexSet.table.invExt)
    (h : abortPendingIpcOnEndpoint epId isReceiveQ tid st = .ok st') :
    st'.objectIndexSet.table.invExt := by
  obtain ⟨st1, _, hRem, _, hStore⟩ := abortPendingIpcOnEndpoint_shape h
  have hSet1 : st1.objectIndexSet.table.invExt := by
    rw [endpointQueueRemove_objectIndexSet_eq epId isReceiveQ tid st st1 hRem]; exact hObjSetInv
  exact SeLe4n.Model.storeObject_preserves_objectIndexSet_invExt st1 st' _ _ hSet1 hStore

/-- WS-OD OD1.4: the abort preserves the identity registry's completeness.

The splice half creates no key and leaves the registry unchanged; the store half
registers the one key it writes. -/
theorem abortPendingIpcOnEndpoint_preserves_objectIndexSetComplete
    (epId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState) (hInv : st.objects.invExt)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hComplete : SeLe4n.Model.objectIndexSetComplete st)
    (h : abortPendingIpcOnEndpoint epId isReceiveQ tid st = .ok st') :
    SeLe4n.Model.objectIndexSetComplete st' := by
  obtain ⟨st1, _, hRem, _, hStore⟩ := abortPendingIpcOnEndpoint_shape h
  have hInv1 := endpointQueueRemove_preserves_objects_invExt _ _ _ _ _ hInv hRem
  have hSet1 : st1.objectIndexSet.table.invExt := by
    rw [endpointQueueRemove_objectIndexSet_eq epId isReceiveQ tid st st1 hRem]; exact hObjSetInv
  have hC1 : SeLe4n.Model.objectIndexSetComplete st1 :=
    endpointQueueRemove_preserves_objectIndexSetComplete epId isReceiveQ tid st st1 hInv
      hComplete hRem
  exact SeLe4n.Model.storeObject_preserves_objectIndexSetComplete st1 st' _ _ hInv1 hSet1
    hC1 hStore

/-- WS-OD OD1.4: **the abort carries `donationOwnerValid`**, given that the
aborted thread is not itself the owner of any donation.

The side condition is exactly what the abort can break and nothing else can: the
conjunct requires a donation's owner to be `.blockedOnReply`, and the abort's one
substantive write moves the aborted thread to `.ready`.  Every other thread's
`ipcState` and every thread's `schedContextBinding` are untouched
(`_tcb_forward_of_ne`, `_binding_backward`), and no SchedContext is written in
either direction (`_schedContext_forward`).

It is stated as "the aborted thread holds a binding" rather than as "the aborted
thread owns no donation" because that is the form the cancellation reclaim
supplies for free: the thread it aborts is the *holder* of the cancelled
caller's donation, so its binding is `.donated`, and `donationOwnerValid`'s own
second clause puts every owner at `.unbound`. -/
theorem abortPendingIpcOnEndpoint_preserves_donationOwnerValid
    (epId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState) (hInv : st.objects.invExt)
    (h : abortPendingIpcOnEndpoint epId isReceiveQ tid st = .ok st')
    (hBound : ∀ t, st.getTcb? tid = some t → t.schedContextBinding ≠ .unbound)
    (hOwner : donationOwnerValid st) :
    donationOwnerValid st' := by
  intro donee doneeTcb scId owner hDoneeAt hBind
  obtain ⟨doneeTcb0, hDoneeAt0, hBind0⟩ :=
    abortPendingIpcOnEndpoint_binding_backward epId isReceiveQ tid st st' hInv h
      donee.toObjId doneeTcb hDoneeAt
  obtain ⟨⟨sc, hScAt, hScBound⟩, ownerTcb, hOwnerAt, hOwnerUnbound, hOwnerBlocked⟩ :=
    hOwner donee doneeTcb0 scId owner hDoneeAt0 (hBind0.trans hBind)
  -- The owner is not the aborted thread: owners are `.unbound`, and the aborted
  -- thread holds a binding by hypothesis.
  have hOwnerNe : owner.toObjId ≠ tid.toObjId := by
    intro hEq
    exact hBound ownerTcb ((SystemState.getTcb?_eq_some_iff st tid ownerTcb).mpr
      (hEq ▸ hOwnerAt)) hOwnerUnbound
  obtain ⟨ownerTcb', hOwnerAt', hIpc', hBind'⟩ :=
    abortPendingIpcOnEndpoint_tcb_forward_of_ne epId isReceiveQ tid st st' hInv h
      owner.toObjId hOwnerNe ownerTcb hOwnerAt
  exact ⟨⟨sc, abortPendingIpcOnEndpoint_schedContext_forward epId isReceiveQ tid st st'
      hInv h scId.toObjId sc hScAt, hScBound⟩,
    ownerTcb', hOwnerAt', hBind'.trans hOwnerUnbound, by rw [hIpc']; exact hOwnerBlocked⟩

end SeLe4n.Kernel
