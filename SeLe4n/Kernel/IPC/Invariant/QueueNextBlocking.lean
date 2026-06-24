-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.QueueMembership

/-!
# V3-J-cross: queueNextBlockingConsistent Preservation Proofs

Primitive preservation lemmas for the `queueNextBlockingConsistent` invariant,
which ensures that if `a.queueNext = some b`, then `a` and `b` are blocked on
the same endpoint with compatible queue types.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

set_option linter.unusedVariables false

-- ============================================================================
-- Section 1: queueNextBlockingMatch helpers
-- ============================================================================

/-- Any ipcState is self-compatible. -/
theorem queueNextBlockingMatch_self (s : ThreadIpcState) :
    queueNextBlockingMatch s s := by
  unfold queueNextBlockingMatch; cases s <;> first | exact rfl | exact True.intro

/-- Non-blocking states (ready, blockedOnReply, blockedOnNotification) are
compatible with anything from either side. -/
theorem queueNextBlockingMatch_ready_left (s : ThreadIpcState) :
    queueNextBlockingMatch .ready s := by
  unfold queueNextBlockingMatch; cases s <;> exact True.intro

theorem queueNextBlockingMatch_ready_right (s : ThreadIpcState) :
    queueNextBlockingMatch s .ready := by
  unfold queueNextBlockingMatch; cases s <;> exact True.intro

-- ============================================================================
-- Section 2: Scheduler-only frame (ensureRunnable / removeRunnable)
-- ============================================================================

/-- Pointwise object lookup equality implies queueNextBlockingConsistent transfer. -/
theorem queueNextBlockingConsistent_of_objects_eq
    (st st' : SystemState)
    (hLk : ∀ (x : SeLe4n.ObjId), st'.objects[x]? = st.objects[x]?)
    (hInv : queueNextBlockingConsistent st) :
    queueNextBlockingConsistent st' := by
  intro a b tcbA tcbB hA hB hN
  rw [hLk] at hA hB
  exact hInv a b tcbA tcbB hA hB hN

theorem ensureRunnable_preserves_queueNextBlockingConsistent
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : queueNextBlockingConsistent st) :
    queueNextBlockingConsistent (ensureRunnable st tid) := by
  apply queueNextBlockingConsistent_of_objects_eq st (ensureRunnable st tid)
  · intro x; unfold ensureRunnable; split
    · rfl
    · split <;> rfl
  · exact hInv

theorem removeRunnable_preserves_queueNextBlockingConsistent
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : queueNextBlockingConsistent st) :
    queueNextBlockingConsistent (removeRunnable st tid) := by
  apply queueNextBlockingConsistent_of_objects_eq st (removeRunnable st tid)
  · intro x; unfold removeRunnable; simp
  · exact hInv

-- ============================================================================
-- Section 3: storeObject endpoint preserves queueNextBlockingConsistent
-- ============================================================================

theorem storeObject_endpoint_preserves_queueNextBlockingConsistent
    (st st' : SystemState) (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hInv : queueNextBlockingConsistent st)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid (.endpoint ep) st = .ok ((), st')) :
    queueNextBlockingConsistent st' := by
  have hFrame : ∀ x, x ≠ oid → st'.objects[x]? = st.objects[x]? :=
    fun x hNe => storeObject_objects_ne st st' oid x _ hNe hObjInv hStore
  have hEqAt : st'.objects[oid]? = some (.endpoint ep) :=
    storeObject_objects_eq st st' oid _ hObjInv hStore
  intro a b tcbA tcbB hA hB hN
  have hNeA : a.toObjId ≠ oid := by
    intro hEq; rw [hEq] at hA; rw [hEqAt] at hA; cases hA
  have hNeB : b.toObjId ≠ oid := by
    intro hEq; rw [hEq] at hB; rw [hEqAt] at hB; cases hB
  rw [hFrame a.toObjId hNeA] at hA
  rw [hFrame b.toObjId hNeB] at hB
  exact hInv a b tcbA tcbB hA hB hN

-- ============================================================================
-- Section 4: storeObject non-TCB/non-endpoint frame
-- ============================================================================

theorem storeObject_non_ep_non_tcb_preserves_queueNextBlockingConsistent
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hInv : queueNextBlockingConsistent st)
    (hObjInv : st.objects.invExt)
    (hNotTcb : ∀ tcb, obj ≠ .tcb tcb)
    (hPrevNotTcb : ∀ tcb, st.objects[oid]? ≠ some (.tcb tcb))
    (hStore : storeObject oid obj st = .ok ((), st')) :
    queueNextBlockingConsistent st' := by
  have hFrame : ∀ x, x ≠ oid → st'.objects[x]? = st.objects[x]? :=
    fun x hNe => storeObject_objects_ne st st' oid x obj hNe hObjInv hStore
  have hEqAt : st'.objects[oid]? = some obj :=
    storeObject_objects_eq st st' oid obj hObjInv hStore
  intro a b tcbA tcbB hA hB hN
  have hNeA : a.toObjId ≠ oid := by
    intro hEq; rw [hEq] at hA; rw [hEqAt] at hA; cases hA; exact absurd rfl (hNotTcb tcbA)
  have hNeB : b.toObjId ≠ oid := by
    intro hEq; rw [hEq] at hB; rw [hEqAt] at hB; cases hB; exact absurd rfl (hNotTcb tcbB)
  rw [hFrame a.toObjId hNeA] at hA
  rw [hFrame b.toObjId hNeB] at hB
  exact hInv a b tcbA tcbB hA hB hN

-- ============================================================================
-- Section 5: storeTcbQueueLinks preserves queueNextBlockingConsistent
-- ============================================================================

theorem storeTcbQueueLinks_preserves_queueNextBlockingConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId)
    (hInv : queueNextBlockingConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st')
    (hNewLink : ∀ (b : SeLe4n.ThreadId) (tcbTid tcbB : TCB),
      next = some b →
      st.objects[tid.toObjId]? = some (.tcb tcbTid) →
      st.objects[b.toObjId]? = some (.tcb tcbB) →
      queueNextBlockingMatch tcbTid.ipcState tcbB.ipcState) :
    queueNextBlockingConsistent st' := by
  have hFrame : ∀ x, x ≠ tid.toObjId → st'.objects[x]? = st.objects[x]? :=
    fun x hNe => storeTcbQueueLinks_preserves_objects_ne st st' tid prev pprev next x hNe hObjInv hStep
  have hStored := storeTcbQueueLinks_stored_queueNext st st' tid prev pprev next hObjInv hStep
  obtain ⟨tcb', hTcb', hQN'⟩ := hStored
  have hIpcBack := storeTcbQueueLinks_tcb_ipcState_backward st st' tid prev pprev next hObjInv hStep
  intro a b tcbA tcbB hA hB hN
  by_cases hEqA : a.toObjId = tid.toObjId
  · -- a is the target
    by_cases hEqB : b.toObjId = tid.toObjId
    · -- b = target too: same ipcState via backward
      have ⟨origA, hOrigA, hIpcA⟩ := hIpcBack a tcbA (hEqA ▸ hA)
      have ⟨origB, hOrigB, hIpcB⟩ := hIpcBack b tcbB (hEqB ▸ hB)
      rw [hEqA] at hOrigA; rw [hEqB] at hOrigB
      rw [hOrigA] at hOrigB; cases Option.some.inj hOrigB
      show queueNextBlockingMatch tcbA.ipcState tcbB.ipcState
      rw [← hIpcA, ← hIpcB]; exact queueNextBlockingMatch_self _
    · -- b ≠ target
      rw [hFrame b.toObjId hEqB] at hB
      have ⟨origA, hOrigA, hIpcA⟩ := hIpcBack a tcbA (hEqA ▸ hA)
      rw [hEqA] at hOrigA
      -- tcbA at target has queueNext = next (= tcb'.queueNext)
      -- tcbA.ipcState = origA.ipcState (from hIpcBack)
      -- tcb' at target has queueNext = next (from hQN')
      -- hA : st'.objects[tid.toObjId]? = some (.tcb tcbA)
      -- hTcb' : st'.objects[tid.toObjId]? = some (.tcb tcb')
      -- So tcbA = tcb', meaning tcbA.queueNext = next
      rw [hEqA] at hA; rw [hTcb'] at hA
      have hTcbEq : tcb' = tcbA := by cases Option.some.inj hA; rfl
      rw [← hTcbEq, hQN'] at hN
      show queueNextBlockingMatch tcbA.ipcState tcbB.ipcState
      rw [← hIpcA]; exact hNewLink b origA tcbB hN hOrigA hB
  · -- a ≠ target
    rw [hFrame a.toObjId hEqA] at hA
    by_cases hEqB : b.toObjId = tid.toObjId
    · -- b = target
      have ⟨origB, hOrigB, hIpcB⟩ := hIpcBack b tcbB (hEqB ▸ hB)
      rw [hEqB] at hOrigB
      have hPre := hInv a b tcbA origB hA (hEqB ▸ hOrigB) hN
      show queueNextBlockingMatch tcbA.ipcState tcbB.ipcState
      rw [← hIpcB]; exact hPre
    · -- neither
      rw [hFrame b.toObjId hEqB] at hB
      exact hInv a b tcbA tcbB hA hB hN

/-- Variant: storeTcbQueueLinks with next = none trivially preserves. -/
theorem storeTcbQueueLinks_none_preserves_queueNextBlockingConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (hInv : queueNextBlockingConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st tid prev pprev none = .ok st') :
    queueNextBlockingConsistent st' :=
  storeTcbQueueLinks_preserves_queueNextBlockingConsistent
    st st' tid prev pprev none hInv hObjInv hStep
    (fun _ _ _ hN _ _ => by cases hN)

-- ============================================================================
-- Section 6: storeTcbIpcStateAndMessage preserves queueNextBlockingConsistent
-- ============================================================================

theorem storeTcbIpcStateAndMessage_preserves_queueNextBlockingConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipcState : ThreadIpcState) (msg : Option IpcMessage)
    (hInv : queueNextBlockingConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid ipcState msg = .ok st')
    (hFwd : ∀ (b : SeLe4n.ThreadId) (tcbTid tcbB : TCB),
      st.objects[tid.toObjId]? = some (.tcb tcbTid) →
      tcbTid.queueNext = some b →
      st.objects[b.toObjId]? = some (.tcb tcbB) →
      queueNextBlockingMatch ipcState tcbB.ipcState)
    (hBwd : ∀ (a : SeLe4n.ThreadId) (tcbA tcbTid : TCB),
      st.objects[a.toObjId]? = some (.tcb tcbA) →
      tcbA.queueNext = some tid →
      st.objects[tid.toObjId]? = some (.tcb tcbTid) →
      queueNextBlockingMatch tcbA.ipcState ipcState) :
    queueNextBlockingConsistent st' := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some origTcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { origTcb with ipcState := ipcState, pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep; subst hEq
      have hEqAt := storeObject_objects_eq' st tid.toObjId _ pair hObjInv hStore
      have hOrigTcb := lookupTcb_some_objects st tid origTcb hLookup
      have hFrame : ∀ x, x ≠ tid.toObjId → pair.snd.objects[x]? = st.objects[x]? :=
        fun x hNe => storeObject_objects_ne' st tid.toObjId x _ pair hNe hObjInv hStore
      -- Key facts about the stored TCB:
      -- ipcState = ipcState (by construction)
      -- queueNext = origTcb.queueNext (record update doesn't touch it)
      intro a b tcbA tcbB hA hB hN
      by_cases hEqA : a.toObjId = tid.toObjId
      · -- a is the target
        rw [hEqA] at hA; rw [hEqAt] at hA
        have hIpcA : tcbA.ipcState = ipcState := by cases Option.some.inj hA; rfl
        have hQNA : tcbA.queueNext = origTcb.queueNext := by cases Option.some.inj hA; rfl
        by_cases hEqB : b.toObjId = tid.toObjId
        · -- b also at target
          rw [hEqB] at hB; rw [hEqAt] at hB
          have hIpcB : tcbB.ipcState = ipcState := by cases Option.some.inj hB; rfl
          show queueNextBlockingMatch tcbA.ipcState tcbB.ipcState
          rw [hIpcA, hIpcB]; exact queueNextBlockingMatch_self _
        · -- b not at target
          rw [hFrame b.toObjId hEqB] at hB
          show queueNextBlockingMatch tcbA.ipcState tcbB.ipcState
          rw [hIpcA]; rw [hQNA] at hN
          exact hFwd b origTcb tcbB hOrigTcb hN hB
      · -- a not at target
        rw [hFrame a.toObjId hEqA] at hA
        by_cases hEqB : b.toObjId = tid.toObjId
        · -- b at target
          rw [hEqB] at hB; rw [hEqAt] at hB
          have hIpcB : tcbB.ipcState = ipcState := by cases Option.some.inj hB; rfl
          have hBTid := SeLe4n.ThreadId.toObjId_injective b tid hEqB; subst hBTid
          show queueNextBlockingMatch tcbA.ipcState tcbB.ipcState
          rw [hIpcB]
          exact hBwd a tcbA origTcb hA hN hOrigTcb
        · -- neither
          rw [hFrame b.toObjId hEqB] at hB
          exact hInv a b tcbA tcbB hA hB hN

-- ============================================================================
-- Section 7: Simplified variants
-- ============================================================================

/-- When the new ipcState is .ready, preservation is unconditional. -/
theorem storeTcbIpcStateAndMessage_ready_preserves_queueNextBlockingConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (msg : Option IpcMessage)
    (hInv : queueNextBlockingConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid .ready msg = .ok st') :
    queueNextBlockingConsistent st' :=
  storeTcbIpcStateAndMessage_preserves_queueNextBlockingConsistent
    st st' tid .ready msg hInv hObjInv hStep
    (fun _ _ _ _ _ _ => queueNextBlockingMatch_ready_left _)
    (fun _ _ _ _ _ _ => queueNextBlockingMatch_ready_right _)

/-- When tid has queueNext = none and no predecessor, preservation is unconditional. -/
theorem storeTcbIpcStateAndMessage_nolinks_preserves_queueNextBlockingConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipcState : ThreadIpcState) (msg : Option IpcMessage)
    (hInv : queueNextBlockingConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid ipcState msg = .ok st')
    (hNoNext : ∀ (tcb : TCB), st.objects[tid.toObjId]? = some (.tcb tcb) →
      tcb.queueNext = none)
    (hNoPrev : ∀ (a : SeLe4n.ThreadId) (tcbA : TCB),
      st.objects[a.toObjId]? = some (.tcb tcbA) →
      tcbA.queueNext ≠ some tid) :
    queueNextBlockingConsistent st' :=
  storeTcbIpcStateAndMessage_preserves_queueNextBlockingConsistent
    st st' tid ipcState msg hInv hObjInv hStep
    (fun _ tcbTid _ hTid hQN _ => absurd (hNoNext tcbTid hTid ▸ hQN) (by simp))
    (fun a tcbA _ hA hQN _ => absurd hQN (hNoPrev a tcbA hA))

-- ============================================================================
-- Section: queueHeadBlockedConsistent primitive preservation
-- ============================================================================

/-- ensureRunnable preserves queueHeadBlockedConsistent (doesn't change objects). -/
theorem ensureRunnable_preserves_queueHeadBlockedConsistent
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : queueHeadBlockedConsistent st) :
    queueHeadBlockedConsistent (ensureRunnable st tid) := by
  intro epId ep hd tcb hEp hTcb
  rw [show (ensureRunnable st tid).objects = st.objects from
    ensureRunnable_preserves_objects st tid] at hEp hTcb
  exact hInv epId ep hd tcb hEp hTcb

/-- removeRunnable preserves queueHeadBlockedConsistent (doesn't change objects). -/
theorem removeRunnable_preserves_queueHeadBlockedConsistent
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : queueHeadBlockedConsistent st) :
    queueHeadBlockedConsistent (removeRunnable st tid) := by
  intro epId ep hd tcb hEp hTcb
  rw [show (removeRunnable st tid).objects = st.objects from
    removeRunnable_preserves_objects st tid] at hEp hTcb
  exact hInv epId ep hd tcb hEp hTcb

/-- storeTcbIpcStateAndMessage preserves queueHeadBlockedConsistent when the
thread is not a queue head. The precondition hNotHead ensures that tid is not
the head of any endpoint queue. -/
theorem storeTcbIpcStateAndMessage_preserves_queueHeadBlockedConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipcState : ThreadIpcState) (msg : Option IpcMessage)
    (hInv : queueHeadBlockedConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid ipcState msg = .ok st')
    (hNotHead : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.receiveQ.head ≠ some tid ∧ ep.sendQ.head ≠ some tid) :
    queueHeadBlockedConsistent st' := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hSt : storeObject tid.toObjId
        (.tcb { tcb with ipcState := ipcState, pendingMessage := msg }) st with
    | error e => simp [hSt] at hStep
    | ok pair =>
      simp only [hSt, Except.ok.injEq] at hStep; subst hStep
      have hFrame := fun x (h : x ≠ tid.toObjId) =>
        storeObject_objects_ne st pair.2 tid.toObjId x _ h hObjInv hSt
      have hEqAt := storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hSt
      intro epId ep hd hdTcb hEp hTcb
      have hNeEp : epId ≠ tid.toObjId := by
        intro h; subst h; rw [hEqAt] at hEp; cases hEp
      rw [hFrame epId hNeEp] at hEp
      by_cases hHdEq : hd.toObjId = tid.toObjId
      · -- hd = tid: but hNotHead says tid is not a queue head — contradiction
        have hTidEq := ThreadId.toObjId_injective hd tid hHdEq; subst hTidEq
        have ⟨hNR, hNS⟩ := hNotHead epId ep hEp
        exact ⟨fun h => absurd h hNR, fun h => absurd h hNS⟩
      · rw [hFrame hd.toObjId hHdEq] at hTcb
        exact hInv epId ep hd hdTcb hEp hTcb

/-- storeTcbPendingMessage preserves queueHeadBlockedConsistent. -/
theorem storeTcbPendingMessage_preserves_queueHeadBlockedConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (msg : Option IpcMessage)
    (hInv : queueHeadBlockedConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbPendingMessage st tid msg = .ok st') :
    queueHeadBlockedConsistent st' := by
  unfold storeTcbPendingMessage at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hSt : storeObject tid.toObjId
        (.tcb { tcb with pendingMessage := msg }) st with
    | error e => simp [hSt] at hStep
    | ok pair =>
      simp only [hSt, Except.ok.injEq] at hStep; subst hStep
      have hFrame := fun x (h : x ≠ tid.toObjId) =>
        storeObject_objects_ne st pair.2 tid.toObjId x _ h hObjInv hSt
      have hEqAt := storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hSt
      have hTcbObj := lookupTcb_some_objects st tid tcb hLookup
      intro epId ep hd hdTcb hEp hTcb
      have hNeEp : epId ≠ tid.toObjId := by
        intro h; subst h; rw [hEqAt] at hEp; cases hEp
      rw [hFrame epId hNeEp] at hEp
      by_cases hHdEq : hd.toObjId = tid.toObjId
      · -- hd = tid: pendingMessage changed but ipcState preserved
        rw [hHdEq, hEqAt] at hTcb
        simp only [Option.some.injEq, KernelObject.tcb.injEq] at hTcb
        subst hTcb
        exact hInv epId ep hd tcb hEp (by rw [hHdEq]; exact hTcbObj)
      · rw [hFrame hd.toObjId hHdEq] at hTcb
        exact hInv epId ep hd hdTcb hEp hTcb

-- ============================================================================
-- Section 8: storeTcbReceiveComplete / storeTcbPendingMessage frames
-- ============================================================================

/-- `storeTcbReceiveComplete` stores the receiver with `.ready` ipcState (plus
the delivered message and a cleared `pendingReceiveReply` stash, neither of which
this invariant reads), so the queueNext-blocking link from/to the stored thread
becomes vacuously compatible (`.ready` matches anything). Identical in shape to
`storeTcbIpcStateAndMessage_ready_preserves_queueNextBlockingConsistent`. -/
theorem storeTcbReceiveComplete_preserves_queueNextBlockingConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (msg : Option IpcMessage)
    (hInv : queueNextBlockingConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbReceiveComplete st tid msg = .ok st') :
    queueNextBlockingConsistent st' := by
  unfold storeTcbReceiveComplete at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some origTcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { origTcb with ipcState := .ready, pendingMessage := msg, pendingReceiveReply := none }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore, Except.ok.injEq] at hStep; subst hStep
      have hEqAt := storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hStore
      have hOrigTcb := lookupTcb_some_objects st tid origTcb hLookup
      have hFrame : ∀ x, x ≠ tid.toObjId → pair.2.objects[x]? = st.objects[x]? :=
        fun x hNe => storeObject_objects_ne st pair.2 tid.toObjId x _ hNe hObjInv hStore
      intro a b tcbA tcbB hA hB hN
      by_cases hEqA : a.toObjId = tid.toObjId
      · -- a is the target: stored ipcState = .ready, so match holds left.
        rw [hEqA] at hA; rw [hEqAt] at hA
        have hIpcA : tcbA.ipcState = .ready := by cases Option.some.inj hA; rfl
        rw [hIpcA]; exact queueNextBlockingMatch_ready_left _
      · rw [hFrame a.toObjId hEqA] at hA
        by_cases hEqB : b.toObjId = tid.toObjId
        · -- b is the target: stored ipcState = .ready, so match holds right.
          rw [hEqB] at hB; rw [hEqAt] at hB
          have hIpcB : tcbB.ipcState = .ready := by cases Option.some.inj hB; rfl
          rw [hIpcB]; exact queueNextBlockingMatch_ready_right _
        · rw [hFrame b.toObjId hEqB] at hB
          exact hInv a b tcbA tcbB hA hB hN

/-- `storeTcbReceiveComplete` stores the receiver `.ready`. A `.ready` thread is
neither a sendQ nor receiveQ head (heads are blocked), so this preserves
`queueHeadBlockedConsistent` for any thread that *was* a head (its ipcState is
unchanged), and the stored thread itself, if it were a head, is now `.ready` —
but the property only constrains heads, and a head must be blocked, which the
pre-state invariant already records. Proven directly by unfolding. -/
theorem storeTcbReceiveComplete_preserves_queueHeadBlockedConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (msg : Option IpcMessage)
    (hInv : queueHeadBlockedConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbReceiveComplete st tid msg = .ok st')
    (hNotHead : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.receiveQ.head ≠ some tid ∧ ep.sendQ.head ≠ some tid) :
    queueHeadBlockedConsistent st' := by
  unfold storeTcbReceiveComplete at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hSt : storeObject tid.toObjId (.tcb { tcb with ipcState := .ready, pendingMessage := msg, pendingReceiveReply := none }) st with
    | error e => simp [hSt] at hStep
    | ok pair =>
      simp only [hSt, Except.ok.injEq] at hStep; subst hStep
      have hFrame := fun x (h : x ≠ tid.toObjId) =>
        storeObject_objects_ne st pair.2 tid.toObjId x _ h hObjInv hSt
      have hEqAt := storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hSt
      intro epId ep hd hdTcb hEp hTcb
      have hNeEp : epId ≠ tid.toObjId := by
        intro h; subst h; rw [hEqAt] at hEp; cases hEp
      rw [hFrame epId hNeEp] at hEp
      by_cases hHdEq : hd.toObjId = tid.toObjId
      · -- hd = tid: but hNotHead says tid is not a queue head — contradiction.
        have hTidEq := ThreadId.toObjId_injective hd tid hHdEq; subst hTidEq
        have ⟨hNR, hNS⟩ := hNotHead epId ep hEp
        exact ⟨fun h => absurd h hNR, fun h => absurd h hNS⟩
      · rw [hFrame hd.toObjId hHdEq] at hTcb
        exact hInv epId ep hd hdTcb hEp hTcb

/-- `storeTcbReceiveComplete` preserves `endpointQueueTailBlockedConsistent` when the woken
thread is not a queue tail (`hNotTail`).  Tail dual of
`storeTcbReceiveComplete_preserves_queueHeadBlockedConsistent`: the receiver is set `.ready`, so
if it were a tail the invariant would break — `hNotTail` rules that out (the rendezvous caller
discharges it from the post-pop state, where the woken head has been removed from its queue). -/
theorem storeTcbReceiveComplete_preserves_endpointQueueTailBlockedConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (msg : Option IpcMessage)
    (hInv : endpointQueueTailBlockedConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbReceiveComplete st tid msg = .ok st')
    (hNotTail : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.receiveQ.tail ≠ some tid ∧ ep.sendQ.tail ≠ some tid) :
    endpointQueueTailBlockedConsistent st' := by
  unfold storeTcbReceiveComplete at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hSt : storeObject tid.toObjId
        (.tcb { tcb with ipcState := .ready, pendingMessage := msg, pendingReceiveReply := none })
        st with
    | error e => simp [hSt] at hStep
    | ok pair =>
      simp only [hSt, Except.ok.injEq] at hStep; subst hStep
      have hFrame := fun x (h : x ≠ tid.toObjId) =>
        storeObject_objects_ne st pair.2 tid.toObjId x _ h hObjInv hSt
      have hEqAt := storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hSt
      intro epId ep tl tlTcb hEp hTcb
      have hNeEp : epId ≠ tid.toObjId := by
        intro h; subst h; rw [hEqAt] at hEp; cases hEp
      rw [hFrame epId hNeEp] at hEp
      by_cases hTlEq : tl.toObjId = tid.toObjId
      · have hTidEq := ThreadId.toObjId_injective tl tid hTlEq; subst hTidEq
        have ⟨hNR, hNS⟩ := hNotTail epId ep hEp
        exact ⟨fun h => absurd h hNR, fun h => absurd h hNS⟩
      · rw [hFrame tl.toObjId hTlEq] at hTcb
        exact hInv epId ep tl tlTcb hEp hTcb

/-- `storeTcbPendingMessage` only writes `pendingMessage`; `ipcState` and
`queueNext` are unchanged, so `queueNextBlockingConsistent` is preserved
unconditionally. -/
theorem storeTcbPendingMessage_preserves_queueNextBlockingConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (msg : Option IpcMessage)
    (hInv : queueNextBlockingConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbPendingMessage st tid msg = .ok st') :
    queueNextBlockingConsistent st' := by
  unfold storeTcbPendingMessage at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some origTcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { origTcb with pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore, Except.ok.injEq] at hStep; subst hStep
      have hEqAt := storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hStore
      have hOrigTcb := lookupTcb_some_objects st tid origTcb hLookup
      have hFrame : ∀ x, x ≠ tid.toObjId → pair.2.objects[x]? = st.objects[x]? :=
        fun x hNe => storeObject_objects_ne st pair.2 tid.toObjId x _ hNe hObjInv hStore
      intro a b tcbA tcbB hA hB hN
      -- The stored TCB keeps `ipcState` and `queueNext`; rewrite the post-state
      -- reads back to pre-state reads (preserving those fields) and apply hInv.
      by_cases hEqA : a.toObjId = tid.toObjId
      · have hATid := SeLe4n.ThreadId.toObjId_injective a tid hEqA; subst hATid
        rw [hEqAt] at hA
        have hIpcA : tcbA.ipcState = origTcb.ipcState := by cases Option.some.inj hA; rfl
        have hQNA : tcbA.queueNext = origTcb.queueNext := by cases Option.some.inj hA; rfl
        by_cases hEqB : b.toObjId = a.toObjId
        · rw [hEqB] at hB; rw [hEqAt] at hB
          have hIpcB : tcbB.ipcState = origTcb.ipcState := by cases Option.some.inj hB; rfl
          have hBeqA : b = a := SeLe4n.ThreadId.toObjId_injective b a hEqB
          rw [hIpcA, hIpcB]; rw [hQNA] at hN; rw [hBeqA] at hN
          exact hInv a a origTcb origTcb hOrigTcb hOrigTcb hN
        · rw [hFrame b.toObjId hEqB] at hB
          rw [hIpcA]; rw [hQNA] at hN
          exact hInv a b origTcb tcbB hOrigTcb hB hN
      · rw [hFrame a.toObjId hEqA] at hA
        by_cases hEqB : b.toObjId = tid.toObjId
        · rw [hEqB] at hB; rw [hEqAt] at hB
          have hIpcB : tcbB.ipcState = origTcb.ipcState := by cases Option.some.inj hB; rfl
          have hBTid := SeLe4n.ThreadId.toObjId_injective b tid hEqB; subst hBTid
          rw [hIpcB]
          exact hInv a b tcbA origTcb hA hOrigTcb hN
        · rw [hFrame b.toObjId hEqB] at hB
          exact hInv a b tcbA tcbB hA hB hN

-- ============================================================================
-- Section 9: endpointQueuePopHead / endpointQueueEnqueue frames
-- ============================================================================

/-- `endpointQueuePopHead` frames `queueNextBlockingConsistent`. The endpoint
store frames it directly; the head-removal store (`tid → next=none`) is a `none`
link (always safe); the optional relink of the new head re-stores its *own*
`queueNext`, so its new link is exactly the pre-state link, discharged by the
pre-state invariant (transported back through the endpoint store). -/
theorem endpointQueuePopHead_preserves_queueNextBlockingConsistent
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (rTid : SeLe4n.ThreadId) (rTcb : TCB)
    (hObjInv : st.objects.invExt)
    (hInv : queueNextBlockingConsistent st)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (rTid, rTcb, st')) :
    queueNextBlockingConsistent st' := by
  unfold endpointQueuePopHead at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
        simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp [hHead] at hStep
      | some headTid =>
        simp only [hHead] at hStep
        cases hLookup : lookupTcb st headTid with
        | none => simp [hLookup] at hStep
        | some tcb =>
          simp only [hLookup] at hStep
          revert hStep
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
            have hP1 := storeObject_endpoint_preserves_queueNextBlockingConsistent
              st pair.2 endpointId _ hInv hObjInv (by
                rw [show pair = ((), pair.2) from by cases pair; rfl] at hStore; exact hStore)
            cases hNext : tcb.queueNext with
            | none =>
              simp only []
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, _, rfl⟩
                exact storeTcbQueueLinks_none_preserves_queueNextBlockingConsistent
                  pair.2 st3 headTid none none hP1 hInv1 hFinal
            | some nextTid =>
              simp only []
              cases hLookupNext : lookupTcb pair.2 nextTid with
              | none => simp
              | some nextTcb =>
                simp only []
                cases hLink : storeTcbQueueLinks pair.2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp
                | ok st2 =>
                  simp only []
                  have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _ hInv1 hLink
                  -- The relink re-stores nextTid's own queueNext; the new link is
                  -- the pre-existing one, framed by `hInv` through the endpoint store.
                  have hP2 := storeTcbQueueLinks_preserves_queueNextBlockingConsistent
                    pair.2 st2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext
                    hP1 hInv1 hLink (by
                      -- The relink re-stores nextTid's own queueNext (= nextTcb.queueNext),
                      -- so the "new" link is one that already exists in pair.2; discharge
                      -- it directly from `hP1` (the post-endpoint-store invariant).
                      -- `hNextEq : nextTcb.queueNext = some b`, `hTcbN : pair.2[nextTid] = tcbN`.
                      intro b tcbN tcbB hNextEq hTcbN hB2
                      -- nextTid's stored TCB tcbN equals nextTcb (lookup agrees).
                      have hEq : tcbN = nextTcb := by
                        have hNTObj := lookupTcb_some_objects pair.2 nextTid nextTcb hLookupNext
                        rw [hNTObj] at hTcbN; cases hTcbN; rfl
                      subst hEq
                      exact hP1 nextTid b tcbN tcbB hTcbN hB2 hNextEq)
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, _, rfl⟩
                    exact storeTcbQueueLinks_none_preserves_queueNextBlockingConsistent
                      st2 st3 headTid none none hP2 hInv2 hFinal

/-- `endpointQueueEnqueue` frames `queueNextBlockingConsistent`. The enqueued
thread `tid` is `.ready` (enforced by the operation's guard), so the only new
link created — `tail.queueNext := some tid` — has a `.ready` target and is
vacuously compatible (`queueNextBlockingMatch _ .ready`). The endpoint store
frames directly; `tid`'s own final link is `none`. -/
theorem endpointQueueEnqueue_preserves_queueNextBlockingConsistent
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hInv : queueNextBlockingConsistent st)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    queueNextBlockingConsistent st' := by
  unfold endpointQueueEnqueue at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
        simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hLookup : lookupTcb st tid with
      | none => simp [hLookup] at hStep
      | some tcb =>
        simp only [hLookup] at hStep
        -- Extract the guard facts: tid is `.ready` with no existing links.
        split at hStep
        · simp at hStep
        · rename_i hReady
          rw [show ¬(tcb.ipcState ≠ .ready) ↔ tcb.ipcState = .ready from by
            constructor <;> intro h <;> simpa using h] at hReady
          split at hStep
          · simp at hStep
          · revert hStep
            cases hTail : (if isReceiveQ then ep.receiveQ else ep.sendQ).tail with
            | none =>
              cases hStore : storeObject endpointId _ st with
              | error e => simp
              | ok pair =>
                simp only []; intro hStep
                have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                have hP1 := storeObject_endpoint_preserves_queueNextBlockingConsistent
                  st pair.2 endpointId _ hInv hObjInv (by
                    rw [show pair = ((), pair.2) from by cases pair; rfl] at hStore; exact hStore)
                -- tid is the only enqueued thread; its final link is `none`.
                exact storeTcbQueueLinks_none_preserves_queueNextBlockingConsistent
                  pair.2 st' tid none (some QueuePPrev.endpointHead) hP1 hInv1 hStep
            | some tailTid =>
              cases hLookupTail : lookupTcb st tailTid with
              | none => simp [hLookupTail]
              | some tailTcb =>
                simp only [hLookupTail]
                cases hStore : storeObject endpointId _ st with
                | error e => simp
                | ok pair =>
                  simp only []
                  have hStore2 := hStore
                  rw [show pair = ((), pair.2) from by cases pair; rfl] at hStore2
                  have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                  have hP1 := storeObject_endpoint_preserves_queueNextBlockingConsistent
                    st pair.2 endpointId _ hInv hObjInv hStore2
                  -- tid's ipcState in pair.2 is still `.ready` (endpoint store kept it).
                  have hTidReadyPair : ∀ (t : TCB), pair.2.objects[tid.toObjId]? = some (.tcb t) →
                      t.ipcState = .ready := by
                    intro t hT
                    have hTidObj := lookupTcb_some_objects st tid tcb hLookup
                    have hNe : tid.toObjId ≠ endpointId := by
                      intro hEq; rw [hEq, hObj] at hTidObj; cases hTidObj
                    rw [storeObject_objects_ne' st endpointId tid.toObjId _ ((), pair.2) hNe hObjInv hStore2] at hT
                    rw [hTidObj] at hT; cases hT; exact hReady
                  cases hLink1 : storeTcbQueueLinks pair.2 tailTid tailTcb.queuePrev tailTcb.queuePPrev (some tid) with
                  | error e => simp
                  | ok st2 =>
                    simp only []; intro hStep
                    have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ tailTid _ _ _ hInv1 hLink1
                    -- The tail→tid link: discharge via `tid` being `.ready` in pair.2.
                    have hP2 := storeTcbQueueLinks_preserves_queueNextBlockingConsistent
                      pair.2 st2 tailTid tailTcb.queuePrev tailTcb.queuePPrev (some tid)
                      hP1 hInv1 hLink1 (by
                        intro b tcbTail tcbB hNextEq hTail2 hB2
                        -- next = some tid, so b = tid.
                        have hBeq : b = tid := by cases hNextEq; rfl
                        subst hBeq
                        rw [hTidReadyPair tcbB hB2]
                        exact queueNextBlockingMatch_ready_right _)
                    -- tid's final link is `none`.
                    exact storeTcbQueueLinks_none_preserves_queueNextBlockingConsistent
                      st2 st' tid (some tailTid) (some (.tcbNext tailTid)) hP2 hInv2 hStep

-- ============================================================================
-- Section 9b: storeTcbIpcState queueNextBlockingConsistent frames
-- ============================================================================

/-- `storeTcbIpcState` (ipcState-only TCB write) preserves
`queueNextBlockingConsistent` given the new ipcState is compatible with every
neighbour link (`hFwd`/`hBwd`).  Mirrors the `storeTcbIpcStateAndMessage`
variant; the pending-message field is irrelevant to this invariant. -/
theorem storeTcbIpcState_preserves_queueNextBlockingConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipcState : ThreadIpcState)
    (hInv : queueNextBlockingConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipcState = .ok st')
    (hFwd : ∀ (b : SeLe4n.ThreadId) (tcbTid tcbB : TCB),
      st.objects[tid.toObjId]? = some (.tcb tcbTid) →
      tcbTid.queueNext = some b →
      st.objects[b.toObjId]? = some (.tcb tcbB) →
      queueNextBlockingMatch ipcState tcbB.ipcState)
    (hBwd : ∀ (a : SeLe4n.ThreadId) (tcbA tcbTid : TCB),
      st.objects[a.toObjId]? = some (.tcb tcbA) →
      tcbA.queueNext = some tid →
      st.objects[tid.toObjId]? = some (.tcb tcbTid) →
      queueNextBlockingMatch tcbA.ipcState ipcState) :
    queueNextBlockingConsistent st' := by
  unfold storeTcbIpcState at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some origTcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { origTcb with ipcState := ipcState }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore, Except.ok.injEq] at hStep; subst hStep
      have hEqAt := storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hStore
      have hOrigTcb := lookupTcb_some_objects st tid origTcb hLookup
      have hFrame : ∀ x, x ≠ tid.toObjId → pair.2.objects[x]? = st.objects[x]? :=
        fun x hNe => storeObject_objects_ne st pair.2 tid.toObjId x _ hNe hObjInv hStore
      intro a b tcbA tcbB hA hB hN
      by_cases hEqA : a.toObjId = tid.toObjId
      · rw [hEqA] at hA; rw [hEqAt] at hA
        have hIpcA : tcbA.ipcState = ipcState := by cases Option.some.inj hA; rfl
        have hQNA : tcbA.queueNext = origTcb.queueNext := by cases Option.some.inj hA; rfl
        by_cases hEqB : b.toObjId = tid.toObjId
        · rw [hEqB] at hB; rw [hEqAt] at hB
          have hIpcB : tcbB.ipcState = ipcState := by cases Option.some.inj hB; rfl
          rw [hIpcA, hIpcB]; exact queueNextBlockingMatch_self _
        · rw [hFrame b.toObjId hEqB] at hB
          rw [hIpcA]; rw [hQNA] at hN
          exact hFwd b origTcb tcbB hOrigTcb hN hB
      · rw [hFrame a.toObjId hEqA] at hA
        by_cases hEqB : b.toObjId = tid.toObjId
        · rw [hEqB] at hB; rw [hEqAt] at hB
          have hIpcB : tcbB.ipcState = ipcState := by cases Option.some.inj hB; rfl
          have hBTid := SeLe4n.ThreadId.toObjId_injective b tid hEqB; subst hBTid
          rw [hIpcB]
          exact hBwd a tcbA origTcb hA hN hOrigTcb
        · rw [hFrame b.toObjId hEqB] at hB
          exact hInv a b tcbA tcbB hA hB hN

/-- `storeTcbIpcState … .ready` preserves `queueNextBlockingConsistent`
unconditionally (`.ready` is vacuously link-compatible). -/
theorem storeTcbIpcState_preserves_queueNextBlockingConsistent_ready
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) (hInv : queueNextBlockingConsistent st)
    (hStep : storeTcbIpcState st tid .ready = .ok st') :
    queueNextBlockingConsistent st' :=
  storeTcbIpcState_preserves_queueNextBlockingConsistent st st' tid .ready hInv hObjInv hStep
    (fun _ _ _ _ _ _ => queueNextBlockingMatch_ready_left _)
    (fun _ _ _ _ _ _ => queueNextBlockingMatch_ready_right _)

/-- `storeTcbIpcState … (.blockedOnNotification _)` preserves
`queueNextBlockingConsistent` unconditionally — a `.blockedOnNotification` thread
is link-compatible with anything (notification queues use a separate list, not the
`queueNext` chain). -/
theorem storeTcbIpcState_blockedOnNotification_preserves_queueNextBlockingConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (nid : SeLe4n.ObjId)
    (hObjInv : st.objects.invExt) (hInv : queueNextBlockingConsistent st)
    (hStep : storeTcbIpcState st tid (.blockedOnNotification nid) = .ok st') :
    queueNextBlockingConsistent st' :=
  storeTcbIpcState_preserves_queueNextBlockingConsistent st st' tid (.blockedOnNotification nid)
    hInv hObjInv hStep
    (fun _ _ tcbB _ _ _ => by unfold queueNextBlockingMatch; cases tcbB.ipcState <;> exact True.intro)
    (fun _ tcbA _ _ _ _ => by unfold queueNextBlockingMatch; cases tcbA.ipcState <;> exact True.intro)

-- ============================================================================
-- Section 10: queueHeadBlockedConsistent backward transfer + store frames
-- ============================================================================

/-- Generic backward transfer for `queueHeadBlockedConsistent`: preserved when
(a) every post-state endpoint exists identically in the pre-state, and (b) every
post-state TCB has a pre-state TCB at the same slot with the same `ipcState`. The
workhorse for object stores that touch neither endpoints' queue heads nor any
thread's `ipcState`. -/
theorem queueHeadBlockedConsistent_of_endpoint_tcb_backward
    (st st' : SystemState)
    (hEpBack : ∀ (eid : SeLe4n.ObjId) (ep : Endpoint),
      st'.objects[eid]? = some (.endpoint ep) → st.objects[eid]? = some (.endpoint ep))
    (hTcbBack : ∀ (y : SeLe4n.ThreadId) (tcb' : TCB),
      st'.objects[y.toObjId]? = some (.tcb tcb') →
      ∃ tcb, st.objects[y.toObjId]? = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState)
    (hInv : queueHeadBlockedConsistent st) :
    queueHeadBlockedConsistent st' := by
  intro epId ep hd tcbHd hEp hTcb
  have hEpPre := hEpBack epId ep hEp
  obtain ⟨tcbHdPre, hTcbPre, hIpc⟩ := hTcbBack hd tcbHd hTcb
  have hPre := hInv epId ep hd tcbHdPre hEpPre hTcbPre
  rw [← hIpc]
  exact ⟨fun h => hPre.1 h, fun h => hPre.2 h⟩

/-- `storeObject` of a non-endpoint object that is also not a TCB (e.g. a
notification, reply, schedContext) preserves `queueHeadBlockedConsistent`:
endpoints and all TCBs are unchanged. -/
theorem storeObject_nonEndpointNonTcb_preserves_queueHeadBlockedConsistent
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hObjInv : st.objects.invExt)
    (hNotEp : ∀ ep, obj ≠ .endpoint ep)
    (hNotTcb : ∀ tcb, obj ≠ .tcb tcb)
    (hInv : queueHeadBlockedConsistent st)
    (hStore : storeObject oid obj st = .ok ((), st')) :
    queueHeadBlockedConsistent st' := by
  have hEqAt := storeObject_objects_eq st st' oid obj hObjInv hStore
  refine queueHeadBlockedConsistent_of_endpoint_tcb_backward st st' ?_ ?_ hInv
  · intro eid ep hEp
    by_cases hEq : eid = oid
    · rw [hEq, hEqAt] at hEp; exact (hNotEp ep (Option.some.inj hEp)).elim
    · rwa [storeObject_objects_ne st st' oid eid obj hEq hObjInv hStore] at hEp
  · intro y tcb' hY
    by_cases hEq : y.toObjId = oid
    · rw [hEq, hEqAt] at hY; exact (hNotTcb tcb' (Option.some.inj hY)).elim
    · rw [storeObject_objects_ne st st' oid y.toObjId obj hEq hObjInv hStore] at hY
      exact ⟨tcb', hY, rfl⟩

/-- `storeObject` of a TCB preserving `ipcState` preserves
`queueHeadBlockedConsistent` (endpoints unchanged; the stored TCB keeps its
blocking state). -/
theorem storeObject_tcb_preserveIpc_preserves_queueHeadBlockedConsistent
    (st st' : SystemState) (tid₀ : SeLe4n.ThreadId) (oldTcb newTcb : TCB)
    (hObjInv : st.objects.invExt)
    (hOld : st.objects[tid₀.toObjId]? = some (.tcb oldTcb))
    (hSameIpc : newTcb.ipcState = oldTcb.ipcState)
    (hInv : queueHeadBlockedConsistent st)
    (hStore : storeObject tid₀.toObjId (.tcb newTcb) st = .ok ((), st')) :
    queueHeadBlockedConsistent st' := by
  have hEqAt := storeObject_objects_eq st st' tid₀.toObjId (.tcb newTcb) hObjInv hStore
  refine queueHeadBlockedConsistent_of_endpoint_tcb_backward st st' ?_ ?_ hInv
  · intro eid ep hEp
    by_cases hEq : eid = tid₀.toObjId
    · rw [hEq, hEqAt] at hEp; cases hEp
    · rwa [storeObject_objects_ne st st' tid₀.toObjId eid (.tcb newTcb) hEq hObjInv hStore] at hEp
  · intro y tcb' hY
    by_cases hEq : y.toObjId = tid₀.toObjId
    · rw [hEq, hEqAt] at hY
      obtain rfl : newTcb = tcb' := by
        simpa only [Option.some.injEq, KernelObject.tcb.injEq] using hY
      exact ⟨oldTcb, by rw [hEq]; exact hOld, hSameIpc.symm⟩
    · rw [storeObject_objects_ne st st' tid₀.toObjId y.toObjId (.tcb newTcb) hEq hObjInv hStore] at hY
      exact ⟨tcb', hY, rfl⟩

/-- `storeTcbIpcState` changes a thread's `ipcState`. It preserves
`queueHeadBlockedConsistent` provided the target is not a queue head
(`hNotHead`). Identical in shape to the `storeTcbIpcStateAndMessage` variant. -/
theorem storeTcbIpcState_preserves_queueHeadBlockedConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipcState : ThreadIpcState)
    (hInv : queueHeadBlockedConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipcState = .ok st')
    (hNotHead : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.receiveQ.head ≠ some tid ∧ ep.sendQ.head ≠ some tid) :
    queueHeadBlockedConsistent st' := by
  unfold storeTcbIpcState at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hSt : storeObject tid.toObjId (.tcb { tcb with ipcState := ipcState }) st with
    | error e => simp [hSt] at hStep
    | ok pair =>
      simp only [hSt, Except.ok.injEq] at hStep; subst hStep
      have hFrame := fun x (h : x ≠ tid.toObjId) =>
        storeObject_objects_ne st pair.2 tid.toObjId x _ h hObjInv hSt
      have hEqAt := storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hSt
      intro epId ep hd hdTcb hEp hTcb
      have hNeEp : epId ≠ tid.toObjId := by
        intro h; subst h; rw [hEqAt] at hEp; cases hEp
      rw [hFrame epId hNeEp] at hEp
      by_cases hHdEq : hd.toObjId = tid.toObjId
      · have hTidEq := ThreadId.toObjId_injective hd tid hHdEq; subst hTidEq
        have ⟨hNR, hNS⟩ := hNotHead epId ep hEp
        exact ⟨fun h => absurd h hNR, fun h => absurd h hNS⟩
      · rw [hFrame hd.toObjId hHdEq] at hTcb
        exact hInv epId ep hd hdTcb hEp hTcb

-- ============================================================================
-- Section: endpointQueueTailBlockedConsistent preservation (Finding F-2 dual)
-- These mirror the `queueHeadBlockedConsistent` frames above, for the queue
-- *tail* boundary.  The invariant reads the same fields (endpoint `*.tail`,
-- thread `ipcState`), so the frame combinator + store-op frames are head→tail
-- duals.
-- ============================================================================

/-- Tail dual of `queueHeadBlockedConsistent_of_endpoint_tcb_backward`: a step that preserves
endpoints and every TCB's `ipcState` preserves `endpointQueueTailBlockedConsistent`. -/
theorem endpointQueueTailBlockedConsistent_of_endpoint_tcb_backward
    (st st' : SystemState)
    (hEpBack : ∀ (eid : SeLe4n.ObjId) (ep : Endpoint),
      st'.objects[eid]? = some (.endpoint ep) → st.objects[eid]? = some (.endpoint ep))
    (hTcbBack : ∀ (y : SeLe4n.ThreadId) (tcb' : TCB),
      st'.objects[y.toObjId]? = some (.tcb tcb') →
      ∃ tcb, st.objects[y.toObjId]? = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState)
    (hInv : endpointQueueTailBlockedConsistent st) :
    endpointQueueTailBlockedConsistent st' := by
  intro epId ep tl tcbTl hEp hTcb
  have hEpPre := hEpBack epId ep hEp
  obtain ⟨tcbTlPre, hTcbPre, hIpc⟩ := hTcbBack tl tcbTl hTcb
  have hPre := hInv epId ep tl tcbTlPre hEpPre hTcbPre
  rw [← hIpc]
  exact ⟨fun h => hPre.1 h, fun h => hPre.2 h⟩

/-- ensureRunnable preserves endpointQueueTailBlockedConsistent (doesn't change objects). -/
theorem ensureRunnable_preserves_endpointQueueTailBlockedConsistent
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : endpointQueueTailBlockedConsistent st) :
    endpointQueueTailBlockedConsistent (ensureRunnable st tid) := by
  intro epId ep tl tcb hEp hTcb
  rw [show (ensureRunnable st tid).objects = st.objects from
    ensureRunnable_preserves_objects st tid] at hEp hTcb
  exact hInv epId ep tl tcb hEp hTcb

/-- removeRunnable preserves endpointQueueTailBlockedConsistent (doesn't change objects). -/
theorem removeRunnable_preserves_endpointQueueTailBlockedConsistent
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : endpointQueueTailBlockedConsistent st) :
    endpointQueueTailBlockedConsistent (removeRunnable st tid) := by
  intro epId ep tl tcb hEp hTcb
  rw [show (removeRunnable st tid).objects = st.objects from
    removeRunnable_preserves_objects st tid] at hEp hTcb
  exact hInv epId ep tl tcb hEp hTcb

/-- `storeObject` of a non-endpoint non-TCB object preserves `endpointQueueTailBlockedConsistent`. -/
theorem storeObject_nonEndpointNonTcb_preserves_endpointQueueTailBlockedConsistent
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hObjInv : st.objects.invExt)
    (hNotEp : ∀ ep, obj ≠ .endpoint ep)
    (hNotTcb : ∀ tcb, obj ≠ .tcb tcb)
    (hInv : endpointQueueTailBlockedConsistent st)
    (hStore : storeObject oid obj st = .ok ((), st')) :
    endpointQueueTailBlockedConsistent st' := by
  have hEqAt := storeObject_objects_eq st st' oid obj hObjInv hStore
  refine endpointQueueTailBlockedConsistent_of_endpoint_tcb_backward st st' ?_ ?_ hInv
  · intro eid ep hEp
    by_cases hEq : eid = oid
    · rw [hEq, hEqAt] at hEp; exact (hNotEp ep (Option.some.inj hEp)).elim
    · rwa [storeObject_objects_ne st st' oid eid obj hEq hObjInv hStore] at hEp
  · intro y tcb' hY
    by_cases hEq : y.toObjId = oid
    · rw [hEq, hEqAt] at hY; exact (hNotTcb tcb' (Option.some.inj hY)).elim
    · rw [storeObject_objects_ne st st' oid y.toObjId obj hEq hObjInv hStore] at hY
      exact ⟨tcb', hY, rfl⟩

/-- `storeObject` of a TCB preserving `ipcState` preserves `endpointQueueTailBlockedConsistent`. -/
theorem storeObject_tcb_preserveIpc_preserves_endpointQueueTailBlockedConsistent
    (st st' : SystemState) (tid₀ : SeLe4n.ThreadId) (oldTcb newTcb : TCB)
    (hObjInv : st.objects.invExt)
    (hOld : st.objects[tid₀.toObjId]? = some (.tcb oldTcb))
    (hSameIpc : newTcb.ipcState = oldTcb.ipcState)
    (hInv : endpointQueueTailBlockedConsistent st)
    (hStore : storeObject tid₀.toObjId (.tcb newTcb) st = .ok ((), st')) :
    endpointQueueTailBlockedConsistent st' := by
  have hEqAt := storeObject_objects_eq st st' tid₀.toObjId (.tcb newTcb) hObjInv hStore
  refine endpointQueueTailBlockedConsistent_of_endpoint_tcb_backward st st' ?_ ?_ hInv
  · intro eid ep hEp
    by_cases hEq : eid = tid₀.toObjId
    · rw [hEq, hEqAt] at hEp; cases hEp
    · rwa [storeObject_objects_ne st st' tid₀.toObjId eid (.tcb newTcb) hEq hObjInv hStore] at hEp
  · intro y tcb' hY
    by_cases hEq : y.toObjId = tid₀.toObjId
    · rw [hEq, hEqAt] at hY
      obtain rfl : newTcb = tcb' := by
        simpa only [Option.some.injEq, KernelObject.tcb.injEq] using hY
      exact ⟨oldTcb, by rw [hEq]; exact hOld, hSameIpc.symm⟩
    · rw [storeObject_objects_ne st st' tid₀.toObjId y.toObjId (.tcb newTcb) hEq hObjInv hStore] at hY
      exact ⟨tcb', hY, rfl⟩

/-- `storeTcbIpcStateAndMessage` preserves `endpointQueueTailBlockedConsistent` when the thread is
not a queue tail (`hNotTail`). -/
theorem storeTcbIpcStateAndMessage_preserves_endpointQueueTailBlockedConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipcState : ThreadIpcState) (msg : Option IpcMessage)
    (hInv : endpointQueueTailBlockedConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid ipcState msg = .ok st')
    (hNotTail : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.receiveQ.tail ≠ some tid ∧ ep.sendQ.tail ≠ some tid) :
    endpointQueueTailBlockedConsistent st' := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hSt : storeObject tid.toObjId
        (.tcb { tcb with ipcState := ipcState, pendingMessage := msg }) st with
    | error e => simp [hSt] at hStep
    | ok pair =>
      simp only [hSt, Except.ok.injEq] at hStep; subst hStep
      have hFrame := fun x (h : x ≠ tid.toObjId) =>
        storeObject_objects_ne st pair.2 tid.toObjId x _ h hObjInv hSt
      have hEqAt := storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hSt
      intro epId ep tl tlTcb hEp hTcb
      have hNeEp : epId ≠ tid.toObjId := by
        intro h; subst h; rw [hEqAt] at hEp; cases hEp
      rw [hFrame epId hNeEp] at hEp
      by_cases hTlEq : tl.toObjId = tid.toObjId
      · have hTidEq := ThreadId.toObjId_injective tl tid hTlEq; subst hTidEq
        have ⟨hNR, hNS⟩ := hNotTail epId ep hEp
        exact ⟨fun h => absurd h hNR, fun h => absurd h hNS⟩
      · rw [hFrame tl.toObjId hTlEq] at hTcb
        exact hInv epId ep tl tlTcb hEp hTcb

/-- `storeTcbPendingMessage` preserves `endpointQueueTailBlockedConsistent` (changes only
`pendingMessage`, never `ipcState` or any endpoint tail). -/
theorem storeTcbPendingMessage_preserves_endpointQueueTailBlockedConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (msg : Option IpcMessage)
    (hInv : endpointQueueTailBlockedConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbPendingMessage st tid msg = .ok st') :
    endpointQueueTailBlockedConsistent st' := by
  unfold storeTcbPendingMessage at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hSt : storeObject tid.toObjId
        (.tcb { tcb with pendingMessage := msg }) st with
    | error e => simp [hSt] at hStep
    | ok pair =>
      simp only [hSt, Except.ok.injEq] at hStep; subst hStep
      have hFrame := fun x (h : x ≠ tid.toObjId) =>
        storeObject_objects_ne st pair.2 tid.toObjId x _ h hObjInv hSt
      have hEqAt := storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hSt
      have hTcbObj := lookupTcb_some_objects st tid tcb hLookup
      intro epId ep tl tlTcb hEp hTcb
      have hNeEp : epId ≠ tid.toObjId := by
        intro h; subst h; rw [hEqAt] at hEp; cases hEp
      rw [hFrame epId hNeEp] at hEp
      by_cases hTlEq : tl.toObjId = tid.toObjId
      · rw [hTlEq, hEqAt] at hTcb
        simp only [Option.some.injEq, KernelObject.tcb.injEq] at hTcb
        subst hTcb
        exact hInv epId ep tl tcb hEp (by rw [hTlEq]; exact hTcbObj)
      · rw [hFrame tl.toObjId hTlEq] at hTcb
        exact hInv epId ep tl tlTcb hEp hTcb

/-- `storeTcbIpcState` preserves `endpointQueueTailBlockedConsistent` when the thread is not a
queue tail (`hNotTail`). -/
theorem storeTcbIpcState_preserves_endpointQueueTailBlockedConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipcState : ThreadIpcState)
    (hInv : endpointQueueTailBlockedConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipcState = .ok st')
    (hNotTail : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.receiveQ.tail ≠ some tid ∧ ep.sendQ.tail ≠ some tid) :
    endpointQueueTailBlockedConsistent st' := by
  unfold storeTcbIpcState at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hSt : storeObject tid.toObjId (.tcb { tcb with ipcState := ipcState }) st with
    | error e => simp [hSt] at hStep
    | ok pair =>
      simp only [hSt, Except.ok.injEq] at hStep; subst hStep
      have hFrame := fun x (h : x ≠ tid.toObjId) =>
        storeObject_objects_ne st pair.2 tid.toObjId x _ h hObjInv hSt
      have hEqAt := storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hSt
      intro epId ep tl tlTcb hEp hTcb
      have hNeEp : epId ≠ tid.toObjId := by
        intro h; subst h; rw [hEqAt] at hEp; cases hEp
      rw [hFrame epId hNeEp] at hEp
      by_cases hTlEq : tl.toObjId = tid.toObjId
      · have hTidEq := ThreadId.toObjId_injective tl tid hTlEq; subst hTidEq
        have ⟨hNR, hNS⟩ := hNotTail epId ep hEp
        exact ⟨fun h => absurd h hNR, fun h => absurd h hNS⟩
      · rw [hFrame tl.toObjId hTlEq] at hTcb
        exact hInv epId ep tl tlTcb hEp hTcb

-- ============================================================================
-- Section: queue-operation frames for queueHeadBlockedConsistent /
-- endpointQueueTailBlockedConsistent (Finding F-2 Slice 2b foundation).
-- `storeTcbQueueLinks` writes only a TCB's link fields, so it leaves every
-- endpoint and every `ipcState` untouched — both invariants follow directly
-- from the `_of_endpoint_tcb_backward` combinator + the existing endpoint /
-- ipcState backward lemmas.  The `storeObject_endpoint` frame takes a
-- caller-supplied `hNewHeads` / `hNewTails` obligation describing the new
-- endpoint's head / tail blocking, since an endpoint store *does* change the
-- queue-boundary fields the invariants read.
-- ============================================================================

/-- `storeTcbQueueLinks` preserves `queueHeadBlockedConsistent`: it stores a TCB
(endpoints unchanged) and keeps that TCB's `ipcState` (`tcbWithQueueLinks` only
touches link fields). -/
theorem storeTcbQueueLinks_preserves_queueHeadBlockedConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId)
    (hInv : queueHeadBlockedConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    queueHeadBlockedConsistent st' :=
  queueHeadBlockedConsistent_of_endpoint_tcb_backward st st'
    (fun eid ep hEp =>
      storeTcbQueueLinks_endpoint_backward st st' tid prev pprev next eid ep hObjInv hStep hEp)
    (fun y tcb' hY =>
      storeTcbQueueLinks_tcb_ipcState_backward st st' tid prev pprev next hObjInv hStep y tcb' hY)
    hInv

/-- `storeTcbQueueLinks` preserves `endpointQueueTailBlockedConsistent` (tail dual of the
`queueHeadBlockedConsistent` frame above). -/
theorem storeTcbQueueLinks_preserves_endpointQueueTailBlockedConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId)
    (hInv : endpointQueueTailBlockedConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    endpointQueueTailBlockedConsistent st' :=
  endpointQueueTailBlockedConsistent_of_endpoint_tcb_backward st st'
    (fun eid ep hEp =>
      storeTcbQueueLinks_endpoint_backward st st' tid prev pprev next eid ep hObjInv hStep hEp)
    (fun y tcb' hY =>
      storeTcbQueueLinks_tcb_ipcState_backward st st' tid prev pprev next hObjInv hStep y tcb' hY)
    hInv

/-- `storeObject` of an endpoint preserves `endpointQueueTailBlockedConsistent` provided the
*new* endpoint's `receiveQ`/`sendQ` tails are blocked on `eid` relative to the (unchanged)
pre-state TCBs (`hNewTails`).  An endpoint store touches no TCB, so every thread's `ipcState`
is identical pre/post — only the endpoint's own tail pointers can change, and `hNewTails`
discharges those. -/
theorem storeObject_endpoint_preserves_endpointQueueTailBlockedConsistent
    (st st' : SystemState) (eid : SeLe4n.ObjId) (ep' : Endpoint)
    (hObjInv : st.objects.invExt)
    (hInv : endpointQueueTailBlockedConsistent st)
    (hStore : storeObject eid (.endpoint ep') st = .ok ((), st'))
    (hNewTails : ∀ (tl : SeLe4n.ThreadId) (tcb : TCB),
        st.objects[tl.toObjId]? = some (.tcb tcb) →
        (ep'.receiveQ.tail = some tl → tcb.ipcState = .blockedOnReceive eid) ∧
        (ep'.sendQ.tail = some tl →
          tcb.ipcState = .blockedOnSend eid ∨ tcb.ipcState = .blockedOnCall eid)) :
    endpointQueueTailBlockedConsistent st' := by
  have hEqAt := storeObject_objects_eq st st' eid (.endpoint ep') hObjInv hStore
  intro epId ep tl tcbTl hEp hTcb
  have hTlNe : tl.toObjId ≠ eid := by
    intro hEq; rw [hEq, hEqAt] at hTcb; cases hTcb
  have hTcbPre : st.objects[tl.toObjId]? = some (.tcb tcbTl) := by
    rwa [storeObject_objects_ne st st' eid tl.toObjId _ hTlNe hObjInv hStore] at hTcb
  by_cases hEpEq : epId = eid
  · subst hEpEq
    rw [hEqAt] at hEp
    obtain rfl : ep' = ep := by
      simpa only [Option.some.injEq, KernelObject.endpoint.injEq] using hEp
    exact hNewTails tl tcbTl hTcbPre
  · have hEpPre : st.objects[epId]? = some (.endpoint ep) := by
      rwa [storeObject_objects_ne st st' eid epId _ hEpEq hObjInv hStore] at hEp
    exact hInv epId ep tl tcbTl hEpPre hTcbPre

/-- `storeObject` of an endpoint preserves `queueHeadBlockedConsistent` provided the *new*
endpoint's `receiveQ`/`sendQ` heads are blocked on `eid` relative to the (unchanged) pre-state
TCBs (`hNewHeads`).  Head dual of `storeObject_endpoint_preserves_endpointQueueTailBlockedConsistent`. -/
theorem storeObject_endpoint_preserves_queueHeadBlockedConsistent
    (st st' : SystemState) (eid : SeLe4n.ObjId) (ep' : Endpoint)
    (hObjInv : st.objects.invExt)
    (hInv : queueHeadBlockedConsistent st)
    (hStore : storeObject eid (.endpoint ep') st = .ok ((), st'))
    (hNewHeads : ∀ (hd : SeLe4n.ThreadId) (tcb : TCB),
        st.objects[hd.toObjId]? = some (.tcb tcb) →
        (ep'.receiveQ.head = some hd → tcb.ipcState = .blockedOnReceive eid) ∧
        (ep'.sendQ.head = some hd →
          tcb.ipcState = .blockedOnSend eid ∨ tcb.ipcState = .blockedOnCall eid)) :
    queueHeadBlockedConsistent st' := by
  have hEqAt := storeObject_objects_eq st st' eid (.endpoint ep') hObjInv hStore
  intro epId ep hd tcbHd hEp hTcb
  have hHdNe : hd.toObjId ≠ eid := by
    intro hEq; rw [hEq, hEqAt] at hTcb; cases hTcb
  have hTcbPre : st.objects[hd.toObjId]? = some (.tcb tcbHd) := by
    rwa [storeObject_objects_ne st st' eid hd.toObjId _ hHdNe hObjInv hStore] at hTcb
  by_cases hEpEq : epId = eid
  · subst hEpEq
    rw [hEqAt] at hEp
    obtain rfl : ep' = ep := by
      simpa only [Option.some.injEq, KernelObject.endpoint.injEq] using hEp
    exact hNewHeads hd tcbHd hTcbPre
  · have hEpPre : st.objects[epId]? = some (.endpoint ep) := by
      rwa [storeObject_objects_ne st st' eid epId _ hEpEq hObjInv hStore] at hEp
    exact hInv epId ep hd tcbHd hEpPre hTcbPre

/-- `endpointQueuePopHead` preserves `endpointQueueTailBlockedConsistent`: removing the head
either leaves the popped queue's tail unchanged (≥2 elements: the stored endpoint keeps
`tail := q.tail`) or empties the queue (1 element: `q' = {}`, `tail = none`, vacuous); the other
queue and every thread's `ipcState` are untouched.  Decomposes into the endpoint store (new
tails discharged from pre-state tail-blocked) followed by the head/successor relinks (link-only
TCB writes). -/
theorem endpointQueuePopHead_preserves_endpointQueueTailBlockedConsistent
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (rTid : SeLe4n.ThreadId) (rTcb : TCB)
    (hObjInv : st.objects.invExt)
    (hInv : endpointQueueTailBlockedConsistent st)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (rTid, rTcb, st')) :
    endpointQueueTailBlockedConsistent st' := by
  unfold endpointQueuePopHead at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
        simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp [hHead] at hStep
      | some headTid =>
        simp only [hHead] at hStep
        cases hLookup : lookupTcb st headTid with
        | none => simp [hLookup] at hStep
        | some tcb =>
          simp only [hLookup] at hStep
          revert hStep
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            have hInv1 : endpointQueueTailBlockedConsistent pair.2 := by
              refine storeObject_endpoint_preserves_endpointQueueTailBlockedConsistent
                st pair.2 endpointId _ hObjInv hInv
                (by rw [show pair = ((), pair.2) from by cases pair; rfl] at hStore; exact hStore) ?_
              intro tl tlTcb hTlPre
              have hEpTail := hInv endpointId ep tl tlTcb hObj hTlPre
              cases isReceiveQ with
              | true =>
                refine ⟨fun hRT => hEpTail.1 ?_, fun hST => hEpTail.2 hST⟩
                cases hN : tcb.queueNext with
                | none => simp [hN] at hRT
                | some nextTid => simpa [hN] using hRT
              | false =>
                refine ⟨fun hRT => hEpTail.1 hRT, fun hST => hEpTail.2 ?_⟩
                cases hN : tcb.queueNext with
                | none => simp [hN] at hST
                | some nextTid => simpa [hN] using hST
            have hObjInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
            cases hNext : tcb.queueNext with
            | none =>
              simp only []
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, _, rfl⟩
                exact storeTcbQueueLinks_preserves_endpointQueueTailBlockedConsistent
                  pair.2 st3 headTid none none none hInv1 hObjInv1 hFinal
            | some nextTid =>
              simp only []
              cases hLookupNext : lookupTcb pair.2 nextTid with
              | none => simp
              | some nextTcb =>
                simp only []
                cases hLink : storeTcbQueueLinks pair.2 nextTid none (some QueuePPrev.endpointHead)
                    nextTcb.queueNext with
                | error e => simp
                | ok st2 =>
                  simp only []
                  have hInv2 := storeTcbQueueLinks_preserves_endpointQueueTailBlockedConsistent
                    pair.2 st2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext
                    hInv1 hObjInv1 hLink
                  have hObjInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _
                    hObjInv1 hLink
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, _, rfl⟩
                    exact storeTcbQueueLinks_preserves_endpointQueueTailBlockedConsistent
                      st2 st3 headTid none none none hInv2 hObjInv2 hFinal

open SeLe4n.Model.SystemState in
/-- After `endpointQueueEnqueue`, the enqueued thread's `queuePrev` in the post-state is exactly the
queue's **old tail** (`= none` when the queue was empty).  Built from the operation's final
`storeTcbQueueLinks` on the enqueued thread (`queuePrev := some oldTail` / `none`). -/
theorem endpointQueueEnqueue_enqueued_queuePrev
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState) (ep : Endpoint)
    (hObjInv : st.objects.invExt)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hStep : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    ∃ tcb', st'.objects[tid.toObjId]? = some (.tcb tcb') ∧
      tcb'.queuePrev = (if isReceiveQ then ep.receiveQ else ep.sendQ).tail := by
  unfold endpointQueueEnqueue at hStep
  simp only [hObj] at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    split at hStep
    · simp at hStep
    · split at hStep
      · simp at hStep
      · revert hStep
        cases hTail : (if isReceiveQ then ep.receiveQ else ep.sendQ).tail with
        | none =>
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            simp only []; intro hStep
            have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
            obtain ⟨tcb', hTcb', hPrev'⟩ :=
              storeTcbQueueLinks_stored_queuePrev pair.2 st' tid none (some QueuePPrev.endpointHead)
                none hInv1 hStep
            exact ⟨tcb', hTcb', hPrev'⟩
        | some tailTid =>
          cases hLookupTail : lookupTcb st tailTid with
          | none => simp [hLookupTail]
          | some tailTcb =>
            simp only [hLookupTail]
            cases hStore : storeObject endpointId _ st with
            | error e => simp
            | ok pair =>
              simp only []
              cases hLink1 : storeTcbQueueLinks pair.2 tailTid tailTcb.queuePrev tailTcb.queuePPrev
                  (some tid) with
              | error e => simp
              | ok st2 =>
                simp only []; intro hStep
                have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ tailTid _ _ _ hInv1 hLink1
                obtain ⟨tcb', hTcb', hPrev'⟩ :=
                  storeTcbQueueLinks_stored_queuePrev st2 st' tid (some tailTid)
                    (some (QueuePPrev.tcbNext tailTid)) none hInv2 hStep
                exact ⟨tcb', hTcb', hPrev'⟩

open SeLe4n.Model.SystemState in
/-- After `endpointQueueEnqueue`, the enqueued thread's `queueNext` in the post-state is `none`
(it becomes the new tail; the operation's final `storeTcbQueueLinks` writes `next := none`).
Discharges the block-store `hFwd` (vacuously) in the enqueue transitions' qNBC establishers. -/
theorem endpointQueueEnqueue_enqueued_queueNext_none
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState) (ep : Endpoint)
    (hObjInv : st.objects.invExt)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hStep : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    ∃ tcb', st'.objects[tid.toObjId]? = some (.tcb tcb') ∧ tcb'.queueNext = none := by
  unfold endpointQueueEnqueue at hStep
  simp only [hObj] at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    split at hStep
    · simp at hStep
    · split at hStep
      · simp at hStep
      · revert hStep
        cases hTail : (if isReceiveQ then ep.receiveQ else ep.sendQ).tail with
        | none =>
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            simp only []; intro hStep
            have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
            exact storeTcbQueueLinks_stored_queueNext pair.2 st' tid none
              (some QueuePPrev.endpointHead) none hInv1 hStep
        | some tailTid =>
          cases hLookupTail : lookupTcb st tailTid with
          | none => simp [hLookupTail]
          | some tailTcb =>
            simp only [hLookupTail]
            cases hStore : storeObject endpointId _ st with
            | error e => simp
            | ok pair =>
              simp only []
              cases hLink1 : storeTcbQueueLinks pair.2 tailTid tailTcb.queuePrev tailTcb.queuePPrev
                  (some tid) with
              | error e => simp
              | ok st2 =>
                simp only []; intro hStep
                have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ tailTid _ _ _ hInv1 hLink1
                exact storeTcbQueueLinks_stored_queueNext st2 st' tid (some tailTid)
                  (some (QueuePPrev.tcbNext tailTid)) none hInv2 hStep

open SeLe4n.Model.SystemState in
/-- After `endpointQueueEnqueue`, the enqueued thread is the **tail** of the target queue
(`isReceiveQ ? receiveQ : sendQ`), and the *other* queue's tail is unchanged.  The minimal
endpoint-tail characterisation the enqueue transitions' `endpointQueueTailBlockedConsistent`
establishers need (the freshly-enqueued thread, once block-stored, is the blocked new tail).
The endpoint store sets the target queue's `tail := some tid`; the trailing `storeTcbQueueLinks`
writes only TCB links, so the endpoint (≠ any TCB objId) survives unchanged. -/
theorem endpointQueueEnqueue_enqueued_is_tail
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState) (ep : Endpoint)
    (hObjInv : st.objects.invExt)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hStep : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    ∃ ep', st'.objects[endpointId]? = some (.endpoint ep') ∧
      (if isReceiveQ then ep'.receiveQ.tail else ep'.sendQ.tail) = some tid ∧
      (if isReceiveQ then ep'.sendQ.tail else ep'.receiveQ.tail) =
        (if isReceiveQ then ep.sendQ.tail else ep.receiveQ.tail) := by
  unfold endpointQueueEnqueue at hStep
  simp only [hObj] at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    have hNeTid : endpointId ≠ tid.toObjId := by
      intro h
      rw [h, lookupTcb_some_objects st tid tcb hLookup] at hObj
      exact absurd hObj (by simp)
    split at hStep
    · simp at hStep
    · split at hStep
      · simp at hStep
      · revert hStep
        cases hTail : (if isReceiveQ then ep.receiveQ else ep.sendQ).tail with
        | none =>
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            simp only []; intro hStep
            have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
            have hEpPair := storeObject_objects_eq' st endpointId _ pair hObjInv hStore
            have hEpSt' : st'.objects[endpointId]? = pair.2.objects[endpointId]? :=
              storeTcbQueueLinks_preserves_objects_ne pair.2 st' tid none
                (some QueuePPrev.endpointHead) none endpointId hNeTid hInv1 hStep
            rw [hEpSt', hEpPair]
            refine ⟨_, rfl, ?_, ?_⟩ <;> (by_cases hR : isReceiveQ <;> simp [hR])
        | some tailTid =>
          cases hLookupTail : lookupTcb st tailTid with
          | none => simp [hLookupTail]
          | some tailTcb =>
            simp only [hLookupTail]
            cases hStore : storeObject endpointId _ st with
            | error e => simp
            | ok pair =>
              simp only []
              cases hLink1 : storeTcbQueueLinks pair.2 tailTid tailTcb.queuePrev tailTcb.queuePPrev
                  (some tid) with
              | error e => simp
              | ok st2 =>
                simp only []; intro hStep
                have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ tailTid _ _ _ hInv1 hLink1
                have hNeTail : endpointId ≠ tailTid.toObjId := by
                  intro h
                  rw [h, lookupTcb_some_objects st tailTid tailTcb hLookupTail] at hObj
                  exact absurd hObj (by simp)
                have hEpPair := storeObject_objects_eq' st endpointId _ pair hObjInv hStore
                have hEpSt2 : st2.objects[endpointId]? = pair.2.objects[endpointId]? :=
                  storeTcbQueueLinks_preserves_objects_ne pair.2 st2 tailTid _ _ _ endpointId
                    hNeTail hInv1 hLink1
                have hEpSt' : st'.objects[endpointId]? = st2.objects[endpointId]? :=
                  storeTcbQueueLinks_preserves_objects_ne st2 st' tid _ _ _ endpointId
                    hNeTid hInv2 hStep
                rw [hEpSt', hEpSt2, hEpPair]
                refine ⟨_, rfl, ?_, ?_⟩ <;> (by_cases hR : isReceiveQ <;> simp [hR])

-- ============================================================================
-- Section: frame family for `queueNextTargetBlocked` (Finding F-2 Slice 2c).
-- The invariant has the same `∀ a b, a.queueNext = some b → P(a,b)` shape as
-- `queueNextBlockingConsistent`, so the object-preserving frames transport it
-- identically.  The transition-level establishers (enqueue link + block-store,
-- pop relink) reuse the Slice-2b cores and are built per transition.
-- ============================================================================

/-- Pointwise object lookup equality transports `queueNextTargetBlocked`. -/
theorem queueNextTargetBlocked_of_objects_eq
    (st st' : SystemState)
    (hLk : ∀ (x : SeLe4n.ObjId), st'.objects[x]? = st.objects[x]?)
    (hInv : queueNextTargetBlocked st) :
    queueNextTargetBlocked st' := by
  intro a b tcbA tcbB hA hB hN
  rw [hLk] at hA hB
  exact hInv a b tcbA tcbB hA hB hN

/-- Backward combinator: if every `st'` TCB has an `st` counterpart with the **same** `ipcState`
and `queueNext`, then `queueNextTargetBlocked` transports from `st` to `st'`.  This is the workhorse
for every transition whose TCB writes leave both fields intact (queue-link relinks that the
establisher reasons about separately, scheduler frames, object stores). -/
theorem queueNextTargetBlocked_of_tcb_links_backward
    (st st' : SystemState)
    (hBack : ∀ (y : SeLe4n.ThreadId) (tcb' : TCB),
      st'.objects[y.toObjId]? = some (.tcb tcb') →
      ∃ tcb, st.objects[y.toObjId]? = some (.tcb tcb) ∧
        tcb.ipcState = tcb'.ipcState ∧ tcb.queueNext = tcb'.queueNext)
    (hInv : queueNextTargetBlocked st) :
    queueNextTargetBlocked st' := by
  intro a b tcbA tcbB hA hB hN
  obtain ⟨tcbAPre, hAPre, hIpcA, hNextA⟩ := hBack a tcbA hA
  obtain ⟨tcbBPre, hBPre, hIpcB, _⟩ := hBack b tcbB hB
  have hNPre : tcbAPre.queueNext = some b := by rw [hNextA]; exact hN
  have hPre := hInv a b tcbAPre tcbBPre hAPre hBPre hNPre
  rw [hIpcA, hIpcB] at hPre
  exact hPre

/-- `ensureRunnable` frames `queueNextTargetBlocked` (objects unchanged). -/
theorem ensureRunnable_preserves_queueNextTargetBlocked
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : queueNextTargetBlocked st) :
    queueNextTargetBlocked (ensureRunnable st tid) := by
  apply queueNextTargetBlocked_of_objects_eq st (ensureRunnable st tid)
  · intro x; unfold ensureRunnable; split
    · rfl
    · split <;> rfl
  · exact hInv

/-- `removeRunnable` frames `queueNextTargetBlocked` (objects unchanged). -/
theorem removeRunnable_preserves_queueNextTargetBlocked
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : queueNextTargetBlocked st) :
    queueNextTargetBlocked (removeRunnable st tid) := by
  apply queueNextTargetBlocked_of_objects_eq st (removeRunnable st tid)
  · intro x; unfold removeRunnable; simp
  · exact hInv

/-- `storeObject` of a non-TCB object frames `queueNextTargetBlocked` (no TCB's `ipcState`/`queueNext`
changes). -/
theorem storeObject_non_ep_non_tcb_preserves_queueNextTargetBlocked
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hInv : queueNextTargetBlocked st)
    (hObjInv : st.objects.invExt)
    (hNotTcb : ∀ tcb, obj ≠ .tcb tcb)
    (hPrevNotTcb : ∀ tcb, st.objects[oid]? ≠ some (.tcb tcb))
    (hStore : storeObject oid obj st = .ok ((), st')) :
    queueNextTargetBlocked st' := by
  have hFrame : ∀ x, x ≠ oid → st'.objects[x]? = st.objects[x]? :=
    fun x hNe => storeObject_objects_ne st st' oid x obj hNe hObjInv hStore
  have hEqAt : st'.objects[oid]? = some obj :=
    storeObject_objects_eq st st' oid obj hObjInv hStore
  intro a b tcbA tcbB hA hB hN
  have hNeA : a.toObjId ≠ oid := by
    intro hEq; rw [hEq] at hA; rw [hEqAt] at hA; cases hA; exact absurd rfl (hNotTcb tcbA)
  have hNeB : b.toObjId ≠ oid := by
    intro hEq; rw [hEq] at hB; rw [hEqAt] at hB; cases hB; exact absurd rfl (hNotTcb tcbB)
  rw [hFrame a.toObjId hNeA] at hA
  rw [hFrame b.toObjId hNeB] at hB
  exact hInv a b tcbA tcbB hA hB hN

/-- `storeObject` of an endpoint frames `queueNextTargetBlocked` (no TCB changes). -/
theorem storeObject_endpoint_preserves_queueNextTargetBlocked
    (st st' : SystemState) (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hInv : queueNextTargetBlocked st)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid (.endpoint ep) st = .ok ((), st')) :
    queueNextTargetBlocked st' := by
  have hFrame : ∀ x, x ≠ oid → st'.objects[x]? = st.objects[x]? :=
    fun x hNe => storeObject_objects_ne st st' oid x _ hNe hObjInv hStore
  have hEqAt : st'.objects[oid]? = some (.endpoint ep) :=
    storeObject_objects_eq st st' oid _ hObjInv hStore
  intro a b tcbA tcbB hA hB hN
  have hNeA : a.toObjId ≠ oid := by
    intro hEq; rw [hEq] at hA; rw [hEqAt] at hA; cases hA
  have hNeB : b.toObjId ≠ oid := by
    intro hEq; rw [hEq] at hB; rw [hEqAt] at hB; cases hB
  rw [hFrame a.toObjId hNeA] at hA
  rw [hFrame b.toObjId hNeB] at hB
  exact hInv a b tcbA tcbB hA hB hN

/-- `storeTcbQueueLinks` preserves `queueNextTargetBlocked`: it rewrites only `tid`'s link fields, so
the only *new* outgoing link is `tid.queueNext := next`; the caller discharges that one via
`hNewLink` (in the enqueue establisher, the paired block-store makes the new target blocked on the
same endpoint as `tid`).  Every other link is framed.  Mirrors
`storeTcbQueueLinks_preserves_queueNextBlockingConsistent`. -/
theorem storeTcbQueueLinks_preserves_queueNextTargetBlocked
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId)
    (hInv : queueNextTargetBlocked st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st')
    (hNewLink : ∀ (b : SeLe4n.ThreadId) (tcbTid tcbB : TCB),
      next = some b →
      st.objects[tid.toObjId]? = some (.tcb tcbTid) →
      st.objects[b.toObjId]? = some (.tcb tcbB) →
      (∀ ep, tcbTid.ipcState = .blockedOnReceive ep → tcbB.ipcState = .blockedOnReceive ep) ∧
      (∀ ep, (tcbTid.ipcState = .blockedOnSend ep ∨ tcbTid.ipcState = .blockedOnCall ep) →
        (tcbB.ipcState = .blockedOnSend ep ∨ tcbB.ipcState = .blockedOnCall ep))) :
    queueNextTargetBlocked st' := by
  have hFrame : ∀ x, x ≠ tid.toObjId → st'.objects[x]? = st.objects[x]? :=
    fun x hNe => storeTcbQueueLinks_preserves_objects_ne st st' tid prev pprev next x hNe hObjInv hStep
  obtain ⟨tcb', hTcb', hQN'⟩ :=
    storeTcbQueueLinks_stored_queueNext st st' tid prev pprev next hObjInv hStep
  have hIpcBack := storeTcbQueueLinks_tcb_ipcState_backward st st' tid prev pprev next hObjInv hStep
  intro a b tcbA tcbB hA hB hN
  by_cases hEqA : a.toObjId = tid.toObjId
  · by_cases hEqB : b.toObjId = tid.toObjId
    · -- a = b = target: same `ipcState` (self), consequent trivial.
      obtain ⟨origA, hOrigA, hIpcA⟩ := hIpcBack a tcbA hA
      obtain ⟨origB, hOrigB, hIpcB⟩ := hIpcBack b tcbB hB
      rw [hEqA] at hOrigA; rw [hEqB] at hOrigB
      rw [hOrigA] at hOrigB; cases Option.some.inj hOrigB
      have hSame : tcbA.ipcState = tcbB.ipcState := by rw [← hIpcA, ← hIpcB]
      exact ⟨fun _ h => hSame ▸ h, fun _ h => hSame ▸ h⟩
    · -- a = target, b ≠ target: the freshly-set link `tid → b`.
      obtain ⟨origA, hOrigA, hIpcA⟩ := hIpcBack a tcbA hA
      rw [hEqA] at hOrigA
      rw [hEqA] at hA; rw [hTcb'] at hA
      have hTcbEq : tcb' = tcbA := by cases Option.some.inj hA; rfl
      rw [← hTcbEq, hQN'] at hN
      rw [hFrame b.toObjId hEqB] at hB
      have hLink := hNewLink b origA tcbB hN hOrigA hB
      rw [hIpcA] at hLink
      exact hLink
  · -- a ≠ target.
    rw [hFrame a.toObjId hEqA] at hA
    by_cases hEqB : b.toObjId = tid.toObjId
    · -- b = target: same `ipcState` via backward (link `a → b` already in `st`).
      obtain ⟨origB, hOrigB, hIpcB⟩ := hIpcBack b tcbB hB
      rw [hEqB] at hOrigB
      have hPre := hInv a b tcbA origB hA (hEqB ▸ hOrigB) hN
      rw [hIpcB] at hPre
      exact hPre
    · -- neither.
      rw [hFrame b.toObjId hEqB] at hB
      exact hInv a b tcbA tcbB hA hB hN

/-- `storeTcbIpcStateAndMessage` preserves `queueNextTargetBlocked`: the only changed `ipcState` is
`tid`'s.  The caller discharges the two links that touch `tid` — `hFwd` for `tid`'s outgoing link
(`tid → b`: the new state propagates to `b`) and `hBwd` for any incoming link (`a → tid`: `a`'s state
propagates to the new state).  Mirrors `storeTcbIpcStateAndMessage_preserves_queueNextBlockingConsistent`. -/
theorem storeTcbIpcStateAndMessage_preserves_queueNextTargetBlocked
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipcState : ThreadIpcState) (msg : Option IpcMessage)
    (hInv : queueNextTargetBlocked st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid ipcState msg = .ok st')
    (hFwd : ∀ (b : SeLe4n.ThreadId) (tcbTid tcbB : TCB),
      st.objects[tid.toObjId]? = some (.tcb tcbTid) →
      tcbTid.queueNext = some b →
      st.objects[b.toObjId]? = some (.tcb tcbB) →
      (∀ ep, ipcState = .blockedOnReceive ep → tcbB.ipcState = .blockedOnReceive ep) ∧
      (∀ ep, (ipcState = .blockedOnSend ep ∨ ipcState = .blockedOnCall ep) →
        (tcbB.ipcState = .blockedOnSend ep ∨ tcbB.ipcState = .blockedOnCall ep)))
    (hBwd : ∀ (a : SeLe4n.ThreadId) (tcbA tcbTid : TCB),
      st.objects[a.toObjId]? = some (.tcb tcbA) →
      tcbA.queueNext = some tid →
      st.objects[tid.toObjId]? = some (.tcb tcbTid) →
      (∀ ep, tcbA.ipcState = .blockedOnReceive ep → ipcState = .blockedOnReceive ep) ∧
      (∀ ep, (tcbA.ipcState = .blockedOnSend ep ∨ tcbA.ipcState = .blockedOnCall ep) →
        (ipcState = .blockedOnSend ep ∨ ipcState = .blockedOnCall ep))) :
    queueNextTargetBlocked st' := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some origTcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { origTcb with ipcState := ipcState, pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep; subst hEq
      have hEqAt := storeObject_objects_eq' st tid.toObjId _ pair hObjInv hStore
      have hOrigTcb := lookupTcb_some_objects st tid origTcb hLookup
      have hFrame : ∀ x, x ≠ tid.toObjId → pair.snd.objects[x]? = st.objects[x]? :=
        fun x hNe => storeObject_objects_ne' st tid.toObjId x _ pair hNe hObjInv hStore
      intro a b tcbA tcbB hA hB hN
      by_cases hEqA : a.toObjId = tid.toObjId
      · rw [hEqA] at hA; rw [hEqAt] at hA
        have hIpcA : tcbA.ipcState = ipcState := by cases Option.some.inj hA; rfl
        have hQNA : tcbA.queueNext = origTcb.queueNext := by cases Option.some.inj hA; rfl
        by_cases hEqB : b.toObjId = tid.toObjId
        · rw [hEqB] at hB; rw [hEqAt] at hB
          have hIpcB : tcbB.ipcState = ipcState := by cases Option.some.inj hB; rfl
          rw [hIpcA, hIpcB]; exact ⟨fun _ h => h, fun _ h => h⟩
        · rw [hFrame b.toObjId hEqB] at hB
          rw [hIpcA]; rw [hQNA] at hN
          exact hFwd b origTcb tcbB hOrigTcb hN hB
      · rw [hFrame a.toObjId hEqA] at hA
        by_cases hEqB : b.toObjId = tid.toObjId
        · rw [hEqB] at hB; rw [hEqAt] at hB
          have hIpcB : tcbB.ipcState = ipcState := by cases Option.some.inj hB; rfl
          have hBTid := SeLe4n.ThreadId.toObjId_injective b tid hEqB; subst hBTid
          rw [hIpcB]
          exact hBwd a tcbA origTcb hA hN hOrigTcb
        · rw [hFrame b.toObjId hEqB] at hB
          exact hInv a b tcbA tcbB hA hB hN

/-- `storeTcbIpcStateAndMessage` leaves every TCB's `queueNext` untouched — it rewrites only
`ipcState`/`pendingMessage` (a record update that preserves `queueNext`).  For any post-state TCB
there is a pre-state TCB at the same id with the same `queueNext`. -/
theorem storeTcbIpcStateAndMessage_tcb_queueNext_backward
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipcState : ThreadIpcState) (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid ipcState msg = .ok st')
    (y : SeLe4n.ThreadId) (tcb' : TCB)
    (hTcb' : st'.objects[y.toObjId]? = some (.tcb tcb')) :
    ∃ tcb, st.objects[y.toObjId]? = some (.tcb tcb) ∧ tcb.queueNext = tcb'.queueNext := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some origTcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId
        (.tcb { origTcb with ipcState := ipcState, pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep; subst hEq
      by_cases hEqY : y.toObjId = tid.toObjId
      · rw [hEqY] at hTcb'
        rw [storeObject_objects_eq' st tid.toObjId _ pair hObjInv hStore] at hTcb'
        obtain rfl : ({ origTcb with ipcState := ipcState, pendingMessage := msg } : TCB) = tcb' := by
          simpa using hTcb'
        exact ⟨origTcb, by rw [hEqY]; exact lookupTcb_some_objects st tid origTcb hLookup, rfl⟩
      · rw [storeObject_objects_ne' st tid.toObjId y.toObjId _ pair hEqY hObjInv hStore] at hTcb'
        exact ⟨tcb', hTcb', rfl⟩

/-- `storeTcbIpcState` leaves every TCB's `queueNext` untouched (it rewrites only `ipcState`). -/
theorem storeTcbIpcState_tcb_queueNext_backward
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipcState : ThreadIpcState)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipcState = .ok st')
    (y : SeLe4n.ThreadId) (tcb' : TCB)
    (hTcb' : st'.objects[y.toObjId]? = some (.tcb tcb')) :
    ∃ tcb, st.objects[y.toObjId]? = some (.tcb tcb) ∧ tcb.queueNext = tcb'.queueNext := by
  unfold storeTcbIpcState at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some origTcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { origTcb with ipcState := ipcState }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep; subst hEq
      by_cases hEqY : y.toObjId = tid.toObjId
      · rw [hEqY] at hTcb'
        rw [storeObject_objects_eq' st tid.toObjId _ pair hObjInv hStore] at hTcb'
        obtain rfl : ({ origTcb with ipcState := ipcState } : TCB) = tcb' := by simpa using hTcb'
        exact ⟨origTcb, by rw [hEqY]; exact lookupTcb_some_objects st tid origTcb hLookup, rfl⟩
      · rw [storeObject_objects_ne' st tid.toObjId y.toObjId _ pair hEqY hObjInv hStore] at hTcb'
        exact ⟨tcb', hTcb', rfl⟩

/-- `endpointQueuePopHead` preserves `queueNextTargetBlocked`: the pop only *removes* the popped
head's outgoing link (`headTid.queueNext := none`, a frame whose `hNewLink` is vacuous) and re-stores
the new head's own `queueNext` unchanged (the relink, whose `hNewLink` is the pre-existing link
discharged from the post-endpoint-store invariant).  No new link is created, so the strict per-link
invariant is preserved.  Mirrors `endpointQueuePopHead_preserves_queueNextBlockingConsistent`. -/
theorem endpointQueuePopHead_preserves_queueNextTargetBlocked
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (rTid : SeLe4n.ThreadId) (rTcb : TCB)
    (hObjInv : st.objects.invExt)
    (hInv : queueNextTargetBlocked st)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (rTid, rTcb, st')) :
    queueNextTargetBlocked st' := by
  unfold endpointQueuePopHead at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
        simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp [hHead] at hStep
      | some headTid =>
        simp only [hHead] at hStep
        cases hLookup : lookupTcb st headTid with
        | none => simp [hLookup] at hStep
        | some tcb =>
          simp only [hLookup] at hStep
          revert hStep
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
            have hP1 := storeObject_endpoint_preserves_queueNextTargetBlocked
              st pair.2 endpointId _ hInv hObjInv (by
                rw [show pair = ((), pair.2) from by cases pair; rfl] at hStore; exact hStore)
            cases hNext : tcb.queueNext with
            | none =>
              simp only []
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, _, rfl⟩
                exact storeTcbQueueLinks_preserves_queueNextTargetBlocked
                  pair.2 st3 headTid none none none hP1 hInv1 hFinal
                  (fun b _ _ h _ _ => absurd h (by simp))
            | some nextTid =>
              simp only []
              cases hLookupNext : lookupTcb pair.2 nextTid with
              | none => simp
              | some nextTcb =>
                simp only []
                cases hLink : storeTcbQueueLinks pair.2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp
                | ok st2 =>
                  simp only []
                  have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _ hInv1 hLink
                  have hP2 := storeTcbQueueLinks_preserves_queueNextTargetBlocked
                    pair.2 st2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext
                    hP1 hInv1 hLink (by
                      intro b tcbN tcbB hNextEq hTcbN hB2
                      have hEq : tcbN = nextTcb := by
                        have hNTObj := lookupTcb_some_objects pair.2 nextTid nextTcb hLookupNext
                        rw [hNTObj] at hTcbN; cases hTcbN; rfl
                      subst hEq
                      exact hP1 nextTid b tcbN tcbB hTcbN hB2 hNextEq)
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, _, rfl⟩
                    exact storeTcbQueueLinks_preserves_queueNextTargetBlocked
                      st2 st3 headTid none none none hP2 hInv2 hFinal
                      (fun b _ _ h _ _ => absurd h (by simp))

/-- After `endpointQueuePopHead`, the popped head's `queuePrev` is `none` — the pop's final store
(`storeTcbQueueLinks headTid none none none`) clears its links and nothing afterward touches it. -/
theorem endpointQueuePopHead_popped_queuePrev_none
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (rTid : SeLe4n.ThreadId) (rTcb : TCB)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (rTid, rTcb, st')) :
    ∃ tcb, st'.objects[rTid.toObjId]? = some (.tcb tcb) ∧ tcb.queuePrev = none := by
  unfold endpointQueuePopHead at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
        simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp [hHead] at hStep
      | some headTid =>
        simp only [hHead] at hStep
        cases hLookup : lookupTcb st headTid with
        | none => simp [hLookup] at hStep
        | some tcb =>
          simp only [hLookup] at hStep
          revert hStep
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
            cases hNext : tcb.queueNext with
            | none =>
              simp only []
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                rintro ⟨rfl, _, rfl⟩
                exact storeTcbQueueLinks_stored_queuePrev pair.2 st3 headTid none none none hInv1 hFinal
            | some nextTid =>
              simp only []
              cases hLookupNext : lookupTcb pair.2 nextTid with
              | none => simp
              | some nextTcb =>
                simp only []
                cases hLink : storeTcbQueueLinks pair.2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp
                | ok st2 =>
                  simp only []
                  have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _ hInv1 hLink
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    rintro ⟨rfl, _, rfl⟩
                    exact storeTcbQueueLinks_stored_queuePrev st2 st3 headTid none none none hInv2 hFinal

/-- `storeTcbReceiveComplete` (sets `tid` `.ready`) preserves `queueNextTargetBlocked` provided `tid`
has no incoming `queueNext` link (`hNoIncoming`).  `tid` becomes a `.ready` *source* (its outgoing
links' strict-match obligation is vacuous — `.ready ≠ blockedOn…`); as a *target* it would break the
invariant, but `hNoIncoming` rules out any link to it.  Every other link is framed.  The rendezvous
wakes the popped head, whose `hNoIncoming` is `endpointQueuePopHead_popped_no_incoming`. -/
theorem storeTcbReceiveComplete_preserves_queueNextTargetBlocked
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (hInv : queueNextTargetBlocked st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbReceiveComplete st tid msg = .ok st')
    (hNoIncoming : ∀ (a : SeLe4n.ThreadId) (tcbA : TCB),
      st.objects[a.toObjId]? = some (.tcb tcbA) → tcbA.queueNext ≠ some tid) :
    queueNextTargetBlocked st' := by
  unfold storeTcbReceiveComplete at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some origTcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId
        (.tcb { origTcb with ipcState := .ready, pendingMessage := msg, pendingReceiveReply := none }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep; subst hEq
      have hEqAt := storeObject_objects_eq' st tid.toObjId _ pair hObjInv hStore
      have hFrame : ∀ x, x ≠ tid.toObjId → pair.snd.objects[x]? = st.objects[x]? :=
        fun x hNe => storeObject_objects_ne' st tid.toObjId x _ pair hNe hObjInv hStore
      intro a b tcbA tcbB hA hB hN
      by_cases hEqA : a.toObjId = tid.toObjId
      · rw [hEqA] at hA; rw [hEqAt] at hA
        have hIpcA : tcbA.ipcState = .ready := by cases Option.some.inj hA; rfl
        rw [hIpcA]
        exact ⟨fun ep h => by simp at h, fun ep h => by rcases h with h | h <;> simp at h⟩
      · rw [hFrame a.toObjId hEqA] at hA
        by_cases hEqB : b.toObjId = tid.toObjId
        · have hBTid := SeLe4n.ThreadId.toObjId_injective b tid hEqB; subst hBTid
          exact absurd hN (hNoIncoming a tcbA hA)
        · rw [hFrame b.toObjId hEqB] at hB
          exact hInv a b tcbA tcbB hA hB hN

end SeLe4n.Kernel
