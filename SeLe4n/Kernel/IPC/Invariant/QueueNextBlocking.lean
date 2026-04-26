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
  · intro x; unfold ensureRunnable; split <;> simp [*] <;> split <;> simp [*]
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

end SeLe4n.Kernel
