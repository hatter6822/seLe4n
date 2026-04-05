/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.EndpointPreservation

/-! # Primitive preservation lemmas for `waitingThreadsPendingMessageNone`

These lemmas prove that low-level state mutation operations (storeObject,
storeTcbIpcState, removeRunnable, etc.) preserve the `waitingThreadsPendingMessageNone`
invariant. They are the building blocks for operation-level preservation proofs
in NotificationPreservation.lean and Structural.lean.

Extracted from Structural.lean to break a circular import dependency:
Structural imports NotificationPreservation, so these helpers must live in a
file that both can import. -/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- V3-G6 (M-PRF-5): Primitive preservation for waitingThreadsPendingMessageNone
-- ============================================================================

/-- `removeRunnable` only modifies the scheduler; objects are unchanged,
    so `waitingThreadsPendingMessageNone` is trivially preserved. -/
theorem removeRunnable_preserves_waitingThreadsPendingMessageNone
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : waitingThreadsPendingMessageNone st) :
    waitingThreadsPendingMessageNone (removeRunnable st tid) := by
  intro tid' tcb' hObj
  rw [removeRunnable_preserves_objects] at hObj
  exact hInv tid' tcb' hObj

/-- `ensureRunnable` only modifies the scheduler; objects are unchanged. -/
theorem ensureRunnable_preserves_waitingThreadsPendingMessageNone
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : waitingThreadsPendingMessageNone st) :
    waitingThreadsPendingMessageNone (ensureRunnable st tid) := by
  intro tid' tcb' hObj
  rw [ensureRunnable_preserves_objects] at hObj
  exact hInv tid' tcb' hObj

/-- `storeObject` at a non-TCB-target ID preserves `waitingThreadsPendingMessageNone`
    when the stored object is not a TCB. Since `storeObject` only modifies the
    entry at `id`, any TCB at `tid.toObjId ≠ id` is unchanged by frame. For the
    entry at `id` itself, if the new object is not a TCB, the invariant's universal
    quantifier over TCBs skips it. -/
theorem storeObject_nonTcb_preserves_waitingThreadsPendingMessageNone
    (st st' : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (hNotTcb : ∀ tcb, obj ≠ .tcb tcb)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject id obj st = .ok ((), st'))
    (hInv : waitingThreadsPendingMessageNone st) :
    waitingThreadsPendingMessageNone st' := by
  intro tid tcb hObj
  -- All TCBs at different IDs are unchanged by frame
  have hNe : tid.toObjId ≠ id := by
    intro hEq
    have hFrame := storeObject_objects_eq st st' id obj hObjInv hStore
    rw [hEq] at hObj; rw [hFrame] at hObj
    cases obj with
    | tcb t => exact absurd rfl (hNotTcb t)
    | _ => cases hObj
  have hFrame := storeObject_objects_ne st st' id tid.toObjId obj hNe hObjInv hStore
  rw [hFrame] at hObj
  exact hInv tid tcb hObj

/-- `storeTcbIpcState` preserves `waitingThreadsPendingMessageNone` when the
    new ipcState either (a) exits the invariant scope (e.g., `.ready`, `.blockedOnSend`),
    or (b) enters the scope while `pendingMessage` was already `none`. The latter
    condition is captured by requiring `pendingMessage = none` for the target thread
    when entering a blocking-receive state. -/
theorem storeTcbIpcState_preserves_waitingThreadsPendingMessageNone
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipcState : ThreadIpcState)
    (hObjInv : st.objects.invExt)
    (hStore : storeTcbIpcState st tid ipcState = .ok st')
    (hInv : waitingThreadsPendingMessageNone st)
    (hTarget : ∀ tcb, lookupTcb st tid = some tcb →
      match ipcState with
      | .blockedOnReceive _ => tcb.pendingMessage = none
      | .blockedOnNotification _ => tcb.pendingMessage = none
      | _ => True) :
    waitingThreadsPendingMessageNone st' := by
  unfold storeTcbIpcState at hStore
  cases hLk : lookupTcb st tid with
  | none => simp [hLk] at hStore
  | some tcb =>
    simp only [hLk] at hStore
    cases hSO : storeObject tid.toObjId (.tcb { tcb with ipcState := ipcState }) st with
    | error e => simp [hSO] at hStore
    | ok pair =>
      simp only [hSO, Except.ok.injEq] at hStore; subst hStore
      intro tid' tcb' hObj'
      by_cases hEq : tid'.toObjId = tid.toObjId
      · -- Same thread: modified TCB with new ipcState, same pendingMessage
        have hSelf := storeObject_objects_eq st pair.2 tid.toObjId
          (.tcb { tcb with ipcState := ipcState }) hObjInv hSO
        rw [hEq] at hObj'; rw [hSelf] at hObj'
        cases hObj'
        -- tcb' = { tcb with ipcState := ipcState }, pendingMessage = tcb.pendingMessage
        have h := hTarget tcb hLk
        cases ipcState with
        | blockedOnReceive _ => exact h
        | blockedOnNotification _ => exact h
        | blockedOnCall _ => exact h
        | _ => trivial
      · -- Different thread: frame
        have hNe' : tid'.toObjId ≠ tid.toObjId := hEq
        have hFrame := storeObject_objects_ne st pair.2 tid.toObjId tid'.toObjId
          (.tcb { tcb with ipcState := ipcState }) hNe' hObjInv hSO
        rw [hFrame] at hObj'
        exact hInv tid' tcb' hObj'

/-- `storeTcbIpcStateAndMessage` preserves `waitingThreadsPendingMessageNone` when the
    new state/message combination satisfies the invariant for blocking states. -/
theorem storeTcbIpcStateAndMessage_preserves_waitingThreadsPendingMessageNone
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipcState : ThreadIpcState) (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStore : storeTcbIpcStateAndMessage st tid ipcState msg = .ok st')
    (hInv : waitingThreadsPendingMessageNone st)
    (hTarget : match ipcState with
      | .blockedOnReceive _ => msg = none
      | .blockedOnNotification _ => msg = none
      | _ => True) :
    waitingThreadsPendingMessageNone st' := by
  unfold storeTcbIpcStateAndMessage at hStore
  cases hLk : lookupTcb st tid with
  | none => simp [hLk] at hStore
  | some tcb =>
    simp only [hLk] at hStore
    cases hSO : storeObject tid.toObjId
        (.tcb { tcb with ipcState := ipcState, pendingMessage := msg }) st with
    | error e => simp [hSO] at hStore
    | ok pair =>
      simp only [hSO, Except.ok.injEq] at hStore; subst hStore
      intro tid' tcb' hObj'
      by_cases hEq : tid'.toObjId = tid.toObjId
      · -- Same thread: new ipcState and pendingMessage
        have hSelf := storeObject_objects_eq st pair.2 tid.toObjId
          (.tcb { tcb with ipcState := ipcState, pendingMessage := msg }) hObjInv hSO
        rw [hEq] at hObj'; rw [hSelf] at hObj'
        cases hObj'
        cases ipcState with
        | blockedOnReceive _ => exact hTarget
        | blockedOnNotification _ => exact hTarget
        | blockedOnCall _ => exact hTarget
        | _ => trivial
      · have hNe' : tid'.toObjId ≠ tid.toObjId := hEq
        have hFrame := storeObject_objects_ne st pair.2 tid.toObjId tid'.toObjId
          (.tcb { tcb with ipcState := ipcState, pendingMessage := msg })
          hNe' hObjInv hSO
        rw [hFrame] at hObj'
        exact hInv tid' tcb' hObj'

/-- `storeTcbQueueLinks` only modifies queue link fields (queuePrev, queuePPrev,
    queueNext) via `tcbWithQueueLinks`. ipcState and pendingMessage are unchanged,
    so `waitingThreadsPendingMessageNone` is preserved. -/
theorem storeTcbQueueLinks_preserves_waitingThreadsPendingMessageNone
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStore : storeTcbQueueLinks st tid prev pprev next = .ok st')
    (hInv : waitingThreadsPendingMessageNone st) :
    waitingThreadsPendingMessageNone st' := by
  unfold storeTcbQueueLinks at hStore
  cases hLk : lookupTcb st tid with
  | none => simp [hLk] at hStore
  | some tcb =>
    simp only [hLk] at hStore
    cases hSO : storeObject tid.toObjId (.tcb (tcbWithQueueLinks tcb prev pprev next)) st with
    | error e => simp [hSO] at hStore
    | ok pair =>
      simp only [hSO, Except.ok.injEq] at hStore; subst hStore
      -- Extract objects lookup from lookupTcb
      have hObjOrig : st.objects[tid.toObjId]? = some (.tcb tcb) := by
        unfold lookupTcb at hLk; split at hLk
        · simp at hLk
        · split at hLk
          next t hObj => exact Option.some.inj hLk ▸ hObj
          all_goals simp at hLk
      intro tid' tcb' hObj'
      by_cases hEq : tid'.toObjId = tid.toObjId
      · -- Same thread: ipcState and pendingMessage unchanged by tcbWithQueueLinks
        have hSelf := storeObject_objects_eq st pair.2 tid.toObjId
          (.tcb (tcbWithQueueLinks tcb prev pprev next)) hObjInv hSO
        rw [hEq] at hObj'; rw [hSelf] at hObj'
        simp only [Option.some.injEq, KernelObject.tcb.injEq] at hObj'
        subst hObj'
        simp only [tcbWithQueueLinks]
        exact hInv tid tcb hObjOrig
      · -- Different thread: frame
        have hFrame := storeObject_objects_ne st pair.2 tid.toObjId tid'.toObjId
          (.tcb (tcbWithQueueLinks tcb prev pprev next)) hEq hObjInv hSO
        rw [hFrame] at hObj'
        exact hInv tid' tcb' hObj'

/-- `storeTcbPendingMessage` only modifies `pendingMessage` (not `ipcState`).
    Preservation requires that for threads in blocking states, the new message
    must be `none`. For threads not in blocking states, any message is fine. -/
theorem storeTcbPendingMessage_preserves_waitingThreadsPendingMessageNone
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStore : storeTcbPendingMessage st tid msg = .ok st')
    (hInv : waitingThreadsPendingMessageNone st)
    (hTarget : ∀ tcb, lookupTcb st tid = some tcb →
      match tcb.ipcState with
      | .blockedOnReceive _ => msg = none
      | .blockedOnNotification _ => msg = none
      | _ => True) :
    waitingThreadsPendingMessageNone st' := by
  unfold storeTcbPendingMessage at hStore
  cases hLk : lookupTcb st tid with
  | none => simp [hLk] at hStore
  | some tcb =>
    simp only [hLk] at hStore
    cases hSO : storeObject tid.toObjId (.tcb { tcb with pendingMessage := msg }) st with
    | error e => simp [hSO] at hStore
    | ok pair =>
      simp only [hSO, Except.ok.injEq] at hStore; subst hStore
      have hObjOrig : st.objects[tid.toObjId]? = some (.tcb tcb) := by
        unfold lookupTcb at hLk; split at hLk
        · simp at hLk
        · split at hLk
          next t hObj => exact Option.some.inj hLk ▸ hObj
          all_goals simp at hLk
      intro tid' tcb' hObj'
      by_cases hEq : tid'.toObjId = tid.toObjId
      · have hSelf := storeObject_objects_eq st pair.2 tid.toObjId
          (.tcb { tcb with pendingMessage := msg }) hObjInv hSO
        rw [hEq] at hObj'; rw [hSelf] at hObj'
        simp only [Option.some.injEq, KernelObject.tcb.injEq] at hObj'
        subst hObj'
        dsimp only []
        exact hTarget tcb hLk
      · have hFrame := storeObject_objects_ne st pair.2 tid.toObjId tid'.toObjId
          (.tcb { tcb with pendingMessage := msg }) hEq hObjInv hSO
        rw [hFrame] at hObj'
        exact hInv tid' tcb' hObj'

end SeLe4n.Kernel
