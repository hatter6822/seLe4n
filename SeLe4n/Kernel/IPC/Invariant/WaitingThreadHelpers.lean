-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.EndpointPreservation

/-! # Primitive preservation lemmas for `blockedThreadsPendingMessageConsistent`
    (notification wait-list helpers)

**AN3-F (IPC LOW #1) scope note.**  Despite the historical file name
`WaitingThreadHelpers`, the helpers in this module are specifically
the *notification wait-list* invariant primitives: they prove that
low-level state mutations (`storeObject`, `storeTcbIpcState`,
`removeRunnable`, the `storeTcbIpcStateAndMessage_*` family, ...)
preserve `blockedThreadsPendingMessageConsistent`, the invariant tying
`pendingMessage` to the blocking state -- a thread parked to collect
(`.blockedOnReceive` / `.blockedOnNotification`) holds nothing, a thread
parked to deliver (`.blockedOnSend` / `.blockedOnCall`) holds what it is
delivering.  The file does NOT cover endpoint wait lists — those are
handled in `IPC/Invariant/EndpointPreservation.lean`.  The broader
`WaitingThreadHelpers` name is preserved for git-history continuity;
treat it as an alias for "notification-wait-list helpers" when reading
call sites.

These lemmas prove that low-level state mutation operations (storeObject,
storeTcbIpcState, removeRunnable, etc.) preserve the `blockedThreadsPendingMessageConsistent`
invariant. They are the building blocks for operation-level preservation proofs
in NotificationPreservation.lean and Structural.lean.

Extracted from Structural.lean to break a circular import dependency:
Structural imports NotificationPreservation, so these helpers must live in a
file that both can import. -/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- V3-G6 (M-PRF-5): Primitive preservation for blockedThreadsPendingMessageConsistent
-- ============================================================================

/-- `removeRunnable` only modifies the scheduler; objects are unchanged,
    so `blockedThreadsPendingMessageConsistent` is trivially preserved. -/
theorem removeRunnable_preserves_blockedThreadsPendingMessageConsistent
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : blockedThreadsPendingMessageConsistent st) :
    blockedThreadsPendingMessageConsistent (removeRunnable st tid) := by
  intro tid' tcb' hObj
  rw [removeRunnable_preserves_objects] at hObj
  exact hInv tid' tcb' hObj

/-- `ensureRunnable` only modifies the scheduler; objects are unchanged. -/
theorem ensureRunnable_preserves_blockedThreadsPendingMessageConsistent
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : blockedThreadsPendingMessageConsistent st) :
    blockedThreadsPendingMessageConsistent (ensureRunnable st tid) := by
  intro tid' tcb' hObj
  rw [ensureRunnable_preserves_objects] at hObj
  exact hInv tid' tcb' hObj

/-- `storeObject` at a non-TCB-target ID preserves `blockedThreadsPendingMessageConsistent`
    when the stored object is not a TCB. Since `storeObject` only modifies the
    entry at `id`, any TCB at `tid.toObjId ≠ id` is unchanged by frame. For the
    entry at `id` itself, if the new object is not a TCB, the invariant's universal
    quantifier over TCBs skips it. -/
theorem storeObject_nonTcb_preserves_blockedThreadsPendingMessageConsistent
    (st st' : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (hNotTcb : ∀ tcb, obj ≠ .tcb tcb)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject id obj st = .ok ((), st'))
    (hInv : blockedThreadsPendingMessageConsistent st) :
    blockedThreadsPendingMessageConsistent st' := by
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

/-- `storeTcbIpcState` preserves `blockedThreadsPendingMessageConsistent` when the
    new ipcState either exits the invariant's scope (`.ready`, `.blockedOnReply`,
    ...) or enters it with the target thread's `pendingMessage` already in the
    shape that state requires: absent for the two collecting states, present for
    the two delivering ones. `hTarget` is that obligation, discharged at each
    call site from what the transition knows about the thread it is parking. -/
theorem storeTcbIpcState_preserves_blockedThreadsPendingMessageConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipcState : ThreadIpcState)
    (hObjInv : st.objects.invExt)
    (hStore : storeTcbIpcState st tid ipcState = .ok st')
    (hInv : blockedThreadsPendingMessageConsistent st)
    (hTarget : ∀ tcb, lookupTcb st tid = some tcb →
      match ipcState with
      | .blockedOnReceive _ => tcb.pendingMessage = none
      | .blockedOnNotification _ => tcb.pendingMessage = none
      | .blockedOnSend _ => tcb.pendingMessage.isSome
      | .blockedOnCall _ => tcb.pendingMessage.isSome
      | _ => True) :
    blockedThreadsPendingMessageConsistent st' := by
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
        | blockedOnSend _ => exact h
        | blockedOnCall _ => exact h
        | _ => trivial
      · -- Different thread: frame
        have hNe' : tid'.toObjId ≠ tid.toObjId := hEq
        have hFrame := storeObject_objects_ne st pair.2 tid.toObjId tid'.toObjId
          (.tcb { tcb with ipcState := ipcState }) hNe' hObjInv hSO
        rw [hFrame] at hObj'
        exact hInv tid' tcb' hObj'

/-- `storeTcbIpcStateAndMessage` preserves `blockedThreadsPendingMessageConsistent` when the
    new state/message combination satisfies the invariant for blocking states. -/
theorem storeTcbIpcStateAndMessage_preserves_blockedThreadsPendingMessageConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipcState : ThreadIpcState) (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStore : storeTcbIpcStateAndMessage st tid ipcState msg = .ok st')
    (hInv : blockedThreadsPendingMessageConsistent st)
    (hTarget : match ipcState with
      | .blockedOnReceive _ => msg = none
      | .blockedOnNotification _ => msg = none
      | .blockedOnSend _ => msg.isSome
      | .blockedOnCall _ => msg.isSome
      | _ => True) :
    blockedThreadsPendingMessageConsistent st' := by
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
        | blockedOnSend _ => exact hTarget
        | blockedOnCall _ => exact hTarget
        | _ => trivial
      · have hNe' : tid'.toObjId ≠ tid.toObjId := hEq
        have hFrame := storeObject_objects_ne st pair.2 tid.toObjId tid'.toObjId
          (.tcb { tcb with ipcState := ipcState, pendingMessage := msg })
          hNe' hObjInv hSO
        rw [hFrame] at hObj'
        exact hInv tid' tcb' hObj'

/-- Finding F-1: `storeTcbReceiveComplete` preserves
`blockedThreadsPendingMessageConsistent`.  The stored ipcState is `.ready` (non-waiting),
so no `hTarget` obligation on `msg` is needed.  Mirror of
`storeTcbIpcStateAndMessage_preserves_blockedThreadsPendingMessageConsistent`. -/
theorem storeTcbReceiveComplete_preserves_blockedThreadsPendingMessageConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStore : storeTcbReceiveComplete st tid msg = .ok st')
    (hInv : blockedThreadsPendingMessageConsistent st) :
    blockedThreadsPendingMessageConsistent st' := by
  unfold storeTcbReceiveComplete at hStore
  cases hLk : lookupTcb st tid with
  | none => simp [hLk] at hStore
  | some tcb =>
    simp only [hLk] at hStore
    cases hSO : storeObject tid.toObjId
        (.tcb { tcb with ipcState := .ready, pendingMessage := msg, pendingReceiveReply := none }) st with
    | error e => simp [hSO] at hStore
    | ok pair =>
      simp only [hSO, Except.ok.injEq] at hStore; subst hStore
      intro tid' tcb' hObj'
      by_cases hEq : tid'.toObjId = tid.toObjId
      · -- Same thread: new ipcState `.ready` is non-waiting → trivial
        have hSelf := storeObject_objects_eq st pair.2 tid.toObjId
          (.tcb { tcb with ipcState := .ready, pendingMessage := msg, pendingReceiveReply := none }) hObjInv hSO
        rw [hEq] at hObj'; rw [hSelf] at hObj'
        cases hObj'
        trivial
      · have hNe' : tid'.toObjId ≠ tid.toObjId := hEq
        have hFrame := storeObject_objects_ne st pair.2 tid.toObjId tid'.toObjId
          (.tcb { tcb with ipcState := .ready, pendingMessage := msg, pendingReceiveReply := none })
          hNe' hObjInv hSO
        rw [hFrame] at hObj'
        exact hInv tid' tcb' hObj'

/-- `storeTcbQueueLinks` only modifies queue link fields (queuePrev, queuePPrev,
    queueNext) via `tcbWithQueueLinks`. ipcState and pendingMessage are unchanged,
    so `blockedThreadsPendingMessageConsistent` is preserved. -/
theorem storeTcbQueueLinks_preserves_blockedThreadsPendingMessageConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStore : storeTcbQueueLinks st tid prev pprev next = .ok st')
    (hInv : blockedThreadsPendingMessageConsistent st) :
    blockedThreadsPendingMessageConsistent st' := by
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
theorem storeTcbPendingMessage_preserves_blockedThreadsPendingMessageConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStore : storeTcbPendingMessage st tid msg = .ok st')
    (hInv : blockedThreadsPendingMessageConsistent st)
    (hTarget : ∀ tcb, lookupTcb st tid = some tcb →
      match tcb.ipcState with
      | .blockedOnReceive _ => msg = none
      | .blockedOnNotification _ => msg = none
      | .blockedOnSend _ => msg.isSome
      | .blockedOnCall _ => msg.isSome
      | _ => True) :
    blockedThreadsPendingMessageConsistent st' := by
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

-- ============================================================================
-- WS-RR RR3.2: `consumeCallerReply` primitive preservation, relocated here.
--
-- This theorem used to live in `Structural/DualQueueMembership.lean`, and it
-- was the ONLY name that module supplied to `Structural/PerOperation.lean`.
-- That single edge pinned `PerOperation` downstream of the `ipcInvariantFull`
-- bundles, which is why the bundles could not call `PerOperation`'s own
-- per-transition `blockedThreadsPendingMessageConsistent` establishers and
-- threaded the conjunct as a post-state hypothesis instead.  Sitting upstream
-- of both, it reverses the edge: `DualQueueMembership` now imports
-- `PerOperation` and calls the establishers.
--
-- The home is the right one on merit, not just for ordering: this file is the
-- primitive-preservation module for `blockedThreadsPendingMessageConsistent`,
-- and `consumeCallerReply` is a `Model/State.lean` primitive whose proof rests
-- on nothing but that module's `consumeCallerReply_tcb_forward` transport.
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- PR #827 #3 fold: `consumeCallerReply` preserves
`blockedThreadsPendingMessageConsistent` — `ipcState` and `pendingMessage` are both
preserved TCB fields. -/
theorem consumeCallerReply_preserves_blockedThreadsPendingMessageConsistent
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt) (hInv : blockedThreadsPendingMessageConsistent st)
    (hStep : consumeCallerReply caller rid st = .ok ((), st')) :
    blockedThreadsPendingMessageConsistent st' := by
  have hFwd := consumeCallerReply_tcb_forward st st' caller rid hObjInv hStep
  intro tid tcb hObj
  obtain ⟨ty, hSt, hIS, hPM, _⟩ := hFwd tid.toObjId tcb hObj
  have hbase := hInv tid ty hSt
  rw [hIS, hPM]
  exact hbase

end SeLe4n.Kernel
