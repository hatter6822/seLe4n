-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-SM SM6.C: PRODUCTION (LANDED).  Entered the production import closure with
-- `endpointReplyOnCore` when the live `.reply` / `.replyRecv` dispatch was wired
-- through the cross-core reply stack.  See docs/planning/SMP_CROSS_CORE_IPC_PLAN.md §5 (SM6.C).

import SeLe4n.Kernel.IPC.CrossCore.EndpointReply
import SeLe4n.Kernel.IPC.Invariant

/-!
# WS-SM SM6.C — Cross-core reply IPC-invariant preservation

`endpointReplyOnCore` preserves the kernel's object-store integrity
(`objects.invExt`) and the IPC `ipcInvariant` (notification well-formedness).  The
cross-core reply differs from its single-core form only in the *scheduler*
placement of the woken caller; `ipcInvariant` is **lookup-only** (it reads the
state solely through `objects[·]?`), so the cross-core caller wake (`wakeThread`,
object-invisible on the already-`.ready` caller — the SM6.A/SM6.B object-
invisibility keystone) cannot disturb it.  The reply store step reuses the
single-core per-step preservation lemmas verbatim.

(The full fifteen-conjunct `ipcInvariantFull_perCore` preservation for every IPC
operation is the SM6.D aggregate; this module establishes the two load-bearing
conjuncts for the cross-core reply, matching SM6.A's `EndpointCallInvariant` and
SM6.B's `NotificationInvariant`.)
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  State characterisation: a reply either no-ops or stores-then-wakes
-- ============================================================================

/-- WS-SM SM6.C: the post-state of a cross-core reply is **either** the pre-state
(every error / non-`blockedOnReply` / wrong-replier path returns `st`) **or** the
cross-core wake of the reply-store result (the single success path).  This is the
control-flow factoring the invariant proofs case on. -/
theorem endpointReplyOnCore_state_eq
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) :
    (endpointReplyOnCore replier target msg executingCore st).1 = st
    ∨ ∃ tcb st', lookupTcb st target = some tcb
        ∧ storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) = .ok st'
        ∧ (endpointReplyOnCore replier target msg executingCore st).1
            = (wakeThread st' target executingCore).1 := by
  unfold endpointReplyOnCore
  split
  · exact Or.inl rfl
  split
  · exact Or.inl rfl
  split
  · exact Or.inl rfl
  · next tcb hLk =>
    split
    · next ep replyTarget =>
      split
      · exact Or.inl rfl
      · next expected =>
        -- PR #822 review 6J-lYm: the `replier == expected` gate was removed (authority
        -- is the reply cap), so the `some expected` arm is directly the store match.
        split
        · exact Or.inl rfl
        · next st' hStore => exact Or.inr ⟨tcb, st', hLk, hStore, rfl⟩
    · exact Or.inl rfl

-- ============================================================================
-- §2  `objects.invExt` preservation
-- ============================================================================

/-- WS-SM SM6.C: the cross-core reply preserves object-store integrity (`invExt`)
on every control path. -/
theorem endpointReplyOnCore_preserves_objects_invExt
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    (endpointReplyOnCore replier target msg executingCore st).1.objects.invExt := by
  rcases endpointReplyOnCore_state_eq replier target msg executingCore st with
    hEq | ⟨tcb, st', hLk, hStore, hEq⟩
  · rw [hEq]; exact hObjInv
  · rw [hEq]
    have hStore' : storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st' := by
      rw [← storeTcbIpcStateAndMessage_fromTcb_eq hLk]; exact hStore
    exact wakeThread_preserves_objects_invExt st' target executingCore
      (storeTcbIpcStateAndMessage_preserves_objects_invExt st st' target .ready (some msg) hObjInv hStore')

-- ============================================================================
-- §3  `ipcInvariant` (notification well-formedness) preservation
-- ============================================================================

/-- WS-SM SM6.C: the cross-core reply preserves the IPC `ipcInvariant`.  Mirrors
`endpointReply_preserves_ipcInvariant`, with the cross-core caller wake discharged
through the object-invisibility keystone (the caller is already `.ready` after the
reply store, so `wakeThread` does not disturb any object lookup). -/
theorem endpointReplyOnCore_preserves_ipcInvariant
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (hInv : ipcInvariant st) (hObjInv : st.objects.invExt) :
    ipcInvariant (endpointReplyOnCore replier target msg executingCore st).1 := by
  rcases endpointReplyOnCore_state_eq replier target msg executingCore st with
    hEq | ⟨tcb, st', hLk, hStore, hEq⟩
  · rw [hEq]; exact hInv
  · rw [hEq]
    have hStore' : storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st' := by
      rw [← storeTcbIpcStateAndMessage_fromTcb_eq hLk]; exact hStore
    have hInv1 := storeTcbIpcStateAndMessage_preserves_ipcInvariant st st' target .ready (some msg)
      hInv hObjInv hStore'
    have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st' target .ready (some msg)
      hObjInv hStore'
    obtain ⟨tr, hGet, hReady⟩ :=
      storeTcbIpcStateAndMessage_getTcb?_ipcState st st' target .ready (some msg) hObjInv hStore'
    exact fun oid ntfn h => hInv1 oid ntfn
      (by rwa [wakeThread_objects_getElem_eq_of_ready st' target executingCore tr hGet hReady hObjInv1 oid] at h)

end SeLe4n.Kernel
