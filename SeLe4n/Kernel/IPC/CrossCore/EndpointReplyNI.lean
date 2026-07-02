-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM SM6.C.8 cross-core IPC (per-core / ∀-core
-- non-interference for the reply path; see
-- docs/planning/SMP_CROSS_CORE_IPC_PLAN.md).

import SeLe4n.Kernel.IPC.CrossCore.EndpointReply
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallNiPerCore

/-!
# WS-SM SM6.C.8 — Cross-core reply non-interference

The information-flow slice of SM6.C: a cross-core `endpointReplyOnCore` that
unblocks a **non-observable** caller is invisible to a low observer.

* **`endpointReplyOnCore_reply_path_NI`** — the boot-core `projectState` form
  (the cross-core variant of the single-core reply projection preservation).
* **`endpointReplyOnCore_reply_path_NI_smp`** — the per-core / ∀-core
  `lowEquivalent_smp` strengthening: a high reply is invisible on *every* core,
  including the remote core the caller is woken onto, not just the boot core.

The new content over the single-core proof is the projection preservation of the
cross-core wake step — `wakeThread` (the caller wake routed to its home core) —
for a high thread on an *arbitrary* core.  It composes with the single-core
`storeTcbIpcStateAndMessage` projection lemma (boot core) and the SM6.A per-core
projection family (the `*_preserves_projectionOnCore` lemmas).  The reply store is
the `_fromTcb` variant; it is bridged to the plain form via
`storeTcbIpcStateAndMessage_fromTcb_eq`, exactly as the SM6.C invariant proofs do.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

-- ============================================================================
-- §1  SM6.C.8 — boot-core non-interference (`projectState`)
-- ============================================================================

/-- WS-SM SM6.C.8 (`endpointReply_perCore_NI`, boot-core form): a cross-core reply
that unblocks a **non-observable** caller is invisible to a low observer —
`projectState` of the post-state equals that of the pre-state.  No covert channel
is opened: the reply-payload / `.ready` write to the caller's TCB and the
cross-core caller wake all touch only high state. -/
theorem endpointReplyOnCore_reply_path_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st st' : SystemState) (tcb : TCB) (ep : SeLe4n.ObjId) (expected : SeLe4n.ThreadId)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hLk : lookupTcb st target = some tcb)
    (hIpc : tcb.ipcState = .blockedOnReply ep (some expected))
    (hStore : storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) = .ok st')
    (hObjInv : st.objects.invExt)
    -- PR #827 review #3 (reply-fold): structural completeness for the folded
    -- consume's `.reply` re-store projection-invisibility (mirrors the SM6.A
    -- `endpointCallOnCore_call_path_NI` hypotheses).
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hIdxComplete : objectIndexSetComplete st)
    (hTargetHigh : threadObservable ctx observer target = false)
    (hTargetObjHigh : objectObservable ctx observer target.toObjId = false) :
    projectState ctx observer (endpointReplyOnCore replier target msg executingCore st).1
      = projectState ctx observer st := by
  have hStore' : storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st' := by
    rw [← storeTcbIpcStateAndMessage_fromTcb_eq hLk]; exact hStore
  have hInv' : st'.objects.invExt :=
    storeTcbIpcStateAndMessage_preserves_objects_invExt st st' target .ready (some msg) hObjInv hStore'
  have hChain : projectState ctx observer (wakeThread st' target executingCore).1
      = projectState ctx observer st := by
    rw [wakeThread_preserves_projection ctx observer st' target executingCore
          hTargetHigh hTargetObjHigh hInv',
        storeTcbIpcStateAndMessage_preserves_projection ctx observer st st' target _ _
          hTargetObjHigh hObjInv hStore']
  -- PR #827 #3 fold: case on the woken caller's reply link.
  cases hRO : tcb.replyObject with
  | none =>
    rw [endpointReplyOnCore_reply_eq replier target msg executingCore st st' tcb ep expected
          hSz1 hSz2 hLk hIpc hStore hRO]
    exact hChain
  | some rid =>
    obtain ⟨stC, hCons, hEq⟩ := endpointReplyOnCore_reply_eq_linked replier target msg
      executingCore st st' tcb ep expected rid hSz1 hSz2 hLk hIpc hStore hRO
    rw [hEq]
    show projectState ctx observer stC = projectState ctx observer st
    have hInvWake : (wakeThread st' target executingCore).1.objects.invExt :=
      wakeThread_preserves_objects_invExt st' target executingCore hInv'
    have hComplete' : objectIndexSetComplete st' :=
      storeTcbIpcStateAndMessage_preserves_objectIndexSetComplete st st' target .ready (some msg)
        hObjInv hObjSetInv hIdxComplete hStore'
    obtain ⟨tr, hGet, hReady⟩ :=
      storeTcbIpcStateAndMessage_getTcb?_ipcState st st' target .ready (some msg) hObjInv hStore'
    have hCompleteWake : objectIndexSetComplete (wakeThread st' target executingCore).1 :=
      wakeThread_preserves_objectIndexSetComplete_of_ready st' target executingCore tr hGet hReady
        hInv' hComplete'
    rw [consumeCallerReply_preserves_projection ctx observer _ stC target rid
          hTargetObjHigh hCompleteWake hInvWake hCons]
    exact hChain

-- ============================================================================
-- §2  SM6.C.8 — per-core / ∀-core non-interference (`lowEquivalent_smp`)
-- ============================================================================

/-- WS-SM SM6.C.8 (`endpointReply_perCore_NI`, ∀-core form): a high cross-core
reply is invisible to a low observer on *every* core — the post-state is
`lowEquivalent_smp` to the pre-state.  This is the SMP-faithful strengthening of
`endpointReplyOnCore_reply_path_NI` (which covers only the boot core): no covert
channel is opened on the *remote* core the caller is woken onto, nor on any
bystander core.  Proof: the same single-step chain as the boot-core theorem,
discharged at an arbitrary observer core `c` — the caller-store write is high
(object-store frame), and the caller wake's run-queue insert edits only a *high*
thread the observer filters out. -/
theorem endpointReplyOnCore_reply_path_NI_smp
    (ctx : LabelingContext) (observer : IfObserver)
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st st' : SystemState) (tcb : TCB) (ep : SeLe4n.ObjId) (expected : SeLe4n.ThreadId)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hLk : lookupTcb st target = some tcb)
    (hIpc : tcb.ipcState = .blockedOnReply ep (some expected))
    (hStore : storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) = .ok st')
    (hObjInv : st.objects.invExt)
    -- PR #827 review #3 (reply-fold): structural completeness for the folded
    -- consume's `.reply` re-store projection-invisibility (mirrors the SM6.A
    -- `endpointCallOnCore_call_path_NI_smp` hypotheses).
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hIdxComplete : objectIndexSetComplete st)
    (hTargetHigh : threadObservable ctx observer target = false)
    (hTargetObjHigh : objectObservable ctx observer target.toObjId = false) :
    lowEquivalent_smp ctx observer
      (endpointReplyOnCore replier target msg executingCore st).1 st := by
  intro c
  have hStore' : storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st' := by
    rw [← storeTcbIpcStateAndMessage_fromTcb_eq hLk]; exact hStore
  have hInv' : st'.objects.invExt :=
    storeTcbIpcStateAndMessage_preserves_objects_invExt st st' target .ready (some msg) hObjInv hStore'
  show projectStateOnCore ctx observer
      (endpointReplyOnCore replier target msg executingCore st).1 c
    = projectStateOnCore ctx observer st c
  have hChain : projectStateOnCore ctx observer (wakeThread st' target executingCore).1 c
      = projectStateOnCore ctx observer st c := by
    rw [wakeThread_preserves_projectionOnCore ctx observer st' target executingCore c
          hTargetHigh hTargetObjHigh hInv',
        storeTcbIpcStateAndMessage_preserves_projectionOnCore ctx observer st st' target _ _ c
          hTargetObjHigh hObjInv hStore']
  -- PR #827 #3 fold: case on the woken caller's reply link.
  cases hRO : tcb.replyObject with
  | none =>
    rw [endpointReplyOnCore_reply_eq replier target msg executingCore st st' tcb ep expected
          hSz1 hSz2 hLk hIpc hStore hRO]
    exact hChain
  | some rid =>
    obtain ⟨stC, hCons, hEq⟩ := endpointReplyOnCore_reply_eq_linked replier target msg
      executingCore st st' tcb ep expected rid hSz1 hSz2 hLk hIpc hStore hRO
    rw [hEq]
    show projectStateOnCore ctx observer stC c = projectStateOnCore ctx observer st c
    have hInvWake : (wakeThread st' target executingCore).1.objects.invExt :=
      wakeThread_preserves_objects_invExt st' target executingCore hInv'
    have hComplete' : objectIndexSetComplete st' :=
      storeTcbIpcStateAndMessage_preserves_objectIndexSetComplete st st' target .ready (some msg)
        hObjInv hObjSetInv hIdxComplete hStore'
    obtain ⟨tr, hGet, hReady⟩ :=
      storeTcbIpcStateAndMessage_getTcb?_ipcState st st' target .ready (some msg) hObjInv hStore'
    have hCompleteWake : objectIndexSetComplete (wakeThread st' target executingCore).1 :=
      wakeThread_preserves_objectIndexSetComplete_of_ready st' target executingCore tr hGet hReady
        hInv' hComplete'
    rw [consumeCallerReply_preserves_projectionOnCore ctx observer _ stC target rid c
          hTargetObjHigh hCompleteWake hInvWake hCons]
    exact hChain

end SeLe4n.Kernel
