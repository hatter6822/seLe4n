-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.MappingRecordStage.Ipc
import SeLe4n.Kernel.CNodeSlotsKept

/-!
# The reply-receive's reply step keeps every CNode

The steps of a reply-receive's reply that write no CNode at all keep every
capability a CNode holds (`CNodeSlotsKept`): each is a kind-preserving write,
and a kind-preserving write rewrites no CNode (`kindPreservingWriteAt`'s
`post.objectType ≠ .cnode`).  The reply leg (`endpointReplyOnCore`) and the
caller's answer (`replyRecvAnswerCaller`) are such steps.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The reply leg keeps every CNode**: it is the state itself, or the reply's
kind-preserving write followed by scheduler links alone. -/
theorem endpointReplyOnCore_cnodeSlotsKept {replier target : SeLe4n.ThreadId} {msg : IpcMessage}
    {executingCore : Concurrency.CoreId} {st : SystemState} (hInv : st.objects.invExt) :
    CNodeSlotsKept st (endpointReplyOnCore replier target msg executingCore st).1 := by
  rcases endpointReplyOnCore_post_agrees replier target msg executingCore st hInv
    with h | ⟨_, r1, hS, hA⟩
  · rw [h]; exact .refl _
  · exact CNodeSlotsKept.of_kindPreservingWriteAt fun oid =>
      ((endpointReply_kindPreservingWrite _ _ _ _ _ hInv hS) oid).trans
        (hA.objects.kindPreservingAt oid)

/-- The fault reply's decoded outcome keeps every CNode: a TCB write. -/
theorem faultReplyApplyOnCore_cnodeSlotsKept (st : SystemState) (faulted : SeLe4n.ThreadId)
    (outcome : Architecture.FaultReplyOutcome) (hInv : st.objects.invExt) :
    CNodeSlotsKept st (faultReplyApplyOnCore st faulted outcome) := by
  cases outcome with
  | restart frame =>
    exact CNodeSlotsKept.of_kindPreservingWrite (applyFaultRestart_kindPreservingWrite _ _ _ hInv)
  | abandon =>
    exact CNodeSlotsKept.of_kindPreservingWrite (faultAbandonOnCore_kindPreservingWrite _ _ _ hInv)

/-- **The caller's answer keeps every CNode**: its delivered message staged, or
the fault reply's outcome applied. -/
theorem replyRecvAnswerCaller_cnodeSlotsKept (answer : Option Architecture.FaultReplyOutcome)
    (st : SystemState) (prevCaller : SeLe4n.ThreadId) (capInfo : Nat)
    (hInv : st.objects.invExt) :
    CNodeSlotsKept st (replyRecvAnswerCaller answer st prevCaller capInfo) := by
  cases answer with
  | none =>
    exact CNodeSlotsKept.of_kindPreservingWrite
      (Architecture.stageDeliveredMessage_kindPreservingWrite st prevCaller capInfo hInv)
  | some o => exact faultReplyApplyOnCore_cnodeSlotsKept st prevCaller o hInv

end SeLe4n.Kernel
