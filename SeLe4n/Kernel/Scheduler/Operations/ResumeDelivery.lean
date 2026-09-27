-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.PerCoreSwitchToThread
import SeLe4n.Kernel.Architecture.ContextRestore
import SeLe4n.Kernel.Lifecycle.Suspend
import SeLe4n.Kernel.Lifecycle.Invariant.SuspendPreservation
import SeLe4n.Kernel.IPC.Operations.Timeout

/-!
# WS-BP BP7.5 — an unblocked thread resumes reading the error it was staged

WS-RR RR7.14 stages an error frame into the saved context of a thread taken out
of a blocking IPC: `.ipcTimeout` when its budget expired
(`abortPendingIpcOnEndpoint`, which `timeoutThread` runs), `.ipcCancelled` when
the operation was destroyed under it (`restoreToReadyCancelled`, every blocked
arm of `cancelIpcBlocking`).  What was not stated is that the frame is what the
thread *reads*: a staged frame is only an answer if the context restore hands
it back.

The restore resumes a core from the committed state
(`Architecture.restoreTargetOnCore`), and a thread becomes a core's current
thread only by a switch.  So delivery is one relation:
**a switch to a thread resumes it with the return frame its TCB holds**
(`switchToThreadOnCore_delivers_readReturnFrame`).  The switch writes exactly
one TCB — the *outgoing* thread's context save — so the incoming thread's
context crosses it unchanged.  The two unblock paths each state what that frame
is (`restoreToReadyCancelled_readReturnFrame`,
`abortPendingIpcOnEndpoint_readReturnFrame`), and the two corollaries compose
them.

What is deliberately not claimed: that nothing between the unblock and the
switch rewrites the frame.  An unblocked thread is `.ready` and on no IPC queue,
so no IPC delivery targets it, and the trap-frame save writes only a core's
*current* thread — but that is a property of every transition in the tree, not
of this relation, and the executed witness
(`tests/SmpCancellationSuite.lean` §3.19b) drives the live cancellation and the
live switch end to end.
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- **The return frame a restore target delivers** — `x0`–`x5` of the context it
resumes, read the way `readReturnFrame` reads a TCB's.  An idle core and an
empty core deliver none. -/
def RestoreTarget.deliveredFrame? : RestoreTarget → Option SyscallReturnFrame
  | .user ctx _ _ =>
    some { x0 := (ctx.gpr ⟨0⟩).val.toUInt64
           x1 := (ctx.gpr ⟨1⟩).val.toUInt64
           x2 := (ctx.gpr ⟨2⟩).val.toUInt64
           x3 := (ctx.gpr ⟨3⟩).val.toUInt64
           x4 := (ctx.gpr ⟨4⟩).val.toUInt64
           x5 := (ctx.gpr ⟨5⟩).val.toUInt64 }
  | .idle => Option.none
  | .none => Option.none

/-- A core whose current thread is a user thread delivers that thread's
`readReturnFrame`. -/
theorem restoreTargetOnCore_deliveredFrame (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hCur : st.scheduler.currentOnCore c = some tid)
    (hIdle : SeLe4n.Kernel.isIdleThreadId tid = false) (hTcb : st.getTcb? tid = some tcb) :
    (restoreTargetOnCore st c).deliveredFrame? = some (readReturnFrame st tid) := by
  rw [restoreTargetOnCore_user st c tid tcb hCur hIdle hTcb]
  simp [RestoreTarget.deliveredFrame?, readReturnFrame, hTcb]

end SeLe4n.Kernel.Architecture

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)
open SeLe4n.Kernel.Architecture
open SeLe4n.Kernel.Lifecycle.Suspend

/-- **WS-BP BP7.5: a switch resumes the incoming thread with the frame its TCB
holds.**  The switch's only object write is the outgoing thread's context save
(`switchToThreadOnCore_getTcb?_ne_current`), so the incoming thread's context —
whatever an earlier transition staged into it — is what the committed state's
restore target carries. -/
theorem switchToThreadOnCore_delivers_readReturnFrame (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (st' : SystemState)
    (hInv : st.objects.invExt) (hTcb : st.getTcb? tid = some tcb)
    (hNe : st.scheduler.currentOnCore c ≠ some tid)
    (hIdle : isIdleThreadId tid = false)
    (h : switchToThreadOnCore st c tid = .ok st') :
    (restoreTargetOnCore st' c).deliveredFrame? = some (readReturnFrame st tid) := by
  have hSame : st'.getTcb? tid = st.getTcb? tid :=
    switchToThreadOnCore_getTcb?_ne_current st c tid tid st' hInv hNe h
  have hCur := switchToThreadOnCore_sets_current st c tid st' h
  rw [restoreTargetOnCore_deliveredFrame st' c tid tcb hCur hIdle (hSame.trans hTcb)]
  simp [readReturnFrame, hSame]

/-- **The cancellation half**: a thread `cancelIpcBlocking` restored, once
switched to, resumes reading `.ipcCancelled`. -/
theorem restoreToReadyCancelled_then_switch_delivers_cancelledIpcFrame
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB) (st' : SystemState)
    (hInv : st.objects.invExt) (hTcb : st.getTcb? tid = some tcb)
    (hNe : (restoreToReadyCancelled st tid).scheduler.currentOnCore c ≠ some tid)
    (hIdle : isIdleThreadId tid = false)
    (h : switchToThreadOnCore (restoreToReadyCancelled st tid) c tid = .ok st') :
    (restoreTargetOnCore st' c).deliveredFrame? = some cancelledIpcFrame := by
  have hInv' : (restoreToReadyCancelled st tid).objects.invExt :=
    restoreToReadyCancelled_invExt st tid hInv
  obtain ⟨tcb', hTcb'⟩ : ∃ t, (restoreToReadyCancelled st tid).getTcb? tid = some t := by
    rw [restoreToReadyCancelled_tcb st tid hInv]
    unfold restoreToReady restoreToReadyStaging
    rw [SystemState.updateTcb_getTcb?_self _ _ _ hInv, hTcb]
    exact ⟨_, rfl⟩
  rw [switchToThreadOnCore_delivers_readReturnFrame _ c tid tcb' st' hInv' hTcb' hNe hIdle h,
    restoreToReadyCancelled_readReturnFrame st tid tcb hTcb hInv]

/-- A thread whose TCB holds a frame-staged record reads back exactly that
frame — the round trip `readReturnFrame_writeReturnFrame` states for the
write, stated here for any record carrying it. -/
theorem readReturnFrame_of_withReturnFrame (st : SystemState) (tid : SeLe4n.ThreadId)
    (t : TCB) (f : SyscallReturnFrame) (h : st.getTcb? tid = some (t.withReturnFrame f)) :
    readReturnFrame st tid = f := by
  unfold readReturnFrame
  rw [h]
  simp only
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := (t.registerContext).stageReturnFrame_reads_back f
  simp only [SeLe4n.Model.TCB.withReturnFrame_registerContext, h0, h1, h2, h3, h4, h5]
  cases f
  simp [UInt64.ofNat_toNat]

/-- **The timeout half's frame**: the thread the timeout's object prefix
unblocks reads `.ipcTimeout` out of its own context. -/
theorem abortPendingIpcOnEndpoint_readReturnFrame
    (epId : SeLe4n.ObjId) (isRecvQ : Bool) (tid : SeLe4n.ThreadId) (st st' : SystemState)
    (hInv : st.objects.invExt)
    (hStep : abortPendingIpcOnEndpoint epId isRecvQ tid st = .ok st') :
    readReturnFrame st' tid = timeoutFrame := by
  unfold abortPendingIpcOnEndpoint at hStep
  split at hStep
  · simp at hStep
  · rename_i st1 hEQR
    have hInv1 := endpointQueueRemove_preserves_objects_invExt _ _ _ _ _ hInv hEQR
    split at hStep
    · simp at hStep
    · rename_i tcb _
      simp only [] at hStep
      split at hStep
      · simp at hStep
      · rename_i st2 hStore
        simp only [Except.ok.injEq] at hStep
        subst hStep
        exact readReturnFrame_of_withReturnFrame _ tid _ _
          (storeObject_getTcb?_self _ _ tid _ hInv1 hStore)

/-- **The timeout half**: a thread the timeout's object prefix unblocked, once
switched to, resumes reading `.ipcTimeout`. -/
theorem abortPendingIpcOnEndpoint_then_switch_delivers_timeoutFrame
    (epId : SeLe4n.ObjId) (isRecvQ : Bool) (tid : SeLe4n.ThreadId) (c : CoreId)
    (st st' st'' : SystemState) (tcb : TCB)
    (hInv : st.objects.invExt)
    (hStep : abortPendingIpcOnEndpoint epId isRecvQ tid st = .ok st')
    (hTcb : st'.getTcb? tid = some tcb)
    (hNe : st'.scheduler.currentOnCore c ≠ some tid)
    (hIdle : isIdleThreadId tid = false)
    (h : switchToThreadOnCore st' c tid = .ok st'') :
    (restoreTargetOnCore st'' c).deliveredFrame? = some timeoutFrame := by
  rw [switchToThreadOnCore_delivers_readReturnFrame st' c tid tcb st''
      (abortPendingIpcOnEndpoint_preserves_objects_invExt _ _ _ _ _ hInv hStep) hTcb hNe hIdle h,
    abortPendingIpcOnEndpoint_readReturnFrame epId isRecvQ tid st st' hInv hStep]

end SeLe4n.Kernel
