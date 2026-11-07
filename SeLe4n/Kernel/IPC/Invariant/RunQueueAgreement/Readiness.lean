/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.Capability

/-!
# The readiness frame a step keeps, and the send and receive legs'

WS-ZA ZA6.18/ZA6.20.  `readyKeptStage S` says a step blocks no thread outside
`S`: a thread outside `S` ready in IPC, or with no TCB, stays so.  Every
run-queue stage is one for every `S`; a block is one for a set holding the
thread it blocks.  The definitions and the send and receive legs' frames live
here, ahead of the reply-receive's run-queue proof (`RunQueueAgreement/Ipc.lean`),
because that proof needs the answered caller still ready when it is answered:
a fault answer that abandons the caller leaves it `.Inactive`, which is coherent
only for a thread ready in IPC.  `BlockedNotResident.lean` and
`SyscallReadiness.lean` compose them over the entries and the dispatch arms.
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-! ### The IPC-state frame an entry keeps -/

/-- WS-ZA ZA6.18: **a step that blocks no thread outside `S`**: a thread outside
`S` ready in IPC, or with no TCB, stays so.  Every run-queue stage is one for
every `S` (its `StateMono`); a block is one for a set holding the thread it
blocks. -/
def readyKeptExcept (S : SeLe4n.ThreadId → Prop) (st st' : SystemState) : Prop :=
  ∀ t, ¬ S t → st.readyOrAbsent t → st'.readyOrAbsent t

theorem readyKeptExcept.trans {S : SeLe4n.ThreadId → Prop} {a b c : SystemState}
    (h1 : readyKeptExcept S a b) (h2 : readyKeptExcept S b c) : readyKeptExcept S a c :=
  fun t hS h => h2 t hS (h1 t hS h)

theorem readyKeptExcept.of_stateMono {S : SeLe4n.ThreadId → Prop} {st st' : SystemState}
    (h : SystemState.StateMono st st') : readyKeptExcept S st st' :=
  fun _ _ hr => h.readyOrAbsent hr

/-- **A step that keeps readiness off the threads `S`**, given the link
invariants at its start: the readiness frame a blocking arm composes. -/
def readyKeptStage (S : SeLe4n.ThreadId → Prop) (st st' : SystemState) : Prop :=
  st.objects.invExt → st.runQueueRefined → readyKeptExcept S st st'

namespace readyKeptStage

variable {S : SeLe4n.ThreadId → Prop}

theorem refl (st : SystemState) : readyKeptStage S st st := fun _ _ _ _ h => h

theorem of_stage {st st' : SystemState} (h : SystemState.RunQueueStage st st') :
    readyKeptStage S st st' := fun hI hR => .of_stateMono (h.2.2 hI hR)

theorem of_dispatch {c : CoreId} {st st' : SystemState}
    (h : SystemState.RunQueueDispatchStage c st st') : readyKeptStage S st st' :=
  fun hI hR => .of_stateMono (h.2.2 hI hR)

/-- Two readiness frames compose over the link invariants the first step keeps. -/
theorem trans {a b c : SystemState} (L : SystemState.RunQueueLinkStage a b)
    (h1 : readyKeptStage S a b) (h2 : readyKeptStage S b c) : readyKeptStage S a c :=
  fun hI hR => let ⟨hI', hR'⟩ := L.links hI hR; (h1 hI hR).trans (h2 hI' hR')

/-- ...over a frame stage's link half. -/
theorem transFrame {P : SeLe4n.SchedContextId → Prop} {a b c : SystemState}
    (L : SystemState.RunQueueFrameStage P a b)
    (h1 : readyKeptStage S a b) (h2 : readyKeptStage S b c) : readyKeptStage S a c :=
  fun hI hR => let ⟨hI', hR'⟩ := L.1.links hI hR; (h1 hI hR).trans (h2 hI' hR')

/-- A frame stage keeps every thread's readiness: its activity half. -/
theorem of_frame {P : SeLe4n.SchedContextId → Prop} {st st' : SystemState}
    (h : SystemState.RunQueueFrameStage P st st') : readyKeptStage S st st' :=
  fun hI hR => .of_stateMono (h.2.2 hI hR)

theorem mono {S' : SeLe4n.ThreadId → Prop} {st st' : SystemState} (hS : ∀ t, S t → S' t)
    (h : readyKeptStage S st st') : readyKeptStage S' st st' :=
  fun hI hR t hn => h hI hR t fun hs => hn (hS t hs)

end readyKeptStage

/-- **A TCB update that keeps a ready thread ready keeps every thread's
readiness.** -/
theorem readyKeptExcept_updateTcb {S : SeLe4n.ThreadId → Prop} (st : SystemState)
    (tid : SeLe4n.ThreadId) (f : TCB → TCB) (hInv : st.objects.invExt)
    (hf : ∀ x, x.ipcState = .ready → (f x).ipcState = .ready) :
    readyKeptExcept S st (st.updateTcb tid f) := fun t _ h x hx => by
  by_cases e : t = tid
  · subst e
    rw [SystemState.updateTcb_getTcb?_self st t f hInv] at hx
    cases hT : st.getTcb? t with
    | none => rw [hT] at hx; cases hx
    | some y =>
      rw [hT] at hx; cases hx
      exact hf y (h y hT)
  · rw [SystemState.updateTcb_getTcb?_ne st tid f hInv t
      (fun h' => e (ThreadId.toObjId_injective _ _ h').symm)] at hx
    exact h x hx

/-- **The blocking arm's IPC-state store keeps every other thread's readiness**:
it writes the one TCB. -/
theorem storeTcbIpcStateAndMessage_readyKeptStage {st st' : SystemState}
    {tid : SeLe4n.ThreadId} {s : ThreadIpcState} {m : Option IpcMessage}
    (h : storeTcbIpcStateAndMessage st tid s m = .ok st') :
    readyKeptStage (· = tid) st st' := fun hI _ t hn hr x hx => by
  obtain ⟨_, _, hS⟩ := modifyTcb_ok_decompose h
  rw [storeObject_getTcb?_ne st st' _ _ t
    (fun h' => hn (ThreadId.toObjId_injective _ _ h')) hI hS] at hx
  exact hr x hx

/-- **The block of core `c`'s current thread `t`** blocks `t` alone: the stages
around its IPC-state store keep every thread's readiness, and so does the
deschedule closing the window. -/
theorem blockThenDeschedule_readyKeptStage {st st1 st2 st3 : SystemState} {t : SeLe4n.ThreadId}
    {s : ThreadIpcState} {m : Option IpcMessage} {c : CoreId}
    (pre : SystemState.RunQueueStage st st1) (hS : storeTcbIpcStateAndMessage st1 t s m = .ok st2)
    (post : SystemState.RunQueueStage st2 st3) (hC1 : st1.scheduler.currentOnCore c = some t)
    (hC3 : st3.scheduler.currentOnCore c = some t) (hNI : isIdleThreadId t = false) :
    readyKeptStage (· = t) st (removeRunnableOnCore st3 t c) :=
  (readyKeptStage.of_stage pre).trans pre.1
    ((storeTcbIpcStateAndMessage_readyKeptStage hS).trans
      (storeTcbIpcStateAndMessage_runQueueBlockStage hS hC1 hNI).1
      ((readyKeptStage.of_stage post).trans post.1
        (.of_dispatch (SystemState.RunQueueDispatchStage.descheduleCurrent st3 c t hC3))))

theorem blockThenDescheduleRecord_readyKeptStage {st st1 st2 st3 : SystemState}
    {t : SeLe4n.ThreadId} {s : ThreadIpcState} {m : Option IpcMessage} {c : CoreId}
    (pre : SystemState.RunQueueStage st st1) (hS : storeTcbIpcStateAndMessage st1 t s m = .ok st2)
    (post : SystemState.RunQueueStage st2 st3) (hC1 : st1.scheduler.currentOnCore c = some t)
    (hC3 : st3.scheduler.currentOnCore c = some t) (hNI : isIdleThreadId t = false)
    (badge : Option SeLe4n.Badge) (grant : Bool) :
    readyKeptStage (· = t) st (recordSendCap (removeRunnableOnCore st3 t c) t badge grant) :=
  (blockThenDeschedule_readyKeptStage pre hS post hC1 hC3 hNI).trans
    (pre.blockThenDeschedule hS post hC1 hC3 hNI).1
    (.of_stage (recordSendCap_runQueueStage _ t badge grant))

/-! ### Send and receive -/

theorem endpointSendDualOnCore_readyKeptStage (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (payload : SendPayload) (c : CoreId)
    (st : SystemState) (hHeads : endpointHeadsWakeable st)
    (hCur : st.scheduler.currentOnCore c = some sender) (hNI : isIdleThreadId sender = false) :
    readyKeptStage (· = sender) st (endpointSendDualOnCore endpointId sender payload c st).1 := by
  unfold endpointSendDualOnCore
  split
  · split
    · split
      · exact .refl _
      · split
        · exact .refl _
        · rename_i receiver _ st1 hPop
          split
          · exact .refl _
          · rename_i st2 hS2
            exact .of_stage (((endpointQueuePopHead_runQueueStage hPop).trans
              (storeTcbReceiveComplete_runQueueStage hS2)).then_wake c
              ((hHeads.popped hPop).of_scheduler_eq
                (storeTcbReceiveComplete_scheduler_eq _ _ _ _ hS2))
              (hHeads.popped_blocked hPop))
    · split
      · exact .refl _
      · rename_i st1 hE
        split
        · exact .refl _
        · rename_i st2 hS2
          have hC1 := currentOnCore_of_scheduler_eq
            (endpointQueueEnqueue_scheduler_eq _ _ _ _ _ hE) hCur
          exact blockThenDescheduleRecord_readyKeptStage (endpointQueueEnqueue_runQueueStage hE)
            hS2 (SystemState.RunQueueStage.refl _) hC1
            (currentOnCore_of_scheduler_eq
              (storeTcbIpcStateAndMessage_scheduler_eq _ _ _ _ _ hS2) hC1) hNI _ _
  · split <;> exact .refl _

theorem endpointSendDualWithCapsOnCore_readyKeptStage (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (payload : SendPayload)
    (base : SeLe4n.Slot) (c : CoreId) (st : SystemState)
    (hHeads : endpointHeadsWakeable st) (hCur : st.scheduler.currentOnCore c = some sender)
    (hNI : isIdleThreadId sender = false) :
    readyKeptStage (· = sender) st
      (endpointSendDualWithCapsOnCore endpointId sender payload base c st).1 := by
  have s0 := (endpointSendDualOnCore_runQueueEntryStage endpointId sender payload c st hHeads
    hCur hNI).1
  have r0 := endpointSendDualOnCore_readyKeptStage endpointId sender payload c st hHeads hCur hNI
  unfold endpointSendDualWithCapsOnCore
  generalize endpointSendDualOnCore endpointId sender payload c st = r at s0 r0 ⊢
  obtain ⟨st1, r⟩ := r
  cases r with
  | error e => exact r0
  | ok sgi =>
    dsimp only
    repeat' split
    all_goals first
      | exact r0
      | (rename_i hU; exact r0.trans s0 (.of_stage (receiveTransferCaps_runQueueStage hU)))

theorem endpointReceiveDualOnCore_readyKeptStage (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId) (c : CoreId)
    (st : SystemState) (hHeads : endpointHeadsWakeable st)
    (hCur : st.scheduler.currentOnCore c = some receiver)
    (hNI : isIdleThreadId receiver = false) (hAct : st.activeAt receiver) :
    readyKeptStage (· = receiver) st
      (endpointReceiveDualOnCore endpointId receiver replyId c st).1 := by
  unfold endpointReceiveDualOnCore
  split
  · split
    · split
      · exact .refl _
      · rename_i sender senderTcb st1 hPop
        dsimp only
        split
        · rename_i hCall
          have hB : senderTcb.ipcState ≠ .ready := by rw [hCall]; exact fun h => by cases h
          simp only [↓reduceIte]
          split
          · exact .refl _
          · rename_i st2 hS2
            split
            · exact .refl _
            · split
              · exact .refl _
              · rename_i st3 hL
                split
                · rename_i st4 hS4
                  exact .of_stage ((endpointQueuePopHead_then_blockedStore_runQueueStage hPop hS2
                    hB).trans ((linkCallerReply_runQueueStage hL).trans
                      ((storeTcbIpcStateAndMessage_runQueueStage hS4 rfl).trans
                        (SystemState.linkReplyWaiter_runQueueStage _ _ _))))
                · exact .refl _
        · simp only [Bool.false_eq_true, ↓reduceIte]
          split
          · exact .refl _
          · rename_i st2 hS2
            split
            · rename_i st4 hS4
              exact .of_stage ((((endpointQueuePopHead_runQueueStage hPop).trans
                (storeTcbIpcStateAndMessage_runQueueStage hS2 rfl)).then_wake c
                ((hHeads.popped hPop).of_scheduler_eq
                  (storeTcbIpcStateAndMessage_scheduler_eq _ _ _ _ _ hS2))
                (hHeads.popped_blocked hPop)).trans
                (storeTcbIpcStateAndMessage_runQueueStage hS4 rfl))
            · exact .refl _
    · split
      · exact .refl _
      · rename_i stC hC
        split
        · exact .refl _
        · rename_i st1 hE
          split
          · exact .refl _
          · rename_i st2 hS2
            have pre := (cleanupPreReceiveDonationMigrated_runQueueStage hAct hC).trans
              (endpointQueueEnqueue_runQueueStage hE)
            have hC1 : st1.scheduler.currentOnCore c = some receiver :=
              currentOnCore_of_scheduler_eq (endpointQueueEnqueue_scheduler_eq _ _ _ _ _ hE)
                ((cleanupPreReceiveDonationMigrated_currentOnCore _ _ _ hC c).trans hCur)
            have hC2 : st2.scheduler.currentOnCore c = some receiver :=
              currentOnCore_of_scheduler_eq
                (storeTcbIpcStateAndMessage_scheduler_eq _ _ _ _ _ hS2) hC1
            split
            · exact blockThenDeschedule_readyKeptStage pre hS2 (SystemState.RunQueueStage.refl _)
                hC1 hC2 hNI
            · rename_i rTcb hT
              split
              · split
                · exact .refl _
                · rename_i st3 hS3
                  exact blockThenDeschedule_readyKeptStage pre hS2
                    (SystemState.RunQueueStage.of_invExt fun hI =>
                      (recordReplyStasher_runQueueStage _ _ _).trans
                      (storeObject_tcbOver_runQueueStage (old := rTcb)
                        (by rw [SystemState.recordReplyStasher_getTcb? _ _ _ hI]; exact hT) hS3
                        (fun _ => rfl))) hC1
                    (currentOnCore_of_scheduler_eq ((storeObject_scheduler_eq _ _ _ _ hS3).trans
                      (SystemState.recordReplyStasher_scheduler _ _ _)) hC2) hNI
              · exact .refl _
  · split <;> exact .refl _

theorem endpointReceiveDualWithCapsOnCore_readyKeptStage (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId) (root : SeLe4n.ObjId)
    (base : SeLe4n.Slot) (c : CoreId) (st : SystemState)
    (hHeads : endpointHeadsWakeable st) (hCur : st.scheduler.currentOnCore c = some receiver)
    (hNI : isIdleThreadId receiver = false) (hAct : st.activeAt receiver) :
    readyKeptStage (· = receiver) st
      (endpointReceiveDualWithCapsOnCore endpointId receiver replyId root base c st).1 := by
  have s0 := (endpointReceiveDualOnCore_runQueueEntryStage endpointId receiver replyId c st
    hHeads hCur hNI hAct).1
  have r0 := endpointReceiveDualOnCore_readyKeptStage endpointId receiver replyId c st
    hHeads hCur hNI hAct
  unfold endpointReceiveDualWithCapsOnCore
  generalize endpointReceiveDualOnCore endpointId receiver replyId c st = r at s0 r0 ⊢
  obtain ⟨st1, r⟩ := r
  cases r with
  | error e => exact r0
  | ok res =>
    dsimp only
    repeat' split
    all_goals first
      | exact r0
      | (rename_i hU; exact r0.trans s0 (.of_stage (receiveTransferCaps_runQueueStage hU)))

end SeLe4n.Kernel
