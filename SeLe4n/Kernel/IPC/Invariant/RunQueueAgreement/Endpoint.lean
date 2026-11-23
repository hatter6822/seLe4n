/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement
import SeLe4n.Kernel.IPC.CrossCore.EndpointSend
import SeLe4n.Kernel.IPC.CrossCore.EndpointReply

/-!
# Send and receive keep the run-queue link agreement

WS-ZA ZA4.5 part 2.  The send and receive legs, with and without capability
transfer, are kernel entries (`SystemState.RunQueueEntryStage`): a rendezvous
wakes the blocked partner it pops through the stages
`IPC.Invariant.RunQueueAgreement` proves, and a block opens core `c`'s
scheduling point with the IPC-state store over `c`'s current thread and closes
it with that thread's deschedule (`RunQueueStage.blockThenDeschedule`).

The proofs are the `run_queue_stage` tactic, declared here: it peels a goal's
steps off one at a time, last step first, with the stage of whichever step it
recognises.  Each stage proved for a composite step is registered right after
it as a `run_queue_stage_step` rule, so a module downstream proves the next
composite by unfolding it, splitting its matches (`run_queue_stage_split`) and
calling the tactic.
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Model.SystemState (RunQueueStage)

/-- A stage to a pair's state is a stage to whatever state the pair is matched
against. -/
theorem _root_.SeLe4n.Model.SystemState.RunQueueStage.of_fst_eq {α : Type}
    {st st' : SystemState} {p : SystemState × α} {r : α}
    (s : RunQueueStage st p.1) (h : p = (st', r)) : RunQueueStage st st' := by
  subst h; exact s

/-- One step of `run_queue_stage`: peel the goal's last step off with that
step's stage.  Each module that proves a stage adds its rule. -/
syntax "run_queue_stage_step" : tactic

/-- Close a stage goal `RunQueueStage st X` by peeling `X`'s steps off one at a
time (`run_queue_stage_step`) until it reaches `st`. -/
macro "run_queue_stage" : tactic => `(tactic| repeat (first
  | with_reducible exact RunQueueStage.refl _
  | run_queue_stage_step))

/-- One step of `run_queue_current_nowhere`: walk back over a step that keeps
the scheduler, or close the premise at the state it is stated on. -/
syntax "run_queue_current_nowhere_step" : tactic

/-- Close the premise a wake leaves, that the woken thread is current nowhere:
walk back over the steps before it, which keep the scheduler, to the state its
caller's premise speaks of. -/
macro "run_queue_current_nowhere" : tactic => `(tactic| repeat (first
  | (exact (by assumption : SystemState.currentNowhere _ _))
  | run_queue_current_nowhere_step))

macro_rules | `(tactic| run_queue_current_nowhere_step) => `(tactic|
  refine SystemState.currentNowhere.of_scheduler_eq
    (storeTcbIpcStateAndMessage_scheduler_eq _ _ _ _ _ (by with_reducible assumption)) ?_)
macro_rules | `(tactic| run_queue_current_nowhere_step) => `(tactic|
  refine SystemState.currentNowhere.of_scheduler_eq
    (storeTcbReceiveComplete_scheduler_eq _ _ _ _ (by with_reducible assumption)) ?_)
macro_rules | `(tactic| run_queue_current_nowhere_step) => `(tactic|
  refine SystemState.currentNowhere.of_scheduler_eq
    (storeObject_scheduler_eq _ _ _ _ (by with_reducible assumption)) ?_)
macro_rules | `(tactic| run_queue_current_nowhere_step) => `(tactic|
  exact endpointHeadsWakeable.popped (by assumption) (by with_reducible assumption))

/-- Close the premise a wake leaves, that the woken thread was blocked when the
steps before it began: it is the head a pop returned. -/
macro "run_queue_blocked" : tactic => `(tactic|
  exact endpointHeadsWakeable.popped_blocked (by assumption) (by with_reducible assumption))

/-- Split every `match` and `if` in a stage goal or its hypotheses' way. -/
macro "run_queue_stage_split" : tactic => `(tactic| repeat' (first | split | dsimp only))

/-- Close `objRunLinkOn (some new) c = objRunLinkOn st.objects[k]? c` for a
store of a non-TCB object over the object a lookup in the context found. -/
syntax "run_queue_slot_same" : tactic
macro_rules | `(tactic| run_queue_slot_same) => `(tactic| with_reducible rfl)
macro_rules | `(tactic| run_queue_slot_same) => `(tactic|
  (rw [(SystemState.getCNode?_eq_some_iff _ _ _).mp (by with_reducible assumption)]; rfl))
macro_rules | `(tactic| run_queue_slot_same) => `(tactic|
  (rw [(SystemState.getNotification?_eq_some_iff _ _ _).mp (by with_reducible assumption)]; rfl))
macro_rules | `(tactic| run_queue_slot_same) => `(tactic|
  (rw [(SystemState.getEndpoint?_eq_some_iff _ _ _).mp (by with_reducible assumption)]; rfl))
macro_rules | `(tactic| run_queue_slot_same) => `(tactic|
  (rw [(SystemState.getUntyped?_eq_some_iff _ _ _).mp (by with_reducible assumption)]; rfl))
macro_rules | `(tactic| run_queue_slot_same) => `(tactic|
  (rw [(SystemState.getSchedContext?_eq_some_iff _ _ _).mp (by with_reducible assumption)]; rfl))
macro_rules | `(tactic| run_queue_slot_same) => `(tactic|
  (rw [(SystemState.getReply?_eq_some_iff _ _ _).mp (by with_reducible assumption)]; rfl))

macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_
    (RunQueueStage.storeObject (by with_reducible assumption) (fun _ => by run_queue_slot_same)
      (SystemState.objStateMono_nonTcb (by run_queue_slot_same) rfl)))
macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (removeRunnableOnCore_runQueueStage _ _ _))
macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.then_wake ?_ _ ?_ ?_)
macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.of_fst_eq (RunQueueStage.then_wake ?_ _ ?_ ?_)
    (by with_reducible assumption))
macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (endpointQueuePopHead_runQueueStage (by with_reducible assumption)))
macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (endpointQueueEnqueue_runQueueStage (by with_reducible assumption)))
macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (storeTcbReceiveComplete_runQueueStage (by with_reducible assumption)))
macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (storeTcbIpcStateAndMessage_runQueueStage (by with_reducible assumption) rfl))
macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (ipcUnwrapCaps_runQueueStage (by with_reducible assumption)))

/-- **The send** of core `c`'s current thread: the rendezvous wakes the
receive-queue head it pops (`hHeads`); the block enqueues the sender, blocks
it and deschedules it. -/
theorem endpointSendDualOnCore_runQueueEntryStage (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (payload : SendPayload) (c : Concurrency.CoreId)
    (st : SystemState) (hHeads : endpointHeadsWakeable st)
    (hCur : st.scheduler.currentOnCore c = some sender) (hNI : isIdleThreadId sender = false) :
    SystemState.RunQueueEntryStage st (endpointSendDualOnCore endpointId sender payload c st).1 := by
  unfold endpointSendDualOnCore
  split
  · split
    · split
      · exact (RunQueueStage.refl _).entry
      · split
        · exact (RunQueueStage.refl _).entry
        · rename_i receiver _ st1 hPop
          split
          · exact (RunQueueStage.refl _).entry
          · rename_i st2 hS2
            exact (((endpointQueuePopHead_runQueueStage hPop).trans
              (storeTcbReceiveComplete_runQueueStage hS2)).then_wake c
              ((hHeads.popped hPop).of_scheduler_eq
                (storeTcbReceiveComplete_scheduler_eq _ _ _ _ hS2))
              (hHeads.popped_blocked hPop)).entry
    · split
      · exact (RunQueueStage.refl _).entry
      · rename_i st1 hE
        split
        · exact (RunQueueStage.refl _).entry
        · rename_i st2 hS2
          have hC1 := currentOnCore_of_scheduler_eq
            (endpointQueueEnqueue_scheduler_eq _ _ _ _ _ hE) hCur
          exact (endpointQueueEnqueue_runQueueStage hE).blockThenDescheduleRecord hS2
            (RunQueueStage.refl _) hC1
            (currentOnCore_of_scheduler_eq
              (storeTcbIpcStateAndMessage_scheduler_eq _ _ _ _ _ hS2) hC1) hNI _ _ _
  · split <;> exact (RunQueueStage.refl _).entry

theorem endpointSendDualWithCapsOnCore_runQueueEntryStage (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (payload : SendPayload)
    (c : Concurrency.CoreId) (st : SystemState)
    (hHeads : endpointHeadsWakeable st) (hCur : st.scheduler.currentOnCore c = some sender)
    (hNI : isIdleThreadId sender = false) :
    SystemState.RunQueueEntryStage st
      (endpointSendDualWithCapsOnCore endpointId sender payload c st).1 := by
  have s0 := endpointSendDualOnCore_runQueueEntryStage endpointId sender payload c st hHeads hCur hNI
  unfold endpointSendDualWithCapsOnCore
  generalize endpointSendDualOnCore endpointId sender payload c st = r at s0 ⊢
  obtain ⟨st1, r⟩ := r
  cases r with
  | error e => exact s0
  | ok sgi =>
    dsimp only
    repeat' split
    all_goals first
      | exact s0
      | (rename_i hU; exact s0.trans (receiveTransferCaps_runQueueStage hU).entry)

theorem cleanupPreReceiveDonationChecked_runQueueStage {st st' : SystemState}
    {receiver : SeLe4n.ThreadId} (hA : st.activeAt receiver)
    (h : cleanupPreReceiveDonationChecked st receiver = .ok st') :
    RunQueueStage st st' := by
  unfold cleanupPreReceiveDonationChecked at h
  split at h
  · cases h; exact RunQueueStage.refl _
  · split at h
    · exact popHeldReplyHead_lift h (fun _ _ hR => returnDonatedSchedContextResolved_runQueueStage hA hR)
        (fun _ _ hK => keepDonatedSchedContextResolved_runQueueStage hK)
    · cases h; exact RunQueueStage.refl _

theorem preReceiveReturnMigration_runQueueStage (st stClean : SystemState)
    (receiver : SeLe4n.ThreadId) :
    RunQueueStage stClean (preReceiveReturnMigration st stClean receiver) := by
  unfold preReceiveReturnMigration
  split
  · exact migrateSchedContextReplenishment_runQueueStage _ _ _ _
  · exact RunQueueStage.refl _

theorem cleanupPreReceiveDonationMigrated_runQueueStage {st st' : SystemState}
    {receiver : SeLe4n.ThreadId} (hA : st.activeAt receiver)
    (h : cleanupPreReceiveDonationMigrated st receiver = .ok st') :
    RunQueueStage st st' := by
  obtain ⟨stClean, hC, rfl⟩ := cleanupPreReceiveDonationMigrated_ok_decompose h
  exact (cleanupPreReceiveDonationChecked_runQueueStage hA hC).trans
    (preReceiveReturnMigration_runQueueStage _ _ _)

macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (cleanupPreReceiveDonationMigrated_runQueueStage (by assumption) (by with_reducible assumption)))
macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (linkCallerReply_runQueueStage (by with_reducible assumption)))
macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_
    (storeObject_tcbOver_runQueueStage (by with_reducible assumption) (by with_reducible assumption) (by intro; rfl)))

/-- **A head pop, then the popped caller completed `Inactive`** — the receive
of a `Call` that links no reply (seL4 `receiveIPC` with no grant right or no
reply object): the caller was blocked, so it is current nowhere, on no run queue
and no idle thread; its `.ready` store and its `Inactive` mark land on a thread
placed nowhere and leave it coherent (`.ready`).  No stage, since the caller was
active before and is not after. -/
theorem endpointQueuePopHead_then_inactiveStore_runQueueEntryStage {st st1 st2 : SystemState}
    {endpointId : SeLe4n.ObjId} {isReceiveQ : Bool} {r : SeLe4n.ThreadId} {rTcb : TCB}
    (hPop : endpointQueuePopHead endpointId isReceiveQ st = .ok (r, rTcb, st1))
    (hS : storeTcbIpcStateAndMessage st1 r .ready none = .ok st2) (hB : rTcb.ipcState ≠ .ready) :
    SystemState.RunQueueEntryStage st
      (st2.updateTcb r fun t => { t with threadState := .Inactive }) := by
  have P := endpointQueuePopHead_runQueueStage hPop
  have S := storeTcbIpcStateAndMessage_runQueueStage hS rfl
  have W := SystemState.RunQueueLinkStage.updateTcb st2 r
    (f := fun t => { t with threadState := .Inactive }) (fun _ _ => rfl)
  refine SystemState.RunQueueEntryStage.of_inv (P.1.trans (S.1.trans W)) fun h0 _ _ => ?_
  have hE : ∃ ep, st.objects[endpointId]? = some (.endpoint ep) := by
    unfold endpointQueuePopHead SystemState.getObject? at hPop
    split at hPop
    · exact ⟨_, ‹_›⟩
    all_goals cases hPop
  obtain ⟨ep, hObj⟩ := hE
  have hPre := endpointQueuePopHead_returns_pre_tcb _ _ _ ep r rTcb st1 hObj hPop
  refine P.entry.trans ⟨S.1.trans W, fun h1 r1 _ d1 => ?_⟩
  obtain ⟨h2, r2⟩ := S.1 h1 r1
  have d2 := S.2.1 none h1 r1 r2 d1
  have hSch := storeTcbIpcStateAndMessage_scheduler_eq _ _ _ _ _ hS
  have hNR : ¬ st1.runnable r := fun ⟨x, hx, hr⟩ => by
    obtain ⟨y, hy, he⟩ := endpointQueuePopHead_tcb_ipcState_backward _ _ _ _ r r x h0 hPop
      ((SystemState.getTcb?_eq_some_iff _ _ _).mp hx)
    rw [hPre] at hy; cases hy; exact hB (he.trans hr.1)
  refine SystemState.currentDequeuedUniqueExcept_updateTcb_offWrite h2 d2 (fun c hc => ?_)
    (fun c => ?_) ?_ (fun _ _ => rfl) (fun x hx => .inl ?_)
  · rw [hSch] at hc
    rcases (d1.current c r hc).2.2 with h | h
    · cases h
    · exact hNR h
  · rw [SystemState.queuedOn_congr_of_refined r1 r2 c r (by rw [hSch])]
    cases hq : st1.queuedOn c r
    · rfl
    · exact absurd (d1.queuedRunnable c r hq) hNR
  · cases hI : isIdleThreadId r
    · rfl
    · obtain ⟨c, rfl⟩ := (isIdleThreadId_iff r).mp hI
      exact absurd (d1.idleRunnable c) hNR
  · obtain ⟨t, ht, hti⟩ := storeTcbIpcStateAndMessage_getTcb?_ipcState _ _ _ _ _ h1 hS
    rw [ht] at hx; cases hx; exact hti

/-- **The receive** of core `c`'s current thread: a rendezvous with a calling
sender hands it to `.blockedOnReply` (it was blocked, so the store moves no
thread off the steady state); with any other sender it wakes the send-queue
head it pops (`hHeads`); the block enqueues the receiver, blocks it, stashes its
reply object and deschedules it. -/
theorem endpointReceiveDualOnCore_runQueueEntryStage (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId) (c : Concurrency.CoreId)
    (st : SystemState) (hHeads : endpointHeadsWakeable st)
    (hCur : st.scheduler.currentOnCore c = some receiver)
    (hNI : isIdleThreadId receiver = false) (hAct : st.activeAt receiver) :
    SystemState.RunQueueEntryStage st
      (endpointReceiveDualOnCore endpointId receiver replyId c st).1 := by
  unfold endpointReceiveDualOnCore
  split
  · split
    · split
      · exact (RunQueueStage.refl _).entry
      · rename_i sender senderTcb st1 hPop
        dsimp only
        split
        · rename_i hCall
          have hB : senderTcb.ipcState ≠ .ready := by rw [hCall]; exact fun h => by cases h
          simp only [↓reduceIte]
          split
          · split
            · exact (RunQueueStage.refl _).entry
            · rename_i st2 hS2
              split
              · exact (RunQueueStage.refl _).entry
              · split
                · exact (RunQueueStage.refl _).entry
                · rename_i st3 hL
                  split
                  · rename_i st4 hS4
                    exact ((endpointQueuePopHead_then_blockedStore_runQueueStage hPop hS2 hB).trans
                      ((linkCallerReply_runQueueStage hL).trans
                        ((storeTcbIpcStateAndMessage_runQueueStage hS4 rfl).trans
                          (SystemState.linkReplyWaiter_runQueueStage _ _ _)))).entry
                  · exact (RunQueueStage.refl _).entry
          · split
            · exact (RunQueueStage.refl _).entry
            · rename_i st2 hS2
              split
              · rename_i st4 hS4
                exact (endpointQueuePopHead_then_inactiveStore_runQueueEntryStage hPop hS2 hB).trans
                  (storeTcbIpcStateAndMessage_runQueueStage hS4 rfl).entry
              · exact (RunQueueStage.refl _).entry
        · simp only [Bool.false_eq_true, ↓reduceIte]
          split
          · exact (RunQueueStage.refl _).entry
          · rename_i st2 hS2
            split
            · rename_i st4 hS4
              exact ((((endpointQueuePopHead_runQueueStage hPop).trans
                (storeTcbIpcStateAndMessage_runQueueStage hS2 rfl)).then_wake c
                ((hHeads.popped hPop).of_scheduler_eq
                  (storeTcbIpcStateAndMessage_scheduler_eq _ _ _ _ _ hS2))
                (hHeads.popped_blocked hPop)).trans
                (storeTcbIpcStateAndMessage_runQueueStage hS4 rfl)).entry
            · exact (RunQueueStage.refl _).entry
    · split
      · exact (RunQueueStage.refl _).entry
      · rename_i stC hC
        split
        · exact (RunQueueStage.refl _).entry
        · rename_i st1 hE
          split
          · exact (RunQueueStage.refl _).entry
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
            · exact pre.blockThenDeschedule hS2 (RunQueueStage.refl _) hC1 hC2 hNI
            · rename_i rTcb hT
              split
              · split
                · exact (RunQueueStage.refl _).entry
                · rename_i st3 hS3
                  exact pre.blockThenDeschedule hS2
                    (RunQueueStage.of_invExt fun hI => (recordReplyStasher_runQueueStage _ _ _).trans
                      (storeObject_tcbOver_runQueueStage (old := rTcb)
                        (by rw [SystemState.recordReplyStasher_getTcb? _ _ _ hI]; exact hT) hS3
                        (fun _ => rfl))) hC1
                    (currentOnCore_of_scheduler_eq ((storeObject_scheduler_eq _ _ _ _ hS3).trans
                      (SystemState.recordReplyStasher_scheduler _ _ _)) hC2) hNI
              · exact (RunQueueStage.refl _).entry
  · split <;> exact (RunQueueStage.refl _).entry

theorem endpointReceiveDualWithCapsOnCore_runQueueEntryStage (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (c : Concurrency.CoreId) (st : SystemState)
    (hHeads : endpointHeadsWakeable st) (hCur : st.scheduler.currentOnCore c = some receiver)
    (hNI : isIdleThreadId receiver = false) (hAct : st.activeAt receiver) :
    SystemState.RunQueueEntryStage st
      (endpointReceiveDualWithCapsOnCore endpointId receiver replyId c st).1 := by
  have s0 := endpointReceiveDualOnCore_runQueueEntryStage endpointId receiver replyId c st
    hHeads hCur hNI hAct
  unfold endpointReceiveDualWithCapsOnCore
  generalize endpointReceiveDualOnCore endpointId receiver replyId c st = r at s0 ⊢
  obtain ⟨st1, r⟩ := r
  cases r with
  | error e => exact s0
  | ok res =>
    dsimp only
    repeat' split
    all_goals first
      | exact s0
      | (rename_i hU; exact s0.trans (receiveTransferCaps_runQueueStage hU).entry)

end SeLe4n.Kernel
