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
transfer, are `RunQueueStage`s (`SystemState.RunQueueStage`): each wakes or
deschedules through the stages `IPC.Invariant.RunQueueAgreement` proves and
writes no other run-queue field.

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

theorem storeTcbReceiveComplete_runQueueStage {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {m : Option IpcMessage} (h : storeTcbReceiveComplete st tid m = .ok st') :
    RunQueueStage st st' :=
  modifyTcb_runQueueStage h (fun _ _ => rfl)

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
    (RunQueueStage.storeObject (by with_reducible assumption) (fun _ => by run_queue_slot_same)))
macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (removeRunnableOnCore_runQueueStage _ _ _))
macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (wakeThread_runQueueStage _ _ _))
macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_
    (RunQueueStage.of_fst_eq (wakeThread_runQueueStage _ _ _) (by with_reducible assumption)))
macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (endpointQueuePopHead_runQueueStage (by with_reducible assumption)))
macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (endpointQueueEnqueue_runQueueStage (by with_reducible assumption)))
macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (storeTcbReceiveComplete_runQueueStage (by with_reducible assumption)))
macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (storeTcbIpcStateAndMessage_runQueueStage (by with_reducible assumption)))
macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (ipcUnwrapCaps_runQueueStage (by with_reducible assumption)))

theorem endpointSendDualOnCore_runQueueStage (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage) (c : Concurrency.CoreId)
    (st : SystemState) :
    RunQueueStage st (endpointSendDualOnCore endpointId sender msg c st).1 := by
  unfold endpointSendDualOnCore
  run_queue_stage_split
  all_goals run_queue_stage

macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_
    (RunQueueStage.of_fst_eq (endpointSendDualOnCore_runQueueStage _ _ _ _ _) (by with_reducible assumption)))

theorem endpointSendDualWithCapsOnCore_runQueueStage (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage) (rights : AccessRightSet)
    (base : SeLe4n.Slot) (c : Concurrency.CoreId) (st : SystemState) :
    RunQueueStage st
      (endpointSendDualWithCapsOnCore endpointId sender msg rights base c st).1 := by
  unfold endpointSendDualWithCapsOnCore
  run_queue_stage_split
  all_goals run_queue_stage

theorem cleanupPreReceiveDonationChecked_runQueueStage {st st' : SystemState}
    {receiver : SeLe4n.ThreadId} (h : cleanupPreReceiveDonationChecked st receiver = .ok st') :
    RunQueueStage st st' := by
  unfold cleanupPreReceiveDonationChecked at h
  split at h
  · cases h; exact RunQueueStage.refl _
  · split at h
    · exact returnDonatedSchedContextResolved_runQueueStage h
    · cases h; exact RunQueueStage.refl _

theorem preReceiveReturnMigration_runQueueStage (st stClean : SystemState)
    (receiver : SeLe4n.ThreadId) :
    RunQueueStage stClean (preReceiveReturnMigration st stClean receiver) := by
  unfold preReceiveReturnMigration
  split
  · exact migrateSchedContextReplenishment_runQueueStage _ _ _ _
  · exact RunQueueStage.refl _

theorem cleanupPreReceiveDonationMigrated_runQueueStage {st st' : SystemState}
    {receiver : SeLe4n.ThreadId} (h : cleanupPreReceiveDonationMigrated st receiver = .ok st') :
    RunQueueStage st st' := by
  obtain ⟨stClean, hC, rfl⟩ := cleanupPreReceiveDonationMigrated_ok_decompose h
  exact (cleanupPreReceiveDonationChecked_runQueueStage hC).trans
    (preReceiveReturnMigration_runQueueStage _ _ _)

macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (cleanupPreReceiveDonationMigrated_runQueueStage (by with_reducible assumption)))
macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_ (linkCallerReply_runQueueStage (by with_reducible assumption)))
macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_
    (storeObject_tcbOver_runQueueStage (by with_reducible assumption) (by with_reducible assumption) (by intro; rfl)))

theorem endpointReceiveDualOnCore_runQueueStage (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId) (c : Concurrency.CoreId)
    (st : SystemState) :
    RunQueueStage st (endpointReceiveDualOnCore endpointId receiver replyId c st).1 := by
  unfold endpointReceiveDualOnCore
  run_queue_stage_split
  all_goals run_queue_stage

macro_rules | `(tactic| run_queue_stage_step) => `(tactic|
  refine RunQueueStage.trans ?_
    (RunQueueStage.of_fst_eq (endpointReceiveDualOnCore_runQueueStage _ _ _ _ _) (by with_reducible assumption)))

theorem endpointReceiveDualWithCapsOnCore_runQueueStage (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId) (root : SeLe4n.ObjId)
    (base : SeLe4n.Slot) (c : Concurrency.CoreId) (st : SystemState) :
    RunQueueStage st
      (endpointReceiveDualWithCapsOnCore endpointId receiver replyId root base c st).1 := by
  unfold endpointReceiveDualWithCapsOnCore
  run_queue_stage_split
  all_goals run_queue_stage

end SeLe4n.Kernel
