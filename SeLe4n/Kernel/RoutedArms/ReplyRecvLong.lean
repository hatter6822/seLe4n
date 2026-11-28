-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RoutedArms.Report
import SeLe4n.Kernel.RoutedArms.ReplyRecv

/-!
# The long reply-receive route's arm, out of line

The routed entry's `.replyRecvLong` arm (`syscallEntryCheckedK`): a
reply-receive of more than the inline words, as its own function, read and
filled as the long reply's (`replyRecvLongRoutedArm`): slot 0 read, the
reply-receive dispatched through its long arm in continuation form
(`replyRecvLongOperandArmThenTaintKW`, `replyRecvLongOperandArmThenTaintR`'s)
on the state it is handed, its
receive capability read after the reply where the reply answers and the entry
refuses it (`replyRecvOperandCheckedKW`).  The
replier's TCB is read here, off the state the arm is handed.

An overflow slot that does not read clamps the message to its four inline
words, as seL4's `handleInvocation` clamps a message with no IPC buffer, and
the short route's arm runs on it (`replyRecvRoutedArm`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

set_option maxHeartbeats 400000 in
/-- **The long reply-receive arm**: slot 0 read, then the
reply-receive's operand dispatch on the state it is handed; a refusal reported
under the entry's resolved or lookup continuation as the dispatch told them
apart, a result under the first.  The arm inlines the long reply-receive's
whole checked transition, as the short arm does (`replyRecvRoutedArm`), whose
compilation takes more than the default heartbeats. -/
@[noinline] def replyRecvLongRoutedArm (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (capWord : UInt64) (xc : Nat) (length extraCaps label : Nat) (st : SystemState) :
    SystemState :=
  match st.getObject? tid.toObjId with
  | some (.tcb tcb) =>
      SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
        (fun _ => replyRecvRoutedArm ctx executingCore tid capWord xc 4 extraCaps label st)
        (fun _ => replyRecvOperandCheckedKW ctx (SeLe4n.CPtr.ofWord capWord) tid executingCore xc
                  (replyRecvLongOperandArmThenTaintKW ctx tcb.registerContext length extraCaps label
                    tid executingCore (syscallRequiredRight .replyRecv))
                  st entryReportGeneral (entryReportPushOk 1)
                  (replyLookupRefusalW true tid (replyRecvReplyAddr tcb.registerContext)
                    (entryReportPushErrorW 1)
                    (entryReportPushLookupAtW (replyRecvReplyAddr tcb.registerContext).word))
                  entryReportLookup entryReportLookupAtW
                  (fun s => replyRecvAnswersOn ctx tid
                    (SeLe4n.readRegWord tcb.registerContext SeLe4n.arm64DefaultLayout.replyReg)
                    extraCaps s)
                  (fun s => replyRecvAfterReplyRoutedArm ctx executingCore tid capWord
                    (longReplyRegs s tid tcb.registerContext length) length extraCaps label s))
  | _ => entryReportGeneral (.error (.illegalState, st))

/-- **The long reply-receive arm is the specification's routed reply-receive**
(`replyRecvRoutedK`) in each of the overflow read's continuations, on a running
caller. -/
theorem replyRecvLongRoutedArm_eq (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (capWord : UInt64) (length extraCaps label : Nat)
    (st : SystemState) (hCur : st.scheduler.currentOnCore executingCore = some tid) :
    replyRecvLongRoutedArm ctx executingCore tid capWord 0 length extraCaps label st =
      match st.getObject? tid.toObjId with
      | some (.tcb tcb) =>
        SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
          (fun _ => replyRecvRoutedArm ctx executingCore tid capWord 0 4 extraCaps label st)
          (fun _ => replyRecvRoutedK ctx
            (replyRecvRoutedDecode (SeLe4n.CPtr.ofWord capWord)
              (longReplyRegs st tid tcb.registerContext length)
              (SeLe4n.CPtr.ofWord
                (SeLe4n.readRegWord tcb.registerContext SeLe4n.arm64DefaultLayout.replyReg))
              length extraCaps label)
            tid executingCore st entryReportResolved entryReportLookupFor
            (dispatchOperandCheckedK .replyRecv (SeLe4n.CPtr.ofWord capWord) tid executingCore 0
              (replyRecvLongOperandArmThenTaintR ctx tcb.registerContext length extraCaps label
                tid executingCore (syscallRequiredRight .replyRecv))
              st entryReportGeneral
              (replyLookupRefusal true tid (replyRecvReplyAddr tcb.registerContext)
                entryReportResolved
                (entryReportLookupAt (replyRecvReplyAddr tcb.registerContext).word))
              entryReportLookupFor))
      | _ => entryReportGeneral (.error (.illegalState, st)) := by
  unfold replyRecvLongRoutedArm
  cases hT : st.getObject? tid.toObjId with
  | none => rfl
  | some o =>
    cases o with
    | tcb tcb =>
      dsimp only
      congr 1
      funext _
      refine (replyRecvOperandCheckedKW_eq ctx
        (replyRecvRoutedDecode (SeLe4n.CPtr.ofWord capWord)
          (longReplyRegs st tid tcb.registerContext length)
          (SeLe4n.CPtr.ofWord
            (SeLe4n.readRegWord tcb.registerContext SeLe4n.arm64DefaultLayout.replyReg))
          length extraCaps label) tid executingCore 0 _ _ st _ _ _ _ _ _ _ tcb
        (funext fun c => funext fun s => funext fun noCap => funext fun kOk => funext fun kErr =>
          funext fun onL => replyRecvLongOperandArmThenTaintKW_eq ctx _ _ _ _ _ _ _ c s noCap kOk
            kErr onL) rfl hT rfl
        (fun cap hRes hG => replyRecvLongOperandArmThenTaintR_gateRefused ctx _ _ _ _ _ _ cap st
          hRes hG)
        (replyRecvAnswersOn_eq ctx _ tid tcb st _ hT rfl)).trans ?_
      have hIs : (st.scheduler.currentOnCore executingCore).isEqSome tid = true :=
        (threadId_isEqSome_iff _ _).2 hCur
      rw [hIs, dispatchOperandCheckedKW_reportReply]
      cases hR : replyRecvRefusedOnEntry? ctx
          (replyRecvRoutedDecode (SeLe4n.CPtr.ofWord capWord)
            (longReplyRegs st tid tcb.registerContext length)
            (SeLe4n.CPtr.ofWord
              (SeLe4n.readRegWord tcb.registerContext SeLe4n.arm64DefaultLayout.replyReg))
            length extraCaps label) tid st with
      | none =>
        rw [replyRecvRoutedK_of_none hR]
        rfl
      | some q =>
        simp only [Option.isSome_some, ↓reduceIte]
        unfold replyRecvAfterReplyRoutedArm
        rw [hT]
        dsimp only
        rw [replyRecvAfterReplyRoutedOn_eq]
        unfold replyRecvRoutedK
        unfold replyRecvReplyAddr
        rw [hR]
    | _ => rfl

end SeLe4n.Kernel
