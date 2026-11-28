-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RoutedArms.Report
import SeLe4n.Kernel.RoutedArms.ReplyRecvAfterReply

/-!
# The reply-receive route's arm, out of line

The routed entry's `.replyRecv` arm (`syscallEntryCheckedK`) as its own
function: the operand's address and the message info's length, capability
count and label cross as words, the state owned, and the result is the state
with its report pushed (`RoutedArms.Report`).
Where the reply answers a caller and the entry refuses the receive capability,
the reply step runs first and the receive capability is read on the state it
left (`replyRecvOperandCheckedKW`, `replyRecvAfterReplyRoutedArm`), as seL4's
`handleRecv` runs after `handleInvocation`.
The caller's saved register file is read here, off the state the arm is
handed, rather than crossing the call: passed in, it would be held across the
whole arm by the entry's reference, and every write to it the arm makes would
copy it.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

set_option maxHeartbeats 400000 in
/-- **The reply-receive arm**: `replyRecvOperandCheckedKW` on the operand and
the reply-receive's arm and taint step (`replyRecvOperandArmThenTaintR`) over
the caller's message registers, its results reported; a refusal of the receive
capability that writes nothing runs the after-reply route where the reply
answers (`replyRecvAfterReplyRoutedArm`).  The arm inlines the reply-receive's
whole checked transition, whose compilation takes more than the default
heartbeats. -/
@[noinline] def replyRecvRoutedArm (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (capWord : UInt64) (xc : Nat) (length extraCaps label : Nat)
    (st : SystemState) : SystemState :=
  match st.getObject? tid.toObjId with
  | some (.tcb tcb) =>
    replyRecvOperandCheckedKW ctx (SeLe4n.CPtr.ofWord capWord) tid executingCore xc
      (replyRecvOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout tcb.registerContext length
        extraCaps label tid executingCore (syscallRequiredRight .replyRecv))
      st entryReportGeneral (entryReportPushOk 1)
      (replyLookupRefusalW true tid (replyRecvReplyAddr tcb.registerContext)
        (entryReportPushErrorW 1)
        (entryReportPushLookupAtW (replyRecvReplyAddr tcb.registerContext).word))
      entryReportLookup entryReportLookupAtW
      (fun s => replyRecvAnswersOn ctx tid
        (SeLe4n.readRegWord tcb.registerContext SeLe4n.arm64DefaultLayout.replyReg) extraCaps s)
      (fun s => replyRecvAfterReplyRoutedArm ctx executingCore tid capWord
        (Architecture.regMessageRegs SeLe4n.arm64DefaultLayout tcb.registerContext) length
        extraCaps label s)
  | _ => entryReportGeneral (.error (.illegalState, st))

/-- **The reply-receive arm is the specification's routed reply-receive**
(`replyRecvRoutedK`): the entry's operand route where the after-reply route
does not run, the after-reply route where it does, on a running caller. -/
theorem replyRecvRoutedArm_eq (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (capWord : UInt64) (length extraCaps label : Nat)
    (st : SystemState) (hCur : st.scheduler.currentOnCore executingCore = some tid) :
    replyRecvRoutedArm ctx executingCore tid capWord 0 length extraCaps label st =
      match st.getObject? tid.toObjId with
      | some (.tcb tcb) =>
        replyRecvRoutedK ctx
          (replyRecvRoutedDecode (SeLe4n.CPtr.ofWord capWord)
            (Architecture.regMessageRegs SeLe4n.arm64DefaultLayout tcb.registerContext)
            (SeLe4n.CPtr.ofWord
              (SeLe4n.readRegWord tcb.registerContext SeLe4n.arm64DefaultLayout.replyReg))
            length extraCaps label)
          tid executingCore st entryReportResolved entryReportLookupFor
          (dispatchOperandCheckedK .replyRecv (SeLe4n.CPtr.ofWord capWord) tid executingCore 0
            (replyRecvOperandArmThenTaintR ctx SeLe4n.arm64DefaultLayout tcb.registerContext
              length extraCaps label tid executingCore (syscallRequiredRight .replyRecv))
            st entryReportGeneral
            (replyLookupRefusal true tid (replyRecvReplyAddr tcb.registerContext)
              entryReportResolved
              (entryReportLookupAt (replyRecvReplyAddr tcb.registerContext).word))
            entryReportLookupFor)
      | _ => entryReportGeneral (.error (.illegalState, st)) := by
  unfold replyRecvRoutedArm
  cases hT : st.getObject? tid.toObjId with
  | none => rfl
  | some o =>
    cases o with
    | tcb tcb =>
      dsimp only
      refine (replyRecvOperandCheckedKW_eq ctx
        (replyRecvRoutedDecode (SeLe4n.CPtr.ofWord capWord)
          (Architecture.regMessageRegs SeLe4n.arm64DefaultLayout tcb.registerContext)
          (SeLe4n.CPtr.ofWord
            (SeLe4n.readRegWord tcb.registerContext SeLe4n.arm64DefaultLayout.replyReg))
          length extraCaps label) tid executingCore 0 _ st _ _ _ _ _ _ _ tcb rfl hT rfl
        (fun cap hRes hG => replyRecvOperandArmThenTaintR_gateRefused ctx _ _ _ _ _ _ _ cap st
          hRes hG)
        (replyRecvAnswersOn_eq ctx _ tid tcb st _ hT rfl)).trans ?_
      have hIs : (st.scheduler.currentOnCore executingCore).isEqSome tid = true :=
        (threadId_isEqSome_iff _ _).2 hCur
      rw [hIs, dispatchOperandCheckedKW_reportReply]
      cases hR : replyRecvRefusedOnEntry? ctx
          (replyRecvRoutedDecode (SeLe4n.CPtr.ofWord capWord)
            (Architecture.regMessageRegs SeLe4n.arm64DefaultLayout tcb.registerContext)
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
