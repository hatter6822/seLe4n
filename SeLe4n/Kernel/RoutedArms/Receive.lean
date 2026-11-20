-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RoutedArms.Report

/-!
# The receive route's arm, out of line

The routed entry's `.receive` arm (`syscallEntryCheckedK`) as its own
function: the operand's address and the reply object's address cross as
words, `handleRecv`'s `canReply` as a flag, the state owned, and the result is the state with its
report pushed (`RoutedArms.Report`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The receive arm**: `dispatchOperandCheckedK` on the operand and the
receive's arm and taint step (`receiveOperandArmThenTaintR`), its results
reported; its reply capability's failed lookup is reported with the reply
capability's address (`replyLookupRefusalW`), the receive's capability fault. -/
@[noinline] def receiveRoutedArm (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (capWord : UInt64) (xc : Nat) (canReply : Bool) (replyWord : UInt64)
    (st : SystemState) : SystemState :=
  dispatchOperandCheckedKW .receive (SeLe4n.CPtr.ofWord capWord) tid executingCore xc
    (receiveOperandArmThenTaintR ctx tid canReply (SeLe4n.CPtr.ofWord replyWord) executingCore
      (syscallRequiredRight .receive))
    st entryReportGeneral (entryReportPushOk 1)
    (replyLookupRefusalW canReply tid (SeLe4n.CPtr.ofWord replyWord) (entryReportPushErrorW 1) (entryReportPushLookupAtW replyWord))
    entryReportLookup entryReportLookupAtW

end SeLe4n.Kernel
