-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ContextLenders.Interrupt
import SeLe4n.Kernel.InformationFlow.DeclassifiedSignal

/-! # The signal arms keep the lenders' flow

WS-SX SX8.  seL4's `sendSignal`, flow-checked (the syscall's `.notificationSignal`
arm) and declassifying (its `.declassifySignal` arm): the wake writes thread
records, the notification and the woken thread's endpoint queue, and the
donation to the woken thread binds a context without touching its stack head
(`LendersFrame.maybeDonateSchedContext`).  Neither lends a frame, so the
only premise is the store's invariant. -/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace LendersFrame

/-- The flow-checked signal: a refused gate returns the state. -/
theorem notificationSignalBoundCrossCoreDispatchChecked (ctx : LabelingContext)
    (n : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId) (badge : SeLe4n.Badge) (c : CoreId)
    (st : SystemState) (hInv : st.objects.invExt) :
    LendersFrame st
      (_root_.SeLe4n.Kernel.notificationSignalBoundCrossCoreDispatchChecked ctx n signaler badge c
        st).1 :=
  notificationSignalBoundCrossCoreDispatchChecked_induct (fun s => LendersFrame st s) ctx n
    signaler badge c st (refl hInv) (sendSignalOnCoreFlowing ctx n badge c st hInv)

/-- The declassifying wake: the bound signal's writes, then the audit trail;
a refusal returns the state. -/
theorem notificationSignalDeclassifiedOnCore (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (n : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId)
    (st : SystemState) (hInv : st.objects.invExt) :
    LendersFrame st
      (_root_.SeLe4n.Kernel.notificationSignalDeclassifiedOnCore ctx declPolicy n badge c st).1 := by
  unfold _root_.SeLe4n.Kernel.notificationSignalDeclassifiedOnCore
  have S : LendersFrame st (_root_.SeLe4n.Kernel.notificationSignalBoundOnCore n badge c st).1 :=
    ⟨(chainObjectsKept.notificationSignalBoundOnCore n badge c st hInv).linksShrink,
     notificationSignalBoundOnCore_preserves_objects_invExt n badge c st hInv⟩
  generalize _root_.SeLe4n.Kernel.notificationSignalBoundOnCore n badge c st = r at S
  obtain ⟨st1, res⟩ := r
  cases res <;> dsimp only at S ⊢ <;> repeat' split
  all_goals first
    | exact refl hInv
    | (rename_i hRec
       have hEq := recordDeclassifiedHops_frame _ _ _ _ _ hRec
       exact ⟨S.links.trans (chainObjectsKept.of_objects_eq (by rw [hEq])).linksShrink,
         by rw [hEq]; exact S.invExt⟩)

/-- The declassifying signal: the declassifying wake, then the donation to the
woken thread. -/
theorem notificationSignalDeclassifiedCrossCoreDispatch (ctx : GenericLabelingContext)
    (declPolicy : DeclassificationPolicy) (n : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId)
    (st : SystemState) (hInv : st.objects.invExt) :
    LendersFrame st
      (_root_.SeLe4n.Kernel.notificationSignalDeclassifiedCrossCoreDispatch ctx declPolicy n badge c
        st).1 :=
  have S := notificationSignalDeclassifiedOnCore ctx declPolicy n badge c st hInv
  notificationSignalDeclassifiedCrossCoreDispatch_induct (fun s => LendersFrame st s) ctx declPolicy
    n badge c st S (fun t _ _ _ => S.andThen fun h => maybeDonateSchedContext _ n t h)

end LendersFrame

end SeLe4n.Kernel
