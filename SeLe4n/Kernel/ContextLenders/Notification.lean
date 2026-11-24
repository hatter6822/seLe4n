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

/-- The notification's context, read as its binding view. -/
theorem notificationContext?_eq_some_iff_view (st : SystemState) (n : SeLe4n.ObjId)
    (s : SeLe4n.SchedContextId) :
    notificationContext? st n = some s ↔ notificationContextView st n = s.val + 1 := by
  unfold notificationContext? notificationContextView
  cases st.getNotification? n with
  | none => simp
  | some ntfn =>
    show SeLe4n.SchedContextId.ofOptCode ntfn.schedContextCode = some s ↔
      ntfn.schedContextCode = s.val + 1
    generalize ntfn.schedContextCode = k
    cases k with
    | zero => simp
    | succ k => cases s; simp [SeLe4n.SchedContextId.ofOptCode]

/-- A notification's context after a binding shrink was its context before it. -/
theorem notificationContext?_of_bindingShrink {st st' : SystemState} (h : bindingViewsShrink st st')
    {n : SeLe4n.ObjId} {s : SeLe4n.SchedContextId} (hs : notificationContext? st' n = some s) :
    notificationContext? st n = some s :=
  (notificationContext?_eq_some_iff_view _ _ _).mpr
    (h.notification n s.val ((notificationContext?_eq_some_iff_view _ _ _).mp hs))

namespace LendersStep

/-- The flow-checked signal: a refused gate returns the state; the checked
donation's check is its label equation. -/
theorem notificationSignalBoundCrossCoreDispatchChecked (ctx : LabelingContext)
    (n : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId) (badge : SeLe4n.Badge) (c : CoreId)
    (st : SystemState) (hInv : st.objects.invExt) :
    LendersStep ctx st
      (_root_.SeLe4n.Kernel.notificationSignalBoundCrossCoreDispatchChecked ctx n signaler badge c
        st).1 :=
  notificationSignalBoundCrossCoreDispatchChecked_induct (fun s => LendersStep ctx st s) ctx n
    signaler badge c st (refl hInv) (sendSignalOnCoreFlowing ctx n badge c st hInv)

end LendersStep

namespace LendersFrame


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

end LendersFrame

/-- **The declassifying signal**: the declassifying wake, then the unchecked
donation to the woken thread, a creating site whose label equation (`hLend`: the
woken thread labelled as the notification's context, at the state the signal
runs from) the entry's premise pack carries (WS-SX SX17 discharges it). -/
theorem LendersStep.notificationSignalDeclassifiedCrossCoreDispatch (lctx : LabelingContext)
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy) (n : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st : SystemState) (hInv : st.objects.invExt)
    (hLend : ∀ t s, signalWokenThread? st n = some t → notificationContext? st n = some s →
      lctx.threadLabelOf t = lctx.objectLabelOf s.toObjId) :
    LendersStep lctx st
      (_root_.SeLe4n.Kernel.notificationSignalDeclassifiedCrossCoreDispatch ctx declPolicy n badge c
        st).1 :=
  have S := LendersFrame.notificationSignalDeclassifiedOnCore ctx declPolicy n badge c st hInv
  notificationSignalDeclassifiedCrossCoreDispatch_induct (fun s => LendersStep lctx st s) ctx
    declPolicy n badge c st (.of_frame S) (fun t _ hW _ => (LendersStep.of_frame S).andThen fun h =>
      LendersStep.maybeDonateSchedContext _ n t h fun s hs =>
        hLend t s hW (notificationContext?_of_bindingShrink S.links.binding hs))

end SeLe4n.Kernel
