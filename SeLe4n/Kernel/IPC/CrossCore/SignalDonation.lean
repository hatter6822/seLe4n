-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.NotificationBind
import SeLe4n.Kernel.SchedContext.NotificationDonationContextLabel

/-!
# seL4's `sendSignal`, its donations included

seL4-MCS `sendSignal` (`notification.c`) wakes a thread in two places: the
thread bound to an idle notification while it is blocked on a receive, and the
head of a waiting notification's queue.  At each it runs `MCS_DO_IF_SC`:
`maybeDonateSchedContext(tcb, ntfnPtr)` and then `possibleSwitchTo` when the
thread is schedulable.

`sendSignalOnCore` is the signal (`notificationSignalBoundOnCore`) followed by
that donation to the thread it woke (`signalWokenThread?`, read on the state the
signal is handed), the notification's context donated under seL4's guard
(`maybeDonateSchedContext`).  The wake places the thread first, so the bind
finds it placed.  A signal that wakes nothing (it accumulates the word) donates
nothing, as seL4's `ActiveNtfn` and idle-unbound cases do not.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

/-- **The donation after a signal**: the notification's context donated to the
thread the signal woke (`maybeDonateSchedContext`), the state as it was when the
signal woke none. -/
def donateToSignalled (st st' : SystemState) (n : SeLe4n.ObjId) : SystemState :=
  match signalWokenThread? st n with
  | some t => maybeDonateSchedContext st' n t
  | none => st'

/-- **seL4-MCS `sendSignal`**: the signal (`notificationSignalBoundOnCore`), and
on success the donation to the thread it woke (`donateToSignalled`).  A refused
signal returns its own state and error. -/
def sendSignalOnCore (n : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) : SystemState × Except KernelError (Option (CoreId × SgiKind)) :=
  match notificationSignalBoundOnCore n badge executingCore st with
  | (st', .ok sgi) => (donateToSignalled st st' n, .ok sgi)
  | (st', .error e) => (st', .error e)

/-- **The compiled `sendSignalOnCore`**: the thread the signal wakes is read
before the signal, so the state is handed to the signal alone and its writes
are made in place.  The specification reads that thread on the pre-state after
the signal has run, which keeps the pre-state alive across the signal's writes
and so copies the object store on every compiled signal; the read moves no
write (`sendSignalOnCore_eq_impl`).  A signal that wakes nothing is the signal
itself; the donation runs in its compiled form
(`maybeDonateSchedContextFast_eq`). -/
@[inline] def sendSignalOnCoreImpl (n : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (Option (CoreId × SgiKind)) :=
  match signalWokenThread? st n with
  | none => notificationSignalBoundOnCore n badge executingCore st
  | some t =>
    match notificationSignalBoundOnCore n badge executingCore st with
    | (st', .ok sgi) => (maybeDonateSchedContextFast st' n.val t.val, .ok sgi)
    | (st', .error e) => (st', .error e)

@[csimp] theorem sendSignalOnCore_eq_impl : @sendSignalOnCore = @sendSignalOnCoreImpl := by
  funext n badge c st
  unfold sendSignalOnCore sendSignalOnCoreImpl donateToSignalled
  cases hW : signalWokenThread? st n with
  | none =>
    simp only []
    rcases notificationSignalBoundOnCore n badge c st with ⟨st', r⟩
    cases r <;> rfl
  | some t =>
    simp only [maybeDonateSchedContextFast_eq]

/-- The signal's answer is the wake's: the donation writes state alone. -/
theorem sendSignalOnCore_snd (n : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId)
    (st : SystemState) :
    (sendSignalOnCore n badge c st).2 = (notificationSignalBoundOnCore n badge c st).2 := by
  unfold sendSignalOnCore
  rcases notificationSignalBoundOnCore n badge c st with ⟨st', r⟩
  cases r <;> rfl

/-- **The signal's state is the wake's, or the donation on it**: every family
lemma of the signal is the wake's composed with the donation's. -/
theorem sendSignalOnCore_fst (n : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId)
    (st : SystemState) :
    (sendSignalOnCore n badge c st).1 =
      match (notificationSignalBoundOnCore n badge c st).2 with
      | .ok _ => donateToSignalled st (notificationSignalBoundOnCore n badge c st).1 n
      | .error _ => (notificationSignalBoundOnCore n badge c st).1 := by
  unfold sendSignalOnCore
  rcases notificationSignalBoundOnCore n badge c st with ⟨st', r⟩
  cases r <;> rfl

/-- **A property the wake carries and every donation after it carries, the
signal carries.**  The donation's case names the thread the signal woke and the
state the wake left. -/
theorem sendSignalOnCore_induct (P : SystemState → Prop) (n : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st : SystemState)
    (hWake : P (notificationSignalBoundOnCore n badge c st).1)
    (hDonate : ∀ t sgi, signalWokenThread? st n = some t →
      (notificationSignalBoundOnCore n badge c st).2 = .ok sgi →
      P (maybeDonateSchedContext (notificationSignalBoundOnCore n badge c st).1 n t)) :
    P (sendSignalOnCore n badge c st).1 := by
  rw [sendSignalOnCore_fst]
  cases hR : (notificationSignalBoundOnCore n badge c st).2 with
  | error e => exact hWake
  | ok sgi =>
    dsimp only
    unfold donateToSignalled
    cases hW : signalWokenThread? st n with
    | none => exact hWake
    | some t => exact hDonate t sgi hW hR

/-- A refused signal donates nothing: its state is the wake's. -/
theorem sendSignalOnCore_fst_of_error {n : SeLe4n.ObjId} {badge : SeLe4n.Badge} {c : CoreId}
    {st : SystemState} {e : KernelError}
    (h : (notificationSignalBoundOnCore n badge c st).2 = .error e) :
    (sendSignalOnCore n badge c st).1 = (notificationSignalBoundOnCore n badge c st).1 := by
  rw [sendSignalOnCore_fst, h]

/-! ### The checked signal: the donation under the context-label check

The checked kernel's `sendSignal` (`sendSignalOnCoreFlowing`): the same wake,
then the donation to the thread it woke under the context-label check
(`maybeDonateSchedContextFlowing`), so the notification's context is lent only
to a thread its label flows to, and otherwise the wake alone is made, seL4's
"do nothing" branch of the donation. -/

/-- **The checked donation after a signal.** -/
def donateToSignalledFlowing (ctx : LabelingContext) (st st' : SystemState) (n : SeLe4n.ObjId) :
    SystemState :=
  match signalWokenThread? st n with
  | some t => maybeDonateSchedContextFlowing ctx st' n t
  | none => st'

/-- **The checked donation after a signal, under a generic labelling context**
(the declassifying signal's). -/
def donateToSignalledFlowingGeneric (gctx : GenericLabelingContext) (st st' : SystemState)
    (n : SeLe4n.ObjId) : SystemState :=
  match signalWokenThread? st n with
  | some t => maybeDonateSchedContextFlowingGeneric gctx st' n t
  | none => st'

/-- The checked donations after a signal keep the declassification audit
trail, as the donation does. -/
theorem donateToSignalledFlowing_declassificationAuditLog_eq (ctx : LabelingContext)
    (st st' : SystemState) (n : SeLe4n.ObjId) :
    (donateToSignalledFlowing ctx st st' n).declassificationAuditLog =
      st'.declassificationAuditLog := by
  unfold donateToSignalledFlowing
  split
  · exact maybeDonateSchedContextFlowing_induct
      (fun s => s.declassificationAuditLog = st'.declassificationAuditLog) ctx st' n _ rfl
      (maybeDonateSchedContext_declassificationAuditLog_eq _ _ _)
  · rfl

theorem donateToSignalledFlowingGeneric_declassificationAuditLog_eq
    (gctx : GenericLabelingContext) (st st' : SystemState) (n : SeLe4n.ObjId) :
    (donateToSignalledFlowingGeneric gctx st st' n).declassificationAuditLog =
      st'.declassificationAuditLog := by
  unfold donateToSignalledFlowingGeneric
  split
  · exact maybeDonateSchedContextFlowingGeneric_induct
      (fun s => s.declassificationAuditLog = st'.declassificationAuditLog) gctx st' n _ rfl
      (maybeDonateSchedContext_declassificationAuditLog_eq _ _ _)
  · rfl

/-- **The checked `sendSignal`**: the signal (`notificationSignalBoundOnCore`),
and on success the checked donation to the thread it woke. -/
def sendSignalOnCoreFlowing (ctx : LabelingContext) (n : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (Option (CoreId × SgiKind)) :=
  match notificationSignalBoundOnCore n badge executingCore st with
  | (st', .ok sgi) => (donateToSignalledFlowing ctx st st' n, .ok sgi)
  | (st', .error e) => (st', .error e)

/-- **The compiled checked `sendSignal`**: the woken thread read before the
signal, as `sendSignalOnCoreImpl` does, and the donation in its compiled form. -/
@[inline] def sendSignalOnCoreFlowingImpl (ctx : LabelingContext) (n : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (Option (CoreId × SgiKind)) :=
  match signalWokenThread? st n with
  | none => notificationSignalBoundOnCore n badge executingCore st
  | some t =>
    match notificationSignalBoundOnCore n badge executingCore st with
    | (st', .ok sgi) => (maybeDonateSchedContextFlowingFast ctx st' n.val t.val, .ok sgi)
    | (st', .error e) => (st', .error e)

@[csimp] theorem sendSignalOnCoreFlowing_eq_impl :
    @sendSignalOnCoreFlowing = @sendSignalOnCoreFlowingImpl := by
  funext ctx n badge c st
  unfold sendSignalOnCoreFlowing sendSignalOnCoreFlowingImpl donateToSignalledFlowing
  cases hW : signalWokenThread? st n with
  | none =>
    simp only []
    rcases notificationSignalBoundOnCore n badge c st with ⟨st', r⟩
    cases r <;> rfl
  | some t =>
    simp only [maybeDonateSchedContextFlowingFast_eq]

/-- The checked signal's answer is the wake's. -/
theorem sendSignalOnCoreFlowing_snd (ctx : LabelingContext) (n : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st : SystemState) :
    (sendSignalOnCoreFlowing ctx n badge c st).2 = (sendSignalOnCore n badge c st).2 := by
  rw [sendSignalOnCore_snd]
  unfold sendSignalOnCoreFlowing
  rcases notificationSignalBoundOnCore n badge c st with ⟨st', r⟩
  cases r <;> rfl

/-- **The checked signal's state is the wake's, or the donation on it.** -/
theorem sendSignalOnCoreFlowing_induct (P : SystemState → Prop) (ctx : LabelingContext)
    (n : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId) (st : SystemState)
    (hWake : P (notificationSignalBoundOnCore n badge c st).1)
    (hDonate : ∀ t sgi, signalWokenThread? st n = some t →
      (notificationSignalBoundOnCore n badge c st).2 = .ok sgi →
      P (maybeDonateSchedContext (notificationSignalBoundOnCore n badge c st).1 n t)) :
    P (sendSignalOnCoreFlowing ctx n badge c st).1 := by
  unfold sendSignalOnCoreFlowing
  cases hS : notificationSignalBoundOnCore n badge c st with
  | mk st' r =>
    rw [hS] at hWake hDonate
    cases r with
    | error e => exact hWake
    | ok sgi =>
      dsimp only
      unfold donateToSignalledFlowing
      cases hW : signalWokenThread? st n with
      | none => exact hWake
      | some t =>
        exact maybeDonateSchedContextFlowing_induct P ctx st' n t hWake (hDonate t sgi hW rfl)

/-- A refused checked signal donates nothing: its state is the wake's. -/
theorem sendSignalOnCoreFlowing_fst_of_error {ctx : LabelingContext} {n : SeLe4n.ObjId}
    {badge : SeLe4n.Badge} {c : CoreId} {st : SystemState} {e : KernelError}
    (h : (notificationSignalBoundOnCore n badge c st).2 = .error e) :
    (sendSignalOnCoreFlowing ctx n badge c st).1 = (notificationSignalBoundOnCore n badge c st).1 := by
  unfold sendSignalOnCoreFlowing
  rcases hS : notificationSignalBoundOnCore n badge c st with ⟨st', r⟩
  rw [hS] at h
  cases r with
  | error e' => rfl
  | ok _ => cases h

end SeLe4n.Kernel
