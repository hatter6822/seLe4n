-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.NotificationBind

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

/-- The donation after a signal writes the object store and the scheduler
alone. -/
theorem donateToSignalled_onlyObjectsSchedulerDiffer (st st' : SystemState) (n : SeLe4n.ObjId) :
    SystemState.onlyObjectsSchedulerDiffer (donateToSignalled st st' n) st' := by
  unfold donateToSignalled
  split
  · exact maybeDonateSchedContext_onlyObjectsSchedulerDiffer _ _ _
  · exact .refl _

/-- …so it keeps the declassification audit trail. -/
theorem donateToSignalled_declassificationAuditLog_eq (st st' : SystemState) (n : SeLe4n.ObjId) :
    (donateToSignalled st st' n).declassificationAuditLog = st'.declassificationAuditLog := by
  have h := donateToSignalled_onlyObjectsSchedulerDiffer st st' n
  unfold SystemState.onlyObjectsSchedulerDiffer at h
  rw [h]

/-- **seL4-MCS `sendSignal`**: the signal (`notificationSignalBoundOnCore`), and
on success the donation to the thread it woke (`donateToSignalled`).  A refused
signal returns its own state and error. -/
def sendSignalOnCore (n : SeLe4n.ObjId) (badge : SeLe4n.Badge) (executingCore : CoreId)
    (st : SystemState) : SystemState × Except KernelError (Option (CoreId × SgiKind)) :=
  match notificationSignalBoundOnCore n badge executingCore st with
  | (st', .ok sgi) => (donateToSignalled st st' n, .ok sgi)
  | (st', .error e) => (st', .error e)

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

end SeLe4n.Kernel
