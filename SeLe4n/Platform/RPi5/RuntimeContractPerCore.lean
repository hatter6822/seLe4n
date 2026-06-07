-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.RPi5.RuntimeContract

/-!
# WS-SM SM4.D audit-pass-3 — per-core RPi5 register-context runtime contract

`Platform/RPi5/RuntimeContract.lean`'s `registerContextStableCheck` is a
`Bool`-valued platform runtime-contract check that reads scheduler state
(`currentOnCore bootCoreId` and `.runnable`).  It is the **only**
scheduler-reading definition in the Platform layer outside the operations
that stay boot-core until SM5 (`syscallDispatchFromAbi`); a deep audit
found it had been missed by the SM4.D §5.4 file list (which covers the
IPC / capability / lifecycle / service / architecture / information-flow
subsystems, not the Platform/RPi5 runtime contract).

This module closes that gap with the per-core form
`registerContextStableCheckOnCore` (and the `Prop` wrapper
`registerContextStablePredOnCore`), parameterised by an explicit
`(c : CoreId)`, plus the boot-core bridge (`rfl`), a per-core idle
witness, and a default-state witness.  Additive and soundness-preserving:
the live RPi5 runtime-contract surface is untouched.  Staged-only; SM5's
per-core platform bring-up is the first runtime exerciser.

Axiom-clean: every theorem depends only on the standard foundational
axioms (`propext` / `Quot.sound` / `Classical.choice`).
-/

namespace SeLe4n.Platform.RPi5

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

/-- SM4.D: per-core form of `registerContextStableCheck` — the RPi5
register-context stability runtime contract evaluated against core `c`'s
current thread and run queue. -/
def registerContextStableCheckOnCore (_st st' : SystemState) (c : CoreId) : Bool :=
  match (st'.scheduler.currentOnCore c) with
  | none => true
  | some tid =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
      st'.machine.regsOnCore c == tcb.registerContext &&
      !(st'.scheduler.runQueueOnCore c).toList.contains tid &&
      (tcb.timeSlice > 0) &&
      (tcb.ipcState == .ready) &&
      (tcb.deadline.toNat == 0) &&
      budgetSufficientCheck st' tcb
    | _ => false

/-- SM4.D: `Prop`-level per-core register-context stability. -/
def registerContextStablePredOnCore (st st' : SystemState) (c : CoreId) : Prop :=
  registerContextStableCheckOnCore st st' c = true

/-- SM4.D: the per-core check at `bootCoreId` is the live single-core
`registerContextStableCheck` (`.runnable` is the boot-core run-queue
projection, so the bodies coincide definitionally). -/
theorem registerContextStableCheckOnCore_bootCore (st st' : SystemState) :
    registerContextStableCheckOnCore st st' bootCoreId = registerContextStableCheck st st' := rfl

theorem registerContextStablePredOnCore_bootCore_iff (st st' : SystemState) :
    registerContextStablePredOnCore st st' bootCoreId ↔ registerContextStablePred st st' := by
  unfold registerContextStablePredOnCore registerContextStablePred
  rw [registerContextStableCheckOnCore_bootCore]

/-- SM4.D: on an idle core (no current thread) the contract holds (returns
`true`) regardless of the rest of the state. -/
theorem registerContextStableCheckOnCore_true_of_currentNone (st st' : SystemState) (c : CoreId)
    (hCur : st'.scheduler.currentOnCore c = none) :
    registerContextStableCheckOnCore st st' c = true := by
  simp only [registerContextStableCheckOnCore, hCur]

/-- SM4.D: the contract holds on the freshly-booted system on every core
(each core's `current` is `none`). -/
theorem default_registerContextStableCheckOnCore (st : SystemState) (c : CoreId) :
    registerContextStableCheckOnCore st (default : SystemState) c = true :=
  registerContextStableCheckOnCore_true_of_currentNone st (default : SystemState) c
    (default_state_perCoreInitialized c).1

end SeLe4n.Platform.RPi5
