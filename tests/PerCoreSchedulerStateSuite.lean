-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State
import SeLe4n.Kernel.Concurrency.Types

/-!
# WS-SM SM4.B — Per-core `SchedulerState` accessor + theorem test suite

Tier-2 (runtime) + Tier-3 (surface anchor) coverage for the WS-SM Phase
SM4.B "SchedulerState path-a replacement" foundation:

* **SM4.B.8** — the seven per-core accessors
  (`SchedulerState.currentOnCore` / `runQueueOnCore` /
  `replenishQueueOnCore` / `activeDomainOnCore` /
  `domainTimeRemainingOnCore` / `domainScheduleIndexOnCore` /
  `lastTimeoutErrorsOnCore`), each taking an explicit `c : CoreId`, plus
  the seven matching `set…OnCore` writers (the path-a write API).
* **SM4.B.phase-2 store/load algebra** — the 63 `@[simp]` lemmas that
  reduce post-write reads: the 7 read-after-write `set…OnCore_…OnCore_self`
  lemmas, the 42 cross-field `set…OnCore_…OnCore` frames, and the 14
  system-wide-field frames. (Anchored + exercised through proven `example`s
  here; consumed pervasively in the downstream preservation/NI proofs.)
* **SM4.B.9** — `default_state_perCoreInitialized`: the default scheduler
  state reads the neutral value on every core (plan §3.6).
* **SM4.B.10** — `SchedulerState.ext_perCore`: per-core extensionality
  (plan §3.3).

These are checked at elaboration time (`#check` surface anchors +
`example`s discharged through the proven theorems) and at runtime
(`assertBool` mirrors via `lake exe per_core_scheduler_state_suite`, so a
silent regression surfaces in the Tier-2 trace pass). The runtime §3.2
section additionally exercises **per-core independence** — writing one
core's slot leaves every other core's slot at its neutral value — the key
property the path-a `Vector` replacement delivers over the former scalar
fields. (The general same-field-cross-core lemma is deferred to SM5, where
genuine cross-core writes first occur; at single-core only `bootCoreId` is
written, so it is unused here.)
-/

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  Surface anchors (Tier-3): a rename/removal of any SM4.B foundation
--     symbol fails here at elaboration time.
-- ============================================================================

#check @SeLe4n.Model.SchedulerState.currentOnCore
#check @SeLe4n.Model.SchedulerState.runQueueOnCore
#check @SeLe4n.Model.SchedulerState.replenishQueueOnCore
#check @SeLe4n.Model.SchedulerState.activeDomainOnCore
#check @SeLe4n.Model.SchedulerState.domainTimeRemainingOnCore
#check @SeLe4n.Model.SchedulerState.domainScheduleIndexOnCore
#check @SeLe4n.Model.SchedulerState.lastTimeoutErrorsOnCore
#check @SeLe4n.Model.default_state_perCoreInitialized
#check @SeLe4n.Model.SchedulerState.ext_perCore

-- SM4.B.phase-2: the seven per-core setters (the path-a write API).
#check @SeLe4n.Model.SchedulerState.setCurrentOnCore
#check @SeLe4n.Model.SchedulerState.setRunQueueOnCore
#check @SeLe4n.Model.SchedulerState.setReplenishQueueOnCore
#check @SeLe4n.Model.SchedulerState.setActiveDomainOnCore
#check @SeLe4n.Model.SchedulerState.setDomainTimeRemainingOnCore
#check @SeLe4n.Model.SchedulerState.setDomainScheduleIndexOnCore
#check @SeLe4n.Model.SchedulerState.setLastTimeoutErrorsOnCore

-- SM4.B.phase-2: the `@[simp]` store/load algebra — the seven read-after-write
-- (`_self`) lemmas, a representative cross-field frame lemma, and a
-- system-wide-field frame lemma. These are what reduce post-write reads in
-- every downstream proof; a rename fails here at elaboration time.
#check @SeLe4n.Model.SchedulerState.setCurrentOnCore_currentOnCore_self
#check @SeLe4n.Model.SchedulerState.setRunQueueOnCore_runQueueOnCore_self
#check @SeLe4n.Model.SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_self
#check @SeLe4n.Model.SchedulerState.setActiveDomainOnCore_activeDomainOnCore_self
#check @SeLe4n.Model.SchedulerState.setDomainTimeRemainingOnCore_domainTimeRemainingOnCore_self
#check @SeLe4n.Model.SchedulerState.setDomainScheduleIndexOnCore_domainScheduleIndexOnCore_self
#check @SeLe4n.Model.SchedulerState.setLastTimeoutErrorsOnCore_lastTimeoutErrorsOnCore_self
#check @SeLe4n.Model.SchedulerState.setRunQueueOnCore_currentOnCore        -- cross-field frame
#check @SeLe4n.Model.SchedulerState.setRunQueueOnCore_domainSchedule        -- system-wide frame

-- ============================================================================
-- §2  Elaboration examples discharged through the proven SM4.B theorems.
-- ============================================================================

-- SM4.B.9: each conjunct of the default-init theorem, on an arbitrary core.
example (c : CoreId) : (default : SchedulerState).currentOnCore c = none :=
  (default_state_perCoreInitialized c).1
example (c : CoreId) :
    (default : SchedulerState).runQueueOnCore c = SeLe4n.Kernel.RunQueue.empty :=
  (default_state_perCoreInitialized c).2.1
example (c : CoreId) :
    (default : SchedulerState).replenishQueueOnCore c = SeLe4n.Kernel.ReplenishQueue.empty :=
  (default_state_perCoreInitialized c).2.2.1
example (c : CoreId) : (default : SchedulerState).activeDomainOnCore c = ⟨0⟩ :=
  (default_state_perCoreInitialized c).2.2.2.1
example (c : CoreId) : (default : SchedulerState).domainTimeRemainingOnCore c = 5 :=
  (default_state_perCoreInitialized c).2.2.2.2.1
example (c : CoreId) : (default : SchedulerState).domainScheduleIndexOnCore c = 0 :=
  (default_state_perCoreInitialized c).2.2.2.2.2.1
example (c : CoreId) : (default : SchedulerState).lastTimeoutErrorsOnCore c = [] :=
  (default_state_perCoreInitialized c).2.2.2.2.2.2

-- SM4.B.phase-2: each per-core accessor reads back a value written into its
-- own field at the same core (read-after-write at one core), via the seven
-- `_self` store/load lemmas.
example (c : CoreId) :
    ((default : SchedulerState).setCurrentOnCore c (some (SeLe4n.ThreadId.ofNat 1))).currentOnCore c
      = some (SeLe4n.ThreadId.ofNat 1) :=
  SchedulerState.setCurrentOnCore_currentOnCore_self _ c _
example (c : CoreId) (rq : SeLe4n.Kernel.RunQueue) :
    ((default : SchedulerState).setRunQueueOnCore c rq).runQueueOnCore c = rq :=
  SchedulerState.setRunQueueOnCore_runQueueOnCore_self _ c _
example (c : CoreId) (q : SeLe4n.Kernel.ReplenishQueue) :
    ((default : SchedulerState).setReplenishQueueOnCore c q).replenishQueueOnCore c = q :=
  SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_self _ c _
example (c : CoreId) (d : SeLe4n.DomainId) :
    ((default : SchedulerState).setActiveDomainOnCore c d).activeDomainOnCore c = d :=
  SchedulerState.setActiveDomainOnCore_activeDomainOnCore_self _ c _
example (c : CoreId) (n : Nat) :
    ((default : SchedulerState).setDomainTimeRemainingOnCore c n).domainTimeRemainingOnCore c = n :=
  SchedulerState.setDomainTimeRemainingOnCore_domainTimeRemainingOnCore_self _ c _
example (c : CoreId) (n : Nat) :
    ((default : SchedulerState).setDomainScheduleIndexOnCore c n).domainScheduleIndexOnCore c = n :=
  SchedulerState.setDomainScheduleIndexOnCore_domainScheduleIndexOnCore_self _ c _
example (c : CoreId) (es : List (SeLe4n.ThreadId × SeLe4n.Model.KernelError)) :
    ((default : SchedulerState).setLastTimeoutErrorsOnCore c es).lastTimeoutErrorsOnCore c = es :=
  SchedulerState.setLastTimeoutErrorsOnCore_lastTimeoutErrorsOnCore_self _ c _

-- SM4.B.phase-2: cross-field frame — writing `current` leaves `runQueue`
-- untouched at every core (the 42 cross-field lemmas; representative).
example (c c' : CoreId) (s : SchedulerState) (v : Option SeLe4n.ThreadId) :
    (s.setCurrentOnCore c v).runQueueOnCore c' = s.runQueueOnCore c' :=
  SchedulerState.setCurrentOnCore_runQueueOnCore _ c c' _

-- SM4.B.phase-2: system-wide frame — per-core writes never touch the shared
-- `domainSchedule` (the 14 system-wide-field lemmas; representative).
example (c : CoreId) (s : SchedulerState) (rq : SeLe4n.Kernel.RunQueue) :
    (s.setRunQueueOnCore c rq).domainSchedule = s.domainSchedule :=
  SchedulerState.setRunQueueOnCore_domainSchedule _ c _

-- SM4.B.10: per-core extensionality is usable — agreement at every core (and
-- on the system-wide fields) collapses two states to equal.
example : (default : SchedulerState) = (default : SchedulerState) :=
  SchedulerState.ext_perCore (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl

-- ============================================================================
-- §3  Runtime assertions (Tier-2): re-run every decidable check at runtime so
--     a silent regression surfaces in `lake exe per_core_scheduler_state_suite`.
-- ============================================================================

namespace SeLe4n.Testing.PerCoreSchedulerState

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then
    IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

/-- SM4.B.9 runtime mirror: every per-core read of the default state returns
    the neutral value on *every* core (`allCores`). -/
private def runDefaultInitChecks : IO Unit := do
  IO.println "--- §3.1 SM4.B.9 default-state per-core initialisation ---"
  assertBool "currentOnCore = none on every core"
    (allCores.all (fun c => decide ((default : SchedulerState).currentOnCore c = none)))
  assertBool "runQueueOnCore is empty (toList = []) on every core"
    (allCores.all (fun c => decide (((default : SchedulerState).runQueueOnCore c).toList = [])))
  assertBool "replenishQueueOnCore is empty (size = 0) on every core"
    (allCores.all (fun c => decide (((default : SchedulerState).replenishQueueOnCore c).size = 0)))
  assertBool "activeDomainOnCore = ⟨0⟩ on every core"
    (allCores.all (fun c => decide ((default : SchedulerState).activeDomainOnCore c = ⟨0⟩)))
  assertBool "domainTimeRemainingOnCore = 5 on every core"
    (allCores.all (fun c => decide ((default : SchedulerState).domainTimeRemainingOnCore c = 5)))
  assertBool "domainScheduleIndexOnCore = 0 on every core"
    (allCores.all (fun c => decide ((default : SchedulerState).domainScheduleIndexOnCore c = 0)))
  assertBool "lastTimeoutErrorsOnCore = [] on every core"
    (allCores.all (fun c => decide ((default : SchedulerState).lastTimeoutErrorsOnCore c = [])))

/-- SM4.B.8 runtime mirror: an accessor reads back a value written at the boot
    core, the write frames `runQueue`, and (per-core independence) the other
    cores' `current` stays at the neutral `none`. -/
private def runAccessorReadChecks : IO Unit := do
  IO.println "--- §3.2 SM4.B.8 accessor read-back ---"
  let s : SchedulerState := (default : SchedulerState).setCurrentOnCore bootCoreId (some (SeLe4n.ThreadId.ofNat 1))
  assertBool "currentOnCore reads the written value at the boot core"
    (decide (s.currentOnCore bootCoreId = some (SeLe4n.ThreadId.ofNat 1)))
  assertBool "writing current leaves runQueueOnCore empty (frame) on every core"
    (allCores.all (fun c => decide ((s.runQueueOnCore c).toList = [])))
  assertBool "per-core independence: a non-boot core's current is unchanged (none)"
    (allCores.all (fun c => decide (c = bootCoreId ∨ s.currentOnCore c = none)))

def runPerCoreSchedulerStateChecks : IO Unit := do
  IO.println "WS-SM SM4.B — Per-core SchedulerState accessor + theorem suite"
  IO.println "===================================="
  runDefaultInitChecks
  runAccessorReadChecks
  IO.println "===================================="
  IO.println "All SM4.B per-core SchedulerState foundation checks PASS."

end SeLe4n.Testing.PerCoreSchedulerState

def main : IO Unit :=
  SeLe4n.Testing.PerCoreSchedulerState.runPerCoreSchedulerStateChecks
