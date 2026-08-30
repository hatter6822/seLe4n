-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM SM10 (the release-closure theorem marker;
-- landed early by WS-RR RR0.6, which replaces the hand-summed literal
-- the marker would otherwise have certified).

import SeLe4n.Model.Object.PerObjectLockInventory
import SeLe4n.Kernel.Concurrency.Assumptions
import SeLe4n.Kernel.Concurrency.LockPrimitives
import SeLe4n.Kernel.Concurrency.Locks.LockSetInventory
import SeLe4n.Kernel.Concurrency.Locks.WithLockSetInventory
import SeLe4n.Kernel.Concurrency.Locks.DeadlockInventory
import SeLe4n.Kernel.Concurrency.Locks.SerializabilityInventory
import SeLe4n.Kernel.Scheduler.Operations.CrossCoreWakeInventory
import SeLe4n.Kernel.Scheduler.Operations.PerCoreTimerInventory
import SeLe4n.Kernel.Scheduler.Operations.PerCoreIdleInventory
import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCoreInventory
import SeLe4n.Kernel.Scheduler.Operations.PerCoreDomainInventory
import SeLe4n.Kernel.Scheduler.Operations.PerCoreCbsInventory
import SeLe4n.Kernel.Scheduler.Invariant.PerCoreInvariantSuiteInventory
import SeLe4n.Kernel.Scheduler.Operations.PerCoreWcrtInventory

/-!
# SMP completion-phase theorem manifest (WS-RR RR0.6; consumed by WS-SM SM10)

The release-closure plan carried its theorem total as a hand-summed literal:

> 16 SM0 + 1 SM1 + 22 SM2 + 28 SM3 + ~50 SM4 + 30 SM5 + 25 SM6 + 14 SM7
> + 18 SM8 + 5 SM10 = 209 ≈ 210

That sum runs SM8 → SM10 with **no SM9 term**, though SM9 is a landed phase
(CLOSED v0.33.100) whose surface carries hundreds of theorems.  The marker
theorem and the "verify all 210 SM theorems land at HEAD" gate would both have
certified a number computed as if a whole phase never happened — and nothing
would have broken when it did, because a hand-sum cannot detect its own
staleness.

This module replaces the sum with a **measurement**, and pins the measurement
three ways:

1. **Per-phase counts are derived, not asserted.**  Each entry's
   `theoremCount` is proved equal to the sum of the real inventory lengths
   (`…_theoremCount_eq_inventories` below), so an inventory that grows,
   shrinks, or is renamed fails this module's elaboration rather than
   silently invalidating a literal.
2. **The phase set is total.**  `SmpCompletionPhase` enumerates all eleven
   phases and `smpPhaseTheoremManifest_covers_all` proves every one of them
   has an entry.  Adding a phase without registering it does not compile —
   the SM9 shape is unrepresentable.
3. **No inventory may go unclaimed.**
   `scripts/generate_smp_theorem_manifest.py --check` (Tier 0) discovers every
   theorem inventory in the tree from its `_identifiers_nodup` witness, over
   the comment-free code view, and fails when one is claimed by no phase,
   claimed twice, or claimed with a count the tree does not measure.  Lean
   cannot see that failure on its own: a manifest that never mentions an
   inventory elaborates perfectly.

## What the number counts

`smpInventoriedTheoremCount` is the number of theorems registered in a
machine-checked inventory — a list of theorem identifiers, each resolved at
elaboration time by its inventory's construction macro, carrying a
duplicate-free witness and a size witness.  It is a *measurement of the tree*,
not an estimate of what a phase "substantively" proved, and it is deliberately
the narrower claim: every theorem it counts is named, resolves, and is unique.

Phases with no inventory contribute **zero** and are registered as
`unregistered` rather than given a plausible-looking figure.  That gap is real
and is registered as such in `docs/WORKSTREAM_HISTORY.md`; the honest zero is
what makes it visible.  Assumption ledgers (`smpLatentInventory`,
`smpRetiredInventory`) enumerate assumptions rather than proved theorems, so
they are claimed — an unclaimed inventory is a gate failure — under
`assumptionLedger`, and contribute nothing to the total.

## Naming

The phases are named for what they are (`perCoreScheduler`, `crossCoreIpc`,
…) rather than by their phase codes.  Phase codes are commit-time labels that
age out with the workstream, and CLAUDE.md's internal-first naming rule
forbids them in identifiers; the code is carried in each entry's `label`,
which is data.
-/

namespace SeLe4n.Kernel.Concurrency

/-- The eleven phases of the SMP multi-core completion workstream, named for
    what each one delivers.  Totality of this inductive is what makes an
    omitted phase impossible: `smpPhaseTheoremManifest_covers_all` quantifies
    over `all`, so a new constructor fails elaboration until it is
    registered. -/
inductive SmpCompletionPhase where
  /-- SM0 — foundational types, honesty patches, the lock hierarchy. -/
  | foundations
  /-- SM1 — Rust HAL: PSCI, per-CPU, secondary init, TLBI, SGI, QEMU. -/
  | rustHal
  /-- SM2 — memory model, TicketLock, RwLock, FFI bridge, refinement. -/
  | verifiedLockPrimitives
  /-- SM3 — per-object locks, lock sets, 2PL, deadlock-freedom, serializability. -/
  | perObjectLocks
  /-- SM4 — per-core `Vector` state, scheduler state, register banks. -/
  | perCoreState
  /-- SM5 — per-core scheduler: selection, switch, wake, timer, idle, PIP, CBS. -/
  | perCoreScheduler
  /-- SM6 — cross-core IPC: call, notification, reply, cancellation. -/
  | crossCoreIpc
  /-- SM7 — TLB shootdown protocol, per-core TLB model, cache maintenance. -/
  | tlbShootdown
  /-- SM8 — per-core observable state, non-interference, fine-lock flow. -/
  | informationFlow
  /-- SM9 — declassification completion: audit reader, refusal auditing, provenance. -/
  | declassification
  /-- SM10 — release closure: the boot path, documentation, tests, the v1.0.0 tag. -/
  | releaseClosure
  deriving Repr, DecidableEq, Inhabited

/-- Every phase, in execution order. -/
def SmpCompletionPhase.all : List SmpCompletionPhase :=
  [ .foundations, .rustHal, .verifiedLockPrimitives, .perObjectLocks,
    .perCoreState, .perCoreScheduler, .crossCoreIpc, .tlbShootdown,
    .informationFlow, .declassification, .releaseClosure ]

/-- `all` is exhaustive: adding a constructor without extending `all` fails
    this proof. -/
theorem SmpCompletionPhase.mem_all (p : SmpCompletionPhase) :
    p ∈ SmpCompletionPhase.all := by
  cases p <;> decide

/-- `all` lists no phase twice, so a per-phase count cannot be double-counted. -/
theorem SmpCompletionPhase.all_nodup : SmpCompletionPhase.all.Nodup := by decide

/-- WS-SM has eleven phases, SM0..SM10 inclusive.  The release-closure plan's
    marker list said ten; SM0 is a phase, and the manifest counts it. -/
theorem SmpCompletionPhase.all_length : SmpCompletionPhase.all.length = 11 := by decide

/-- What a phase's registered inventories are. -/
inductive PhaseInventoryKind where
  /-- Lists of theorem identifiers; these are what the total counts. -/
  | theoremInventory
  /-- Ledgers of assumptions (latent, retired).  Registered so they cannot go
      unclaimed, but they enumerate assumptions rather than proved theorems and
      contribute nothing to the theorem total. -/
  | assumptionLedger
  /-- The phase has no machine-checked theorem inventory yet.  A registered
      gap, not an estimate: see the debt row in `docs/WORKSTREAM_HISTORY.md`. -/
  | unregistered
  deriving Repr, DecidableEq, Inhabited

/-- One phase's registered theorem inventories.

    `inventories` names the Lean inventory definitions by their unqualified
    identifier — the same strings
    `scripts/generate_smp_theorem_manifest.py` discovers in the tree, so the
    two sides can be compared without either inventing a name.  Each entry's
    `theoremCount` is *proved* equal to those inventories' lengths below. -/
structure PhaseTheoremEntry where
  /-- The phase this entry registers. -/
  phase        : SmpCompletionPhase
  /-- Human-readable label carrying the phase code (data, not an identifier). -/
  label        : String
  /-- Whether these inventories are theorem lists, assumption ledgers, or absent. -/
  kind         : PhaseInventoryKind
  /-- Unqualified names of the phase's inventory definitions. -/
  inventories  : List String
  /-- Theorems registered by those inventories; zero for every non-theorem kind. -/
  theoremCount : Nat
  deriving Repr, Inhabited

/-- The manifest: exactly one entry per SMP completion phase.

    Regenerate the JSON side with
    `python3 scripts/generate_smp_theorem_manifest.py --write`; Tier 0 fails
    when this list and the tree disagree. -/
def smpPhaseTheoremManifest : List PhaseTheoremEntry :=
  [ { phase := .foundations,
      label := "SM0 — foundations",
      kind := .assumptionLedger,
      inventories := ["smpLatentInventory"],
      theoremCount := 0 },
    { phase := .rustHal,
      label := "SM1 — Rust HAL",
      kind := .unregistered,
      inventories := [],
      theoremCount := 0 },
    { phase := .verifiedLockPrimitives,
      label := "SM2 — verified lock primitives",
      kind := .theoremInventory,
      inventories := ["lockPrimitives"],
      theoremCount := 22 },
    { phase := .perObjectLocks,
      label := "SM3 — per-object locks",
      kind := .theoremInventory,
      inventories := ["perObjectLockTheorems", "lockSetTheorems",
                      "withLockSetTheorems", "deadlockTheorems",
                      "serializabilityTheorems"],
      theoremCount := 409 },
    { phase := .perCoreState,
      label := "SM4 — per-core state",
      kind := .assumptionLedger,
      inventories := ["smpRetiredInventory"],
      theoremCount := 0 },
    { phase := .perCoreScheduler,
      label := "SM5 — per-core scheduler",
      kind := .theoremInventory,
      inventories := ["crossCoreWakeTheorems", "perCoreTimerTheorems",
                      "perCoreIdleTheorems", "perCorePipTheorems",
                      "perCoreDomainTheorems", "perCoreCbsTheorems",
                      "perCoreInvariantSuiteTheorems", "perCoreWcrtTheorems"],
      theoremCount := 680 },
    { phase := .crossCoreIpc,
      label := "SM6 — cross-core IPC",
      kind := .unregistered,
      inventories := [],
      theoremCount := 0 },
    { phase := .tlbShootdown,
      label := "SM7 — TLB shootdown",
      kind := .unregistered,
      inventories := [],
      theoremCount := 0 },
    { phase := .informationFlow,
      label := "SM8 — information flow",
      kind := .unregistered,
      inventories := [],
      theoremCount := 0 },
    { phase := .declassification,
      label := "SM9 — declassification",
      kind := .unregistered,
      inventories := [],
      theoremCount := 0 },
    { phase := .releaseClosure,
      label := "SM10 — release closure",
      kind := .unregistered,
      inventories := [],
      theoremCount := 0 } ]

/-- The manifest entry registering `p`, if any. -/
def smpPhaseEntry? (p : SmpCompletionPhase) : Option PhaseTheoremEntry :=
  smpPhaseTheoremManifest.find? (fun e => e.phase == p)

/-- Theorems `p` registers.  Zero for a phase whose inventories are an
    assumption ledger or absent. -/
def smpPhaseTheoremCount (p : SmpCompletionPhase) : Nat :=
  match smpPhaseEntry? p with
  | some e => if e.kind == PhaseInventoryKind.theoremInventory then e.theoremCount else 0
  | none   => 0

/-- Theorems registered in a machine-checked inventory across every SMP
    completion phase — the sum of the per-phase entries, never a literal
    written beside them. -/
def smpInventoriedTheoremCount : Nat :=
  (SmpCompletionPhase.all.map smpPhaseTheoremCount).sum

/-! ## Completeness — no phase can be omitted

The defect this module exists to close was a *missing term*, not a wrong one.
These three witnesses make the omission unrepresentable: every phase has an
entry, no phase has two, and the manifest is exactly as long as the phase
enumeration. -/

/-- Every SMP completion phase has a manifest entry. -/
theorem smpPhaseTheoremManifest_covers_all :
    SmpCompletionPhase.all.all (fun p => (smpPhaseEntry? p).isSome) := by decide

/-- Every phase has an entry, in `∀` form. -/
theorem smpPhaseTheoremManifest_covers (p : SmpCompletionPhase) :
    (smpPhaseEntry? p).isSome := by
  cases p <;> decide

/-- No phase is registered twice, so no phase's theorems are double-counted. -/
theorem smpPhaseTheoremManifest_phases_nodup :
    (smpPhaseTheoremManifest.map (·.phase)).Nodup := by decide

/-- One entry per phase: the manifest length matches the phase enumeration. -/
theorem smpPhaseTheoremManifest_length :
    smpPhaseTheoremManifest.length = SmpCompletionPhase.all.length := by decide

/-! ## Derivation — no count can go stale

Each theorem below ties a manifest entry's declared `theoremCount` to the
*actual lengths* of the inventories it names, through those inventories' own
size witnesses.  An inventory that gains or loses an entry changes its
`…_count` witness, which changes the right-hand side here, which fails this
module.  That is what makes the manifest a measurement rather than a copy. -/

/-- SM2's registered count is the SM2.D.7 lock-primitive inventory's length. -/
theorem smpPhase_verifiedLockPrimitives_theoremCount_eq_inventories :
    smpPhaseTheoremCount .verifiedLockPrimitives = lockPrimitives.length := by
  rw [lockPrimitives_count]
  decide

/-- SM3's registered count is the sum of its five SM3.A–E inventories. -/
theorem smpPhase_perObjectLocks_theoremCount_eq_inventories :
    smpPhaseTheoremCount .perObjectLocks
      = Model.perObjectLockTheorems.length + lockSetTheorems.length
        + withLockSetTheorems.length + deadlockTheorems.length
        + serializabilityTheorems.length := by
  rw [Model.perObjectLockTheorems_count, lockSetTheorems_count,
      withLockSetTheorems_count, deadlockTheorems_count,
      serializabilityTheorems_count]
  decide

/-- SM5's registered count is the sum of its eight SM5.C–J inventories. -/
theorem smpPhase_perCoreScheduler_theoremCount_eq_inventories :
    smpPhaseTheoremCount .perCoreScheduler
      = crossCoreWakeTheorems.length + perCoreTimerTheorems.length
        + perCoreIdleTheorems.length + PriorityInheritance.perCorePipTheorems.length
        + perCoreDomainTheorems.length + perCoreCbsTheorems.length
        + perCoreInvariantSuiteTheorems.length + perCoreWcrtTheorems.length := by
  rw [crossCoreWakeTheorems_count, perCoreTimerTheorems_count,
      perCoreIdleTheorems_count, PriorityInheritance.perCorePipTheorems_count,
      perCoreDomainTheorems_count, perCoreCbsTheorems_count,
      perCoreInvariantSuiteTheorems_count, perCoreWcrtTheorems_count]
  decide

/-- SM0's ledger is an assumption ledger, so it contributes nothing to the
    theorem total even though its eight entries are registered. -/
theorem smpPhase_foundations_theoremCount_zero :
    smpPhaseTheoremCount .foundations = 0 := by decide

/-- SM4's ledger is likewise an assumption ledger. -/
theorem smpPhase_perCoreState_theoremCount_zero :
    smpPhaseTheoremCount .perCoreState = 0 := by decide

/-- The six phases with no machine-checked theorem inventory contribute zero
    — an honest gap rather than an estimate.  Registered as debt in
    `docs/WORKSTREAM_HISTORY.md` with closure target SM10.B.13. -/
theorem smpPhase_unregistered_theoremCount_zero :
    smpPhaseTheoremCount .rustHal = 0
    ∧ smpPhaseTheoremCount .crossCoreIpc = 0
    ∧ smpPhaseTheoremCount .tlbShootdown = 0
    ∧ smpPhaseTheoremCount .informationFlow = 0
    ∧ smpPhaseTheoremCount .declassification = 0
    ∧ smpPhaseTheoremCount .releaseClosure = 0 := by decide

/-! ## The marker theorem

`smp_inventoried_theorem_count` is the SM10 marker the release-closure plan
listed as `wsm_theorem_count`.  Renamed on landing per CLAUDE.md's
internal-first naming rule (a workstream ID is not a description), and
restated as a sum over the manifest rather than a per-phase hand-sum: this
number cannot be edited into agreement with a stale belief, because nothing
here is written twice. -/

/-- Theorems registered in a machine-checked inventory across SM0..SM10.

    Derived: `(SmpCompletionPhase.all.map smpPhaseTheoremCount).sum`, whose
    summands are each pinned to a real inventory length above.  Changing any
    inventory changes this number, and the Tier-0 gate fails until the
    manifest and `docs/smp_theorem_manifest.json` agree with the tree. -/
theorem smp_inventoried_theorem_count : smpInventoriedTheoremCount = 1111 := by
  decide

/-- The total is the sum of the two phases that carry inventories today.
    Stated separately from the numeral so a reader can see where the number
    comes from without unfolding the manifest. -/
theorem smp_inventoried_theorem_count_decomposition :
    smpInventoriedTheoremCount
      = smpPhaseTheoremCount .verifiedLockPrimitives
        + smpPhaseTheoremCount .perObjectLocks
        + smpPhaseTheoremCount .perCoreScheduler := by
  decide

/-! ## Build anchor

Every inventory the manifest names is `@`-referenced here, so a rename or a
deletion fails elaboration rather than leaving a dangling string in
`inventories`.  The `String` entries above are data — Lean does not check
that a string resolves — which is exactly the gap this anchor closes on the
Lean side and `generate_smp_theorem_manifest.py` closes on the tree side.

Sixteen inventories: fourteen theorem inventories plus the two assumption
ledgers, each with its size witness. -/
example : True := by
  let _ := @Model.perObjectLockTheorems
  let _ := @Model.perObjectLockTheorems_count
  let _ := @lockSetTheorems
  let _ := @lockSetTheorems_count
  let _ := @withLockSetTheorems
  let _ := @withLockSetTheorems_count
  let _ := @deadlockTheorems
  let _ := @deadlockTheorems_count
  let _ := @serializabilityTheorems
  let _ := @serializabilityTheorems_count
  let _ := @lockPrimitives
  let _ := @lockPrimitives_count
  let _ := @crossCoreWakeTheorems
  let _ := @crossCoreWakeTheorems_count
  let _ := @perCoreTimerTheorems
  let _ := @perCoreTimerTheorems_count
  let _ := @perCoreIdleTheorems
  let _ := @perCoreIdleTheorems_count
  let _ := @PriorityInheritance.perCorePipTheorems
  let _ := @PriorityInheritance.perCorePipTheorems_count
  let _ := @perCoreDomainTheorems
  let _ := @perCoreDomainTheorems_count
  let _ := @perCoreCbsTheorems
  let _ := @perCoreCbsTheorems_count
  let _ := @perCoreInvariantSuiteTheorems
  let _ := @perCoreInvariantSuiteTheorems_count
  let _ := @perCoreWcrtTheorems
  let _ := @perCoreWcrtTheorems_count
  let _ := @smpLatentInventory
  let _ := @smpLatentInventory_count
  let _ := @smpRetiredInventory
  let _ := @smpRetiredInventory_count
  trivial

end SeLe4n.Kernel.Concurrency
