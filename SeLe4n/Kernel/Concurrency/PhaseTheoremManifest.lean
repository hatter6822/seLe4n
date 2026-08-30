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

import Lean.Elab.Command
import Lean.Meta.Basic
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

Unique *across the whole census*, not merely within its own inventory.  Each
inventory's `_identifiers_nodup` witness compares the identifier strings it
stores, in its own list, so it can see neither the same declaration registered
under two spellings nor the same declaration claimed by two phases.  The
census below de-duplicates on the *resolved* `Name` and errors on a repeat, so
the total cannot drift from a count of theorems into a count of
registrations.

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
  /-- **Entries** in those inventories — every registered declaration, whatever
      its type.  Proved equal to the inventories' `List.length` below. -/
  entryCount   : Nat
  /-- **Theorems** among those entries: the entries whose declaration type is a
      `Prop`.  This is the number `smpInventoriedTheoremCount` sums, and it is
      *not* `entryCount`: the inventories register a phase's whole surface, so
      209 of the 1111 entries are `def`s — lock-set footprints, per-core
      invariant predicates, WCRT cost functions — rather than proofs.  Checked
      against the environment by the census at the end of this module, which
      fails elaboration on drift; zero for every non-theorem kind. -/
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
      entryCount := 8,
      theoremCount := 0 },
    { phase := .rustHal,
      label := "SM1 — Rust HAL",
      kind := .unregistered,
      inventories := [],
      entryCount := 0,
      theoremCount := 0 },
    { phase := .verifiedLockPrimitives,
      label := "SM2 — verified lock primitives",
      kind := .theoremInventory,
      inventories := ["lockPrimitives"],
      entryCount := 22,
      theoremCount := 22 },
    { phase := .perObjectLocks,
      label := "SM3 — per-object locks",
      kind := .theoremInventory,
      inventories := ["perObjectLockTheorems", "lockSetTheorems",
                      "withLockSetTheorems", "deadlockTheorems",
                      "serializabilityTheorems"],
      entryCount := 409,
      theoremCount := 276 },
    { phase := .perCoreState,
      label := "SM4 — per-core state",
      kind := .assumptionLedger,
      inventories := ["smpRetiredInventory"],
      entryCount := 8,
      theoremCount := 0 },
    { phase := .perCoreScheduler,
      label := "SM5 — per-core scheduler",
      kind := .theoremInventory,
      inventories := ["crossCoreWakeTheorems", "perCoreTimerTheorems",
                      "perCoreIdleTheorems", "perCorePipTheorems",
                      "perCoreDomainTheorems", "perCoreCbsTheorems",
                      "perCoreInvariantSuiteTheorems", "perCoreWcrtTheorems"],
      entryCount := 680,
      theoremCount := 604 },
    { phase := .crossCoreIpc,
      label := "SM6 — cross-core IPC",
      kind := .unregistered,
      inventories := [],
      entryCount := 0,
      theoremCount := 0 },
    { phase := .tlbShootdown,
      label := "SM7 — TLB shootdown",
      kind := .unregistered,
      inventories := [],
      entryCount := 0,
      theoremCount := 0 },
    { phase := .informationFlow,
      label := "SM8 — information flow",
      kind := .unregistered,
      inventories := [],
      entryCount := 0,
      theoremCount := 0 },
    { phase := .declassification,
      label := "SM9 — declassification",
      kind := .unregistered,
      inventories := [],
      entryCount := 0,
      theoremCount := 0 },
    { phase := .releaseClosure,
      label := "SM10 — release closure",
      kind := .unregistered,
      inventories := [],
      entryCount := 0,
      theoremCount := 0 } ]

/-- The manifest entry registering `p`, if any. -/
def smpPhaseEntry? (p : SmpCompletionPhase) : Option PhaseTheoremEntry :=
  smpPhaseTheoremManifest.find? (fun e => e.phase == p)

/-- **Entries** `p` registers — every declaration in its inventories, whatever
    its type.  Zero for a phase whose inventories are an assumption ledger or
    absent. -/
def smpPhaseEntryCount (p : SmpCompletionPhase) : Nat :=
  match smpPhaseEntry? p with
  | some e => if e.kind == PhaseInventoryKind.theoremInventory then e.entryCount else 0
  | none   => 0

/-- **Theorems** `p` registers — the entries whose declaration type is a `Prop`.
    Zero for a phase whose inventories are an assumption ledger or absent. -/
def smpPhaseTheoremCount (p : SmpCompletionPhase) : Nat :=
  match smpPhaseEntry? p with
  | some e => if e.kind == PhaseInventoryKind.theoremInventory then e.theoremCount else 0
  | none   => 0

/-- Entries registered in a machine-checked inventory across every SMP
    completion phase — the sum of the per-phase entries, never a literal
    written beside them. -/
def smpInventoriedEntryCount : Nat :=
  (SmpCompletionPhase.all.map smpPhaseEntryCount).sum

/-- **Theorems** registered in a machine-checked inventory across every SMP
    completion phase: entries whose declaration type is a `Prop`.

    This is the number to quote.  `smpInventoriedEntryCount` counts the same
    inventories' *entries*, which is a larger and weaker figure — the
    inventories register a phase's surface, not only its proofs. -/
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

/-- SM2's registered **entry** count is the SM2.D.7 lock-primitive inventory's
    length.  Its theorem count coincides only because every `lockPrimitives`
    entry happens to be a proposition; the census below is what establishes
    that, not this theorem. -/
theorem smpPhase_verifiedLockPrimitives_entryCount_eq_inventories :
    smpPhaseEntryCount .verifiedLockPrimitives = lockPrimitives.length := by
  rw [lockPrimitives_count]
  decide

/-- SM3's registered **entry** count is the sum of its five SM3.A–E
    inventories' lengths.  Of those 409 entries, 276 are propositions. -/
theorem smpPhase_perObjectLocks_entryCount_eq_inventories :
    smpPhaseEntryCount .perObjectLocks
      = Model.perObjectLockTheorems.length + lockSetTheorems.length
        + withLockSetTheorems.length + deadlockTheorems.length
        + serializabilityTheorems.length := by
  rw [Model.perObjectLockTheorems_count, lockSetTheorems_count,
      withLockSetTheorems_count, deadlockTheorems_count,
      serializabilityTheorems_count]
  decide

/-- SM5's registered **entry** count is the sum of its eight SM5.C–J
    inventories' lengths.  Of those 680 entries, 604 are propositions. -/
theorem smpPhase_perCoreScheduler_entryCount_eq_inventories :
    smpPhaseEntryCount .perCoreScheduler
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
    `docs/WORKSTREAM_HISTORY.md` with closure target SM10.3.13. -/
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
theorem smp_inventoried_theorem_count : smpInventoriedTheoremCount = 902 := by
  decide

/-- Entries in the same inventories: 1111, of which 209 are `def`s rather than
    proofs.  Kept beside the theorem count so the gap is a number a reader can
    see, not a caveat they have to be told. -/
theorem smp_inventoried_entry_count : smpInventoriedEntryCount = 1111 := by
  decide

/-- The two differ, and by how much.  Stated so that collapsing them — quoting
    1111 as a theorem count, which this module did until `v0.34.27` — is a
    visible edit rather than a silent one. -/
theorem smp_inventoried_theorem_count_lt_entry_count :
    smpInventoriedTheoremCount + 209 = smpInventoriedEntryCount := by
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

/-- The same decomposition for entries. -/
theorem smp_inventoried_entry_count_decomposition :
    smpInventoriedEntryCount
      = smpPhaseEntryCount .verifiedLockPrimitives
        + smpPhaseEntryCount .perObjectLocks
        + smpPhaseEntryCount .perCoreScheduler := by
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

/-! ## The propositionality census — what makes `theoremCount` a theorem count

`entryCount` is proved from `List.length`, which counts *registrations*.  It
cannot distinguish a proof from a definition, and the inventories deliberately
register both: `crossCoreWakeTheorems` carries `wakeThreadLockSet` and
`determineTargetCore`, `perCoreCbsTheorems` carries `replenishOnCore` and
`migrateSchedContextReplenishment`, and so on — 209 such entries across the
fourteen inventories.  Every inventory's construction macro resolves its
identifier (`let _ := @$ident`) and so proves the name exists; **none** checks
that its type is a `Prop`.

So a `List.length` is the wrong witness for a claim about theorems, and until
`v0.34.27` this module made exactly that mistake: it published 1111 as a
theorem total.  The census below is the right one.  It resolves every
registered identifier against the environment, requires the resolution to be
**unambiguous**, and counts those whose type is a proposition — then compares
the result with each manifest entry's `theoremCount` and fails elaboration on
any disagreement.  A gate that guessed which constant an ambiguous name meant
would be a gate that lies, so ambiguity is an error rather than a coin flip.

This has to be a command elaborator rather than a theorem: propositionality is
a fact about the *environment*, not about a value, so no `decide` can see it.
That is also why the Python gate cannot check it — `generate_smp_theorem_manifest.py`
reads text and has no elaborator — and why the two mechanisms are
complementary rather than redundant.
-/

section Census

open Lean Elab Command Meta

/-- The inventory names the census measures.

    A `String` in `PhaseTheoremEntry.inventories` cannot be dereferenced, so
    the bridge from a published name to the list it names has to be written
    once, by hand.  It is written **once**: this list supplies the names, and
    `censusPayloadOf` below is the sole place a name is paired with a payload.
    `censusInventories` is then *derived*, so there is no second site at which
    a label and a list could be paired inconsistently. -/
private def censusInventoryNames : List String :=
  [ "perObjectLockTheorems", "lockSetTheorems", "withLockSetTheorems"
  , "deadlockTheorems", "serializabilityTheorems", "lockPrimitives"
  , "crossCoreWakeTheorems", "perCoreTimerTheorems", "perCoreIdleTheorems"
  , "perCorePipTheorems", "perCoreDomainTheorems", "perCoreCbsTheorems"
  , "perCoreInvariantSuiteTheorems", "perCoreWcrtTheorems" ]

/-- The one place a published inventory name is bound to a namespace and to
    the identifiers of the list it names.

    Every arm spells the name twice — once as the `String` the manifest
    publishes, once as the constant whose identifiers it returns — on a single
    line, so the two are checkable by eye.  Nothing else in this module pairs a
    name with a payload, which is what removes the swap class outright: there
    is no second tuple to disagree with.  The namespace is not taken on trust
    either; `censusNamespacesResolve` below holds each arm's namespace to the
    environment by requiring `ns ++ name` to be the constant that arm returns
    the identifiers of. -/
private def censusPayloadOf (n : String) : Option (Name × List String) :=
  match n with
  | "perObjectLockTheorems" =>
      some (`SeLe4n.Model, SeLe4n.Model.perObjectLockTheorems.map (·.identifier))
  | "lockSetTheorems" =>
      some (`SeLe4n.Kernel.Concurrency, lockSetTheorems.map (·.identifier))
  | "withLockSetTheorems" =>
      some (`SeLe4n.Kernel.Concurrency, withLockSetTheorems.map (·.identifier))
  | "deadlockTheorems" =>
      some (`SeLe4n.Kernel.Concurrency, deadlockTheorems.map (·.identifier))
  | "serializabilityTheorems" =>
      some (`SeLe4n.Kernel.Concurrency, serializabilityTheorems.map (·.identifier))
  | "lockPrimitives" =>
      some (`SeLe4n.Kernel.Concurrency, lockPrimitives.map (·.identifier.toString))
  | "crossCoreWakeTheorems" =>
      some (`SeLe4n.Kernel, SeLe4n.Kernel.crossCoreWakeTheorems.map (·.identifier))
  | "perCoreTimerTheorems" =>
      some (`SeLe4n.Kernel, SeLe4n.Kernel.perCoreTimerTheorems.map (·.identifier))
  | "perCoreIdleTheorems" =>
      some (`SeLe4n.Kernel, SeLe4n.Kernel.perCoreIdleTheorems.map (·.identifier))
  | "perCorePipTheorems" =>
      some (`SeLe4n.Kernel.PriorityInheritance,
        SeLe4n.Kernel.PriorityInheritance.perCorePipTheorems.map (·.identifier))
  | "perCoreDomainTheorems" =>
      some (`SeLe4n.Kernel, SeLe4n.Kernel.perCoreDomainTheorems.map (·.identifier))
  | "perCoreCbsTheorems" =>
      some (`SeLe4n.Kernel, SeLe4n.Kernel.perCoreCbsTheorems.map (·.identifier))
  | "perCoreInvariantSuiteTheorems" =>
      some (`SeLe4n.Kernel, SeLe4n.Kernel.perCoreInvariantSuiteTheorems.map (·.identifier))
  | "perCoreWcrtTheorems" =>
      some (`SeLe4n.Kernel, SeLe4n.Kernel.perCoreWcrtTheorems.map (·.identifier))
  | _ => none

/-- Every inventory the manifest names, paired with its entries' identifiers.

    Derived, never written: each name carries whatever `censusPayloadOf`
    returns for it. -/
private def censusInventories : List (String × Name × List String) :=
  censusInventoryNames.filterMap
    (fun n => (censusPayloadOf n).map (fun p => (n, p.1, p.2)))

/-- The census measures exactly the inventories the `theoremInventory` phases
    claim — neither more nor fewer.  Adding an inventory to a phase without
    adding it here (or the reverse) fails this proof, so the census cannot
    quietly measure a different set than the manifest publishes. -/
theorem censusCoversManifest :
    (censusInventories.map (·.1)).length
      = ((smpPhaseTheoremManifest.filter
            (fun e => e.kind == PhaseInventoryKind.theoremInventory)).flatMap
              (·.inventories)).length
    ∧ (censusInventories.map (·.1)).all
        (fun n => ((smpPhaseTheoremManifest.filter
            (fun e => e.kind == PhaseInventoryKind.theoremInventory)).flatMap
              (·.inventories)).contains n) := by
  decide

/-- The census names are pairwise distinct.

    Length-plus-membership is a statement about the *set* of names, and a set
    is blind to a permutation: exchanging two entries' labels leaves it
    satisfied.  Uniqueness is the half that makes the label a key at all —
    without it `propsOf` could find a name twice and the first match would
    silently decide which payload a phase was credited with. -/
theorem censusInventoryNamesNodup :
    (censusInventories.map (·.1)).Nodup := by
  decide

/-- **No published name is silently unmeasured.**

    `censusInventories` is a `filterMap`, so a name `censusPayloadOf` has no
    arm for would be dropped rather than reported: the census would then
    measure thirteen inventories while the manifest published fourteen, and
    `censusCoversManifest` — which compares the *derived* list against the
    manifest — would fail with a length mismatch that reads as a manifest
    error rather than a missing arm.  Requiring the derivation to be total
    names the real fault at the real site. -/
theorem censusPayloadsAreTotal :
    censusInventories.length = censusInventoryNames.length := by
  decide

/-- The census names are pairwise distinct **as published**.

    `censusInventoryNamesNodup` states this of the derived list; a duplicate in
    `censusInventoryNames` would survive the derivation and be caught there
    too, but only after `filterMap` had already paired it with a payload
    twice.  Held at the source as well, so the diagnostic points at the list a
    reader edits. -/
theorem censusInventoryNamesSourceNodup :
    censusInventoryNames.Nodup := by
  decide

-- **The namespace is held to the environment, not asserted.**
--
-- Each arm of `censusPayloadOf` returns a namespace beside its payload, and
-- `censusResolve` searches from that namespace outward.  A wrong namespace is
-- therefore not inert: it changes which constant an identifier resolves to,
-- and a resolution that still succeeds from a wider prefix would leave the
-- error invisible.  The pairing is checkable because the namespace and the
-- name compose: `ns ++ name` must be the very constant whose identifiers that
-- arm returns.  Checking that it *exists* is what makes the namespace field
-- evidence rather than a restatement -- a swapped or stale namespace names no
-- constant and fails this module's elaboration.
private def censusNamespacesResolve : MetaM Unit := do
  let env ← getEnv
  for (nm, ns, _) in censusInventories do
    let full := ns ++ nm.toName
    if !(env.contains full) then
      throwError "census namespace check: inventory '{nm}' is registered under \
        namespace {ns}, but {full} names no constant -- the namespace and the \
        payload beside it disagree"

run_cmd liftTermElabM censusNamespacesResolve

/-- Does `n` end with every component of `want`?

    The inventories store identifiers at varying qualification — bare
    (`wakeThreadLockSet`), partly qualified (`TCB.lock`), or fully
    (`SeLe4n.Kernel.schedulerInvariantStructural_perCore`).  Matching on the
    final component alone makes `TCB.lock` ambiguous across ten structures, so
    the whole stored suffix has to match. -/
private def censusNameMatches (want n : Name) : Bool :=
  let wc := want.components
  let nc := n.components
  wc.length ≤ nc.length && (nc.drop (nc.length - wc.length)) == wc

/-- Resolve an inventory identifier to the unique `SeLe4n.*` constant it names,
    returning that constant's full name alongside whether its type is a
    proposition.

    The resolved name, not the stored string, is what the census de-duplicates
    on.  One declaration can be registered under two spellings
    (`wakeThreadLockSet` and `SeLe4n.Kernel.wakeThreadLockSet`) or in two
    inventories, and each inventory's `_identifiers_nodup` witness compares
    only its own strings, within its own list -- so neither spelling nor scope
    is enough to see a repeat.

    Ambiguity and absence are both hard errors: the census exists to make a
    number trustworthy, and a resolver that picked a winner among candidates
    would defeat that. -/
private def censusResolve (idx : Std.HashMap String (List Name)) (ns : Name)
    (ident : String) : MetaM (Name × Bool) := do
  let env ← getEnv
  let want := ident.toName
  -- Lean's own resolution order: the enclosing namespace first, then each
  -- shorter prefix, then the root.  `waitGraph` inside
  -- `SeLe4n.Kernel.Concurrency` is that namespace's `def`, not the
  -- `DeadlockCategory.waitGraph` constructor that shares its final component —
  -- suffix search alone cannot tell those apart and must not try.
  -- The prefix chain, longest first, ending at the root (`Name.anonymous ++ n`
  -- is `n`).  Built by `take` rather than by recursing on `getPrefix`, which
  -- Lean cannot see as decreasing.
  let cs := ns.components
  let prefixes : List Name :=
    ((List.range (cs.length + 1)).map
      (fun k => (cs.take k).foldl (· ++ ·) Name.anonymous)).reverse
  match prefixes.findSome? (fun p => env.find? (p ++ want)) with
  | some c => return (c.name, ← isProp c.type)
  | none =>
    -- Fallback for an identifier stored at a qualification the walk cannot
    -- reach.  Ambiguity here is a hard error: a resolver that picked a winner
    -- would defeat the census.
    match (idx.getD want.getString! []).filter (censusNameMatches want) with
    | [n] =>
      match env.find? n with
      | none   => throwError "propositionality census: '{ident}' has no declaration"
      | some c => return (c.name, ← isProp c.type)
    | []  => throwError "propositionality census: '{ident}' resolves to no SeLe4n \
               constant (searched from namespace {ns})"
    | cs  => throwError "propositionality census: '{ident}' is ambiguous ({cs})"

/-- Index every `SeLe4n.*` constant by its final name component. -/
private def censusIndex : MetaM (Std.HashMap String (List Name)) := do
  let env ← getEnv
  let mut m : Std.HashMap String (List Name) := {}
  for (n, _) in env.constants.toList do
    if n.isInternal then continue
    if (`SeLe4n).isPrefixOf n then
      let k := n.getString!
      m := m.insert k ((m.getD k []) ++ [n])
  return m

-- **The check.**  Fails this module's elaboration when the propositions the
-- environment actually holds disagree with any phase's declared
-- `theoremCount`, or with the module-level total.
run_cmd liftTermElabM do
  let idx ← censusIndex
  let mut perInventory : List (String × Nat) := []
  -- Every registration across the whole census must name a *distinct*
  -- declaration.  One theorem registered twice -- in two inventories, or under
  -- two spellings in one -- would be counted twice, and the published total
  -- would quietly become a count of registrations rather than of theorems.
  -- That is exactly the failure this module was built to make impossible, so
  -- it is a hard error rather than a deduplication.
  let mut seen : Std.HashMap Name String := {}
  for (nm, ns, ids) in censusInventories do
    let mut props := 0
    for i in ids do
      let (resolved, isProposition) ← censusResolve idx ns i
      match seen.get? resolved with
      | some origin =>
        throwError "propositionality census: '{i}' in {nm} resolves to \
          {resolved}, already registered as {origin} -- one declaration, two \
          registrations, so the total would count it twice"
      | none => seen := seen.insert resolved s!"'{i}' in {nm}"
      if isProposition then props := props + 1
    perInventory := perInventory ++ [(nm, props)]
  let propsOf (names : List String) : Nat :=
    names.foldl (fun acc n => acc + ((perInventory.find? (·.1 == n)).map (·.2)).getD 0) 0
  let mut total := 0
  for e in smpPhaseTheoremManifest do
    if e.kind == PhaseInventoryKind.theoremInventory then
      let measured := propsOf e.inventories
      if measured != e.theoremCount then
        throwError "propositionality census: phase {e.label} declares theoremCount = \
          {e.theoremCount}, the environment holds {measured} propositions across \
          {e.inventories}"
      total := total + measured
    else if e.theoremCount != 0 then
      throwError "propositionality census: phase {e.label} is not a theoremInventory \
        yet declares theoremCount = {e.theoremCount}"
  if total != smpInventoriedTheoremCount then
    throwError "propositionality census: the per-phase propositions sum to {total}, \
      but smpInventoriedTheoremCount is {smpInventoriedTheoremCount}"

end Census

end SeLe4n.Kernel.Concurrency
