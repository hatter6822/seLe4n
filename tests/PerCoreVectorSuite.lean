-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Prelude
import SeLe4n.Kernel.Concurrency.Types
import SeLe4n.Platform.RPi5.Contract
import SeLe4n.Platform.Sim.Contract

/-!
# WS-SM SM4.A — Per-core `Vector` bootstrap test suite

Tier-2 (runtime) + Tier-3 (surface anchor) coverage for WS-SM Phase
SM4.A "Vector + PlatformBinding".  Covers all eight sub-tasks:

* **SM4.A.1 / SM4.A.2** — the per-core `Vector` bootstrap in
  `Prelude.lean` (`namespace SeLe4n.Vector`): the `get_eq_getElem`
  bridge plus the six helper theorems `get_set_eq`, `get_set_ne`,
  `length`, `replicate_get`, `ext`, `nodup_of_finRange`.  Each is
  exercised both at elaboration time (`#check` + `by decide`/`rfl`
  examples) and at runtime (`assertBool` mirrors so a silent
  regression surfaces in `lake exe per_core_vector_suite`).
* **SM4.A.3** — runtime efficiency: Lean core's `Vector α n` is
  `Array`-backed (`structure Vector where toArray : Array α`) and its
  `get`/`set`/`replicate` are `@[inline, expose]`, so they compile to
  the underlying O(1) `Array` operations.  The runtime block observes
  the `Array` backing (`toArray.size`, `toArray = Array.replicate …`)
  and a deep index (`get` at slot 255 of a 256-wide vector) computing
  correctly — the executable running at all witnesses computability.
  (The full `lake exe sele4n` per-core-access trace lands with
  SM4.B.15, once `SchedulerState` itself becomes `Vector`-shaped.)
* **SM4.A.4** — the RPi5 `PlatformBinding` exposes `coreCount = 4`,
  pinned to `Concurrency.numCores` by `numCores_eq_rpi5_coreCount`.
* **SM4.A.5** — both simulation topologies compile and carry the
  expected core counts: the new single-core sim
  (`SimSingleCorePlatform`, `coreCount = 1`) and the 4-core SMP sims
  (`SimPlatform` / `SimRestrictivePlatform`, `coreCount = 4`).
* **SM4.A.6 / SM4.A.7 / SM4.A.8** — recap anchors for the SM0.E/SM0.G
  deliverables `CoreId = Fin numCores`, `bootCoreId`, and `allCores`
  (`allCores_length`, `allCores_nodup`).  The recap ties the SM4.A.2
  `nodup_of_finRange` generalisation back to `allCores_nodup`: since
  `allCores = List.finRange numCores`, the new general lemma reproduces
  the literal-`4` `decide` proof, and also discharges the
  platform-parameterised `PlatformBinding.coreCount` form.

The suite is a runnable executable (`lake exe per_core_vector_suite`)
that re-runs every decidable check at runtime, so the assertions surface
in the `run` output if they ever silently regress.
-/

open SeLe4n.Kernel.Concurrency
open SeLe4n.Platform
open SeLe4n.Platform.RPi5
open SeLe4n.Platform.Sim

-- ============================================================================
-- §1 — Surface anchors: every SM4.A public symbol resolves at elaboration
-- ============================================================================

/-! ## SM4.A.1 / SM4.A.2 / SM4.A.3 — Per-core `Vector` helpers -/
#check @SeLe4n.Vector.get_eq_getElem
#check @SeLe4n.Vector.get_eq_toArray_getElem
#check @SeLe4n.Vector.get_set_eq
#check @SeLe4n.Vector.get_set_ne
#check @SeLe4n.Vector.toList_length
#check @SeLe4n.Vector.replicate_get
#check @SeLe4n.Vector.ext
#check @SeLe4n.Vector.nodup_of_finRange

/-! ## SM4.A.4 — RPi5 PlatformBinding core count + pinning -/
#check @SeLe4n.Platform.PlatformBinding.coreCount
#check @SeLe4n.Platform.PlatformBinding.bootCoreId
#check @SeLe4n.Platform.RPi5.numCores_eq_rpi5_coreCount
#check @SeLe4n.Platform.RPi5.bootCoreId_val_eq_rpi5

/-! ## SM4.A.5 — Simulation bindings: single-core + 4-core SMP -/
#check @SeLe4n.Platform.Sim.SimSingleCorePlatform
#check SeLe4n.Platform.Sim.simSingleCorePlatformBinding
#check SeLe4n.Platform.Sim.simPlatformBinding
#check SeLe4n.Platform.Sim.simRestrictivePlatformBinding

/-! ## SM4.A.6 / SM4.A.7 / SM4.A.8 — CoreId / bootCoreId / allCores recap -/
#check @SeLe4n.Kernel.Concurrency.numCores
#check @SeLe4n.Kernel.Concurrency.CoreId
#check @SeLe4n.Kernel.Concurrency.bootCoreId
#check @SeLe4n.Kernel.Concurrency.allCores
#check @SeLe4n.Kernel.Concurrency.allCores_length
#check @SeLe4n.Kernel.Concurrency.allCores_nodup

-- ============================================================================
-- §2 — Decidable / definitional examples
-- ============================================================================

/-! ## SM4.A.1 — instances the §4.2 rationale relies on (consumed by SM4.B's
`SchedulerState` `BEq`/`DecidableEq`/`Repr`/`default`).  These verify the
chosen `Array`-backed `Vector α n` actually provides them for the canonical
per-core element type `Option ThreadId` — a missing instance here would
break SM4.B, so the bootstrap anchors them. -/
example : DecidableEq (Vector (Option SeLe4n.ThreadId) numCores) := inferInstance
example : Repr (Vector (Option SeLe4n.ThreadId) numCores) := inferInstance
example : Inhabited (Vector (Option SeLe4n.ThreadId) numCores) := inferInstance
example : BEq (Vector (Option SeLe4n.ThreadId) numCores) := inferInstance
-- The `Inhabited` default of a per-core field is the all-`none` vector, and a
-- read at any core is `none` — the exact shape SM4.B.9's
-- `default_state_perCoreInitialized` discharges (via `replicate_get`).
example : (default : Vector (Option SeLe4n.ThreadId) numCores)
            = Vector.replicate numCores default := rfl
example (c : CoreId) :
    (default : Vector (Option SeLe4n.ThreadId) numCores).get c = none :=
  SeLe4n.Vector.replicate_get numCores default c

/-! ## SM4.A.2 lemma 0 — `get_eq_getElem` bridge -/
example : (Vector.replicate 4 (5 : Nat)).get ⟨2, by decide⟩
            = (Vector.replicate 4 (5 : Nat))[2] :=
  SeLe4n.Vector.get_eq_getElem _ ⟨2, by decide⟩

/-! ## SM4.A.2 lemma 1 — `get_set_eq` -/
example : ((Vector.replicate 4 (0 : Nat)).set 1 7 (by decide)).get ⟨1, by decide⟩ = 7 := by
  decide
example (v : Vector Nat 4) : (v.set 1 7 (by decide)).get ⟨1, by decide⟩ = 7 :=
  SeLe4n.Vector.get_set_eq v ⟨1, by decide⟩ 7

/-! ## SM4.A.2 lemma 2 — `get_set_ne` -/
example :
    ((Vector.replicate 4 (0 : Nat)).set 1 7 (by decide)).get ⟨2, by decide⟩
      = (Vector.replicate 4 (0 : Nat)).get ⟨2, by decide⟩ := by
  decide
example (v : Vector Nat 4) :
    (v.set 1 7 (by decide)).get ⟨2, by decide⟩ = v.get ⟨2, by decide⟩ :=
  SeLe4n.Vector.get_set_ne v ⟨1, by decide⟩ ⟨2, by decide⟩ 7 (by decide)

/-! ## SM4.A.2 lemma 3 — `toList_length` -/
example : (Vector.replicate 4 (0 : Nat)).toList.length = 4 :=
  SeLe4n.Vector.toList_length _
example : (Vector.replicate 7 (0 : Nat)).toList.length = 7 := by decide

/-! ## SM4.A.2 lemma 4 — `replicate_get` -/
example : (Vector.replicate 4 (none : Option Nat)).get ⟨2, by decide⟩ = none :=
  SeLe4n.Vector.replicate_get 4 none ⟨2, by decide⟩
example : (Vector.replicate 4 (none : Option Nat)).get ⟨2, by decide⟩ = none := by decide

/-! ## SM4.A.2 lemma 5 — `ext` -/
-- Abstract application: pointwise-equal vectors are equal.
example (v w : Vector Nat 3) (h : ∀ i : Fin 3, v.get i = w.get i) : v = w :=
  SeLe4n.Vector.ext h
-- Concrete witness of the equality `ext` guarantees (decidable form).
example :
    ((Vector.replicate 2 (0 : Nat)).set 0 3 (by decide)).set 1 3 (by decide)
      = Vector.replicate 2 (3 : Nat) := by decide

/-! ## SM4.A.2 lemma 6 — `nodup_of_finRange` -/
example : (List.finRange 4).Nodup := SeLe4n.Vector.nodup_of_finRange 4
example : (List.finRange 0).Nodup := SeLe4n.Vector.nodup_of_finRange 0
example : (List.finRange 1).Nodup := SeLe4n.Vector.nodup_of_finRange 1

/-! ## SM4.A.3 — `Vector` is `Array`-backed (compiles to `Array`) -/
example : (Vector.replicate 5 (9 : Nat)).toArray.size = 5 := by decide
example : (Vector.replicate 5 (9 : Nat)).toArray = Array.replicate 5 9 := rfl
-- Formal witness that a per-core read is an `Array` element access (the
-- type-level half of "O(1), compiles to Array"; the codegen half is the
-- emitted C where `get` lowers to `lean_array_fget`).
example (v : Vector Nat 4) (i : Fin 4) :
    v.get i = v.toArray[i.val]'(v.size_toArray.symm ▸ i.isLt) :=
  SeLe4n.Vector.get_eq_toArray_getElem v i

/-! ## SM4.A.4 — RPi5 coreCount = 4, pinned to numCores -/
example : PlatformBinding.coreCount (platform := RPi5Platform) = 4 := rfl
example : numCores = PlatformBinding.coreCount (platform := RPi5Platform) :=
  numCores_eq_rpi5_coreCount

/-! ## SM4.A.5 — single-core sim = 1, 4-core sims = 4 -/
example : PlatformBinding.coreCount (platform := SimSingleCorePlatform) = 1 := rfl
example : (PlatformBinding.bootCoreId (platform := SimSingleCorePlatform)).val = 0 := rfl
example : PlatformBinding.coreCount (platform := SimSingleCorePlatform) > 0 := by decide
example : PlatformBinding.coreCount (platform := SimPlatform) = 4 := rfl
example : PlatformBinding.coreCount (platform := SimRestrictivePlatform) = 4 := rfl
-- The binding's `coreCount` actually drives the per-core `Vector`
-- machinery: a per-core field on the single-core topology is a
-- one-element vector whose `length` (via the SM4.A.2 helper) is the
-- binding's `coreCount`.  This consumes `SeLe4n.Vector.toList_length` at a
-- binding-derived size rather than a literal.
example :
    (Vector.replicate (PlatformBinding.coreCount (platform := SimSingleCorePlatform))
      (0 : Nat)).toList.length
      = PlatformBinding.coreCount (platform := SimSingleCorePlatform) :=
  SeLe4n.Vector.toList_length _

/-! ## SM4.A.6 / SM4.A.7 / SM4.A.8 — CoreId / bootCoreId / allCores recap -/
example : numCores = 4 := rfl
example (c : CoreId) : c.val < numCores := c.isLt
example : bootCoreId.val = 0 := rfl
example : bootCoreId.val < numCores := bootCoreId_valid
example : allCores.length = numCores := allCores_length
example : allCores.Nodup := allCores_nodup
-- The SM4.A.2 generalisation reproduces `allCores_nodup` (allCores =
-- finRange numCores), and discharges the platform-parameterised form.
example : allCores = List.finRange numCores := rfl
example : allCores.Nodup := SeLe4n.Vector.nodup_of_finRange numCores
example : (List.finRange (PlatformBinding.coreCount (platform := RPi5Platform))).Nodup :=
  SeLe4n.Vector.nodup_of_finRange _

-- ============================================================================
-- §3 — Runtime assertions: every check above also runs in `main`
-- ============================================================================

namespace SeLe4n.Testing.PerCoreVector

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then
    IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

/-- SM4.A.5 topology-parametric driver: build a per-core field of size `k`
    (every slot `= 7`) and fold `Vector.get` over `List.finRange k`,
    summing to `7 * k`.  Driven by a platform binding's `coreCount`, this
    exercises the binding END-TO-END through the per-core `Vector`
    machinery — `Vector.replicate`, `Fin k` indexing, and `Vector.get` —
    rather than merely field-checking `coreCount`.  At `k = 1`
    (`SimSingleCorePlatform`) it is the minimal non-degenerate per-core
    topology. -/
private def perCoreReadSum (k : Nat) : Nat :=
  let v : Vector Nat k := Vector.replicate k 7
  (List.finRange k).foldl (fun acc c => acc + v.get c) 0

/-- SM4.A.2 lemmas 1-4 (`get_set_eq`, `get_set_ne`, `length`,
    `replicate_get`) plus the `get_eq_getElem` bridge, on concrete
    vectors. -/
private def runVectorHelperChecks : IO Unit := do
  IO.println "--- §3.1 SM4.A.2 Vector helpers (get_set_eq/ne, length, replicate_get) ---"
  assertBool "get_eq_getElem: (replicate 4 5).get ⟨2⟩ = (replicate 4 5)[2]"
    (decide ((Vector.replicate 4 (5 : Nat)).get ⟨2, by decide⟩
              = (Vector.replicate 4 (5 : Nat))[2]'(by decide)))
  assertBool "get_set_eq: (set 1 7).get ⟨1⟩ = 7"
    (decide (((Vector.replicate 4 (0 : Nat)).set 1 7 (by decide)).get ⟨1, by decide⟩ = 7))
  assertBool "get_set_ne: (set 1 7).get ⟨2⟩ unchanged"
    (decide (((Vector.replicate 4 (0 : Nat)).set 1 7 (by decide)).get ⟨2, by decide⟩
              = (Vector.replicate 4 (0 : Nat)).get ⟨2, by decide⟩))
  assertBool "length: (replicate 4 0).toList.length = 4"
    (decide ((Vector.replicate 4 (0 : Nat)).toList.length = 4))
  assertBool "replicate_get: (replicate 4 none).get ⟨2⟩ = none"
    (decide ((Vector.replicate 4 (none : Option Nat)).get ⟨2, by decide⟩ = none))

/-- SM4.A.2 lemma 5 (`ext`) and lemma 6 (`nodup_of_finRange`). -/
private def runExtAndNodupChecks : IO Unit := do
  IO.println "--- §3.2 SM4.A.2 ext + nodup_of_finRange ---"
  -- ext-style pointwise equality: two ways of building the same vector
  -- are equal (the property `ext` discharges from per-index agreement).
  assertBool "ext: (set 0 3; set 1 3) (replicate 2 0) = replicate 2 3"
    (decide (((Vector.replicate 2 (0 : Nat)).set 0 3 (by decide)).set 1 3 (by decide)
              = Vector.replicate 2 (3 : Nat)))
  assertBool "nodup_of_finRange 0 holds (List.finRange 0 = [])"
    (decide ((List.finRange 0).Nodup))
  assertBool "nodup_of_finRange 1 holds"
    (decide ((List.finRange 1).Nodup))
  assertBool "nodup_of_finRange numCores holds"
    (decide ((List.finRange SeLe4n.Kernel.Concurrency.numCores).Nodup))
  -- The new general lemma agrees with the SM0.E literal-4 `allCores_nodup`.
  assertBool "allCores = List.finRange numCores"
    (decide (SeLe4n.Kernel.Concurrency.allCores
              = List.finRange SeLe4n.Kernel.Concurrency.numCores))

/-- SM4.A.3: `Vector` is `Array`-backed and computes (O(1) access). -/
private def runArrayBackingChecks : IO Unit := do
  IO.println "--- §3.3 SM4.A.3 Vector is Array-backed (compiles to Array) ---"
  assertBool "toArray.size = n for (replicate 5 9)"
    (decide ((Vector.replicate 5 (9 : Nat)).toArray.size = 5))
  assertBool "toArray = Array.replicate n a"
    (decide ((Vector.replicate 5 (9 : Nat)).toArray = Array.replicate 5 9))
  -- Deep index computes (Array O(1) access through the type's length proof).
  assertBool "(replicate 256 1).get ⟨255⟩ = 1"
    (decide ((Vector.replicate 256 (1 : Nat)).get ⟨255, by decide⟩ = 1))
  -- A round-trip set/read at a high slot also computes.
  assertBool "set at 255 then get at 255 = 42"
    (decide (((Vector.replicate 256 (1 : Nat)).set 255 42 (by decide)).get ⟨255, by decide⟩ = 42))

/-- SM4.A.4 + SM4.A.5: RPi5 + simulation `coreCount` topologies. -/
private def runPlatformCoreCountChecks : IO Unit := do
  IO.println "--- §3.4 SM4.A.4/A.5 PlatformBinding coreCount (RPi5 + sims) ---"
  assertBool "RPi5.coreCount = 4"
    (decide (PlatformBinding.coreCount (platform := RPi5Platform) = 4))
  assertBool "numCores = RPi5.coreCount (pinned)"
    (decide (SeLe4n.Kernel.Concurrency.numCores
              = PlatformBinding.coreCount (platform := RPi5Platform)))
  assertBool "SimSingleCore.coreCount = 1"
    (decide (PlatformBinding.coreCount (platform := SimSingleCorePlatform) = 1))
  assertBool "SimSingleCore.bootCoreId.val = 0"
    (decide ((PlatformBinding.bootCoreId (platform := SimSingleCorePlatform)).val = 0))
  assertBool "SimSingleCore.coreCountPos witness (1 > 0)"
    (decide (PlatformBinding.coreCount (platform := SimSingleCorePlatform) > 0))
  assertBool "SimPlatform.coreCount = 4"
    (decide (PlatformBinding.coreCount (platform := SimPlatform) = 4))
  assertBool "SimRestrictivePlatform.coreCount = 4"
    (decide (PlatformBinding.coreCount (platform := SimRestrictivePlatform) = 4))

/-- SM4.A.6 / SM4.A.7 / SM4.A.8: CoreId / bootCoreId / allCores recap. -/
private def runCoreIdRecapChecks : IO Unit := do
  IO.println "--- §3.5 SM4.A.6/A.7/A.8 CoreId / bootCoreId / allCores recap ---"
  assertBool "numCores = 4"
    (decide (SeLe4n.Kernel.Concurrency.numCores = 4))
  assertBool "bootCoreId.val = 0"
    (decide (SeLe4n.Kernel.Concurrency.bootCoreId.val = 0))
  assertBool "allCores.length = numCores"
    (decide (SeLe4n.Kernel.Concurrency.allCores.length
              = SeLe4n.Kernel.Concurrency.numCores))
  assertBool "allCores.Nodup"
    (decide (SeLe4n.Kernel.Concurrency.allCores.Nodup))
  -- Every enumerated core is in range (CoreId = Fin numCores).
  assertBool "every CoreId in allCores has val < numCores"
    (SeLe4n.Kernel.Concurrency.allCores.all
      (fun c => decide (c.val < SeLe4n.Kernel.Concurrency.numCores)))

/-- SM4.A.3 array-access witness + SM4.A.5 topology-parametric exercise:
    the `get_eq_toArray_getElem` witness on a concrete vector, and the
    platform bindings' `coreCount` driving the per-core `Vector` machinery
    end-to-end (so `SimSingleCorePlatform` is genuinely exercised, not just
    field-checked). -/
private def runArrayWitnessAndTopologyChecks : IO Unit := do
  IO.println "--- §3.6 SM4.A.3 array-access witness + SM4.A.5 topology-parametric ---"
  -- A.3 witness: `.get` equals the underlying `toArray` element (via the
  -- panicking index `[·]!`, sidestepping the getElem bounds proof at runtime;
  -- 2 < 4 so it never panics).
  assertBool "get_eq_toArray_getElem: (replicate 4 9).get ⟨2⟩ = toArray[2]!"
    (decide ((Vector.replicate 4 (9 : Nat)).get ⟨2, by decide⟩
              = (Vector.replicate 4 (9 : Nat)).toArray[2]!))
  -- Each binding's coreCount drives the per-core read-fold (sum = 7 * k).
  assertBool "SimSingleCore (coreCount=1): per-core read-fold = 7*1 = 7"
    (decide (perCoreReadSum (PlatformBinding.coreCount (platform := SimSingleCorePlatform)) = 7))
  assertBool "SimPlatform (coreCount=4): per-core read-fold = 7*4 = 28"
    (decide (perCoreReadSum (PlatformBinding.coreCount (platform := SimPlatform)) = 28))
  assertBool "RPi5 (coreCount=4): per-core read-fold = 7*4 = 28"
    (decide (perCoreReadSum (PlatformBinding.coreCount (platform := RPi5Platform)) = 28))
  -- `length` (SM4.A.2) at the binding-derived size: the single-core field
  -- is a one-element vector.
  assertBool "SimSingleCore: (replicate coreCount 0).toList.length = coreCount (=1)"
    (decide ((Vector.replicate (PlatformBinding.coreCount (platform := SimSingleCorePlatform))
              (0 : Nat)).toList.length
              = PlatformBinding.coreCount (platform := SimSingleCorePlatform)))

/-- SM4.A.1: the `Vector` instances SM4.B's `SchedulerState` relies on
    actually *compute* — `DecidableEq` decides per-core-field equality
    (default vs. a one-slot write), the foundation of the derived `BEq`. -/
private def runInstanceChecks : IO Unit := do
  IO.println "--- §3.7 SM4.A.1 Vector instances compute (DecidableEq for SchedulerState BEq) ---"
  -- DecidableEq reflexive: a default per-core field equals itself.
  assertBool "DecidableEq: default per-core field equals itself"
    (decide ((default : Vector (Option Nat) numCores) = default))
  -- DecidableEq distinguishes a per-core write from the default (non-vacuous).
  assertBool "DecidableEq: a one-core write differs from the default"
    (decide ((default : Vector (Option Nat) numCores).set 0 (some 5) (by decide)
              ≠ (default : Vector (Option Nat) numCores)))
  -- The default per-core field reads `none` at every core (SM4.B.9 shape).
  assertBool "default per-core field reads none at every core"
    (SeLe4n.Kernel.Concurrency.allCores.all
      (fun c => decide ((default : Vector (Option Nat) numCores).get c = none)))

def runPerCoreVectorChecks : IO Unit := do
  IO.println "WS-SM SM4.A — Per-core Vector bootstrap test suite"
  IO.println "===================================="
  runVectorHelperChecks
  runExtAndNodupChecks
  runArrayBackingChecks
  runPlatformCoreCountChecks
  runCoreIdRecapChecks
  runArrayWitnessAndTopologyChecks
  runInstanceChecks
  IO.println "===================================="
  IO.println "All SM4.A per-core Vector bootstrap checks PASS."

end SeLe4n.Testing.PerCoreVector

def main : IO Unit :=
  SeLe4n.Testing.PerCoreVector.runPerCoreVectorChecks
