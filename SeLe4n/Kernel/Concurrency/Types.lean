-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-SM SM0.E + SM0.F foundational types.  Production-reachable via
-- `Platform.Contract` (which carries `PlatformBinding.sharingDomain`),
-- so this module is in the production import closure rather than the
-- Staged allowlist.

import SeLe4n.Prelude
import SeLe4n.Kernel.Architecture.BarrierComposition

/-!
# WS-SM SM0.E + SM0.F — Concurrency foundational types

This module introduces the foundational typed identifiers WS-SM relies on:

* `numCores` / `CoreId` — typed core identifier with a `Fin numCores`
  representation so every value is in-range by construction.
* `bootCoreId` / `allCores` — enumeration helpers and the boot core
  designation.
* `SharingDomain` — ARMv8 memory-shareability domain (inner vs. outer)
  used to select the appropriate DSB barrier kind on cross-cluster
  topologies.

`numCores` is defined as a literal `4` in this module so the file
does not import `Platform.Contract` (which would create a cycle —
`Platform.Contract` imports this module for `SharingDomain`).  The
literal `4` matches the RPi5 BCM2712 production binding's
`coreCount = 4`; the file is not "platform-agnostic" in the sense
of supporting an arbitrary core count, but it IS independent of the
`Platform.*` import closure.  The pinning theorem
`numCores_eq_rpi5_coreCount` in `SeLe4n.Platform.RPi5.Contract`
discharges `numCores = PlatformBinding.coreCount RPi5Platform` by
`rfl`, so the two literals are structurally pinned at build time —
any future multi-platform build that changes the value must update
both sites in the same PR (the pinning theorem fails to elaborate
otherwise).

The `Concurrency.Sharing.outer` domain is required for cross-cluster
ordering on multi-cluster SoCs (e.g., big.LITTLE).  RPi5 (BCM2712) is
single-cluster Cortex-A76, so its `PlatformBinding.sharingDomain` is
`.inner` — but the abstraction lets the lock primitives select the
correct DSB without rewriting any per-platform branch.
-/

namespace SeLe4n.Kernel.Concurrency

open SeLe4n.Kernel.Architecture

-- ============================================================================
-- SM0.E — Typed core identifier and enumeration
-- ============================================================================

/-- WS-SM SM0.E: number of cores on the kernel's target platform.

At v0.31.4 this is statically `4` (matching RPi5 BCM2712); the
`numCores_eq_rpi5_coreCount` theorem in
`SeLe4n.Platform.RPi5.Contract` pins it to the RPi5
`PlatformBinding.coreCount` field.  A future multi-platform build that
introduces a different `coreCount` must update the literal here in the
same PR (the pinning theorem will fail to elaborate otherwise). -/
def numCores : Nat := 4

/-- WS-SM SM0.E: typed core identifier.  `Fin numCores` makes every
`CoreId` valid by construction; out-of-bounds access is a Lean type
error, not a runtime check.

Using `abbrev` (rather than `def`) lets `Fin`-aware tactics like
`decide` and `omega` see through the definition, which keeps every
`CoreId` example below decidable. -/
abbrev CoreId : Type := Fin numCores

/-- WS-SM SM0.E: `numCores > 0`.  Witnesses the foundational
non-degeneracy precondition: at least one core exists, so a `bootCoreId`
inhabits `CoreId`.  Discharged by `decide` on the literal `4`. -/
theorem numCores_pos : numCores > 0 := by decide

/-- WS-SM SM0.E: the boot core.  Always core `0` in practice;
PlatformBinding-supplied at v1.0.0 so multi-platform builds that boot
on a non-zero affinity slot (rare but possible) can override.  At
v0.31.4 this is the literal `0`, with `numCores_pos` discharging the
in-range obligation. -/
def bootCoreId : CoreId := ⟨0, numCores_pos⟩

/-- WS-SM SM1.B.5: `Inhabited` instance for `CoreId`, witnessed by
`bootCoreId`.  Used by `BaseIO`-monad `panic!` paths in
`Concurrency.Runtime.currentCoreId` (which needs an `Inhabited`
witness to discharge the `panic!` return-type obligation).  The
boot core is the canonical default because every supported platform
boots on it. -/
instance : Inhabited CoreId := ⟨bootCoreId⟩

/-- WS-SM SM0.E: enumeration of every core id.

The list contains exactly `numCores` distinct entries — both witnessed
below (`allCores_length`, `allCores_nodup`) — so iterating over
`allCores` is the canonical way for per-core operations to visit every
core exactly once without an out-of-bounds branch. -/
def allCores : List CoreId := List.finRange numCores

/-- WS-SM SM0.E: `allCores` has length `numCores`.  Discharged by the
Lean Std `List.length_finRange` `@[simp]` lemma. -/
theorem allCores_length : allCores.length = numCores := by
  simp [allCores, List.length_finRange]

/-- WS-SM SM0.E: `allCores` has no duplicate entries.  Lean 4.28's
standard library does not export a `List.nodup_finRange` lemma, so this
routes through the WS-SM SM4.A.2 general lemma
`SeLe4n.PerCoreVector.nodup_of_finRange` (proved by induction for an *arbitrary*
length).  Since `allCores = List.finRange numCores` definitionally, the
general lemma at `numCores` discharges this directly.  Using the general
form rather than a literal-`4` `decide` keeps the proof valid when a
future multi-platform build parameterises `numCores` by
`PlatformBinding.coreCount` (where `decide` on a non-literal would not
reduce). -/
theorem allCores_nodup : allCores.Nodup :=
  SeLe4n.PerCoreVector.nodup_of_finRange numCores

/-- WS-SM SM0.E: `bootCoreId.val < numCores`.  Trivial from the `Fin`
representation; useful as a surface anchor for downstream theorems. -/
theorem bootCoreId_valid : bootCoreId.val < numCores :=
  bootCoreId.isLt

/-- WS-SM SM0.E: `bootCoreId` has raw value `0`.  Used by the per-core
boot-state reasoning that the SMP-shape witness
(`Platform.Boot.bootFromPlatform_smp_witness`, SM4.E) rests on: at boot the
verified kernel drives core 0, so `currentOnCore bootCoreId` is the boot
core's slot of `SchedulerState.current` (a per-core `Vector` since SM4.B). -/
theorem bootCoreId_val_zero : bootCoreId.val = 0 := rfl

/-- WS-SM SM0.E: `allCores` is non-empty.  Direct consequence of
`allCores_length` plus `numCores_pos`.  Useful for `List.head?`-based
iterators that need to know the list inhabits at least one element. -/
theorem allCores_nonempty : allCores ≠ [] := by
  intro h
  have hLen : allCores.length = 0 := by simp [h]
  rw [allCores_length] at hLen
  exact Nat.lt_irrefl 0 (hLen ▸ numCores_pos)

-- ============================================================================
-- SM0.F — SharingDomain and DSB barrier-kind selectors
-- ============================================================================

/-- WS-SM SM0.F: ARMv8 memory-shareability domain.

* `.inner` — Inner-shareable.  Default for single-cluster topologies
  (e.g., RPi5 BCM2712 — quad-core Cortex-A76 in a single cluster).
  Cheaper barrier (DSB ISH covers ordering within the inner-shareable
  domain).
* `.outer` — Outer-shareable.  Required for multi-cluster topologies
  (e.g., big.LITTLE) and for ordering observed by interconnect
  components outside the inner-shareable domain.  More expensive
  barrier (DSB OSH covers a larger set of observers).

PlatformBinding-supplied at v1.0.0 so per-platform code selects the
right barrier without per-call branches. -/
inductive SharingDomain where
  | inner    -- Inner-shareable (single cluster)
  | outer    -- Outer-shareable (multi-cluster / device-coherent)
  deriving DecidableEq, Repr, Inhabited

/-- WS-SM SM0.F: select the data-synchronisation `BarrierKind` for a
given sharing domain.  Used by lock primitives and TLB shootdown
(SM3, SM7) to emit the correct DSB without per-platform branching. -/
def dsbForSharing (d : SharingDomain) : BarrierKind :=
  match d with
  | .inner => .dsbIsh
  | .outer => .dsbOsh

/-- WS-SM SM0.F: select the store-only DSB `BarrierKind` for a given
sharing domain.  Used before MMU updates to flush prior writes only
without ordering loads (slightly cheaper than a full DSB). -/
def dsbStForSharing (d : SharingDomain) : BarrierKind :=
  match d with
  | .inner => .dsbIshst
  | .outer => .dsbOshst

/-- WS-SM SM0.F: inner-shareable selector witness.  Decidable example
discharged by `rfl`. -/
theorem dsbForSharing_inner : dsbForSharing .inner = .dsbIsh := rfl

/-- WS-SM SM0.F: outer-shareable selector witness.  Decidable example
discharged by `rfl`. -/
theorem dsbForSharing_outer : dsbForSharing .outer = .dsbOsh := rfl

/-- WS-SM SM0.F: inner-shareable store-only selector witness. -/
theorem dsbStForSharing_inner : dsbStForSharing .inner = .dsbIshst := rfl

/-- WS-SM SM0.F: outer-shareable store-only selector witness. -/
theorem dsbStForSharing_outer : dsbStForSharing .outer = .dsbOshst := rfl

/-- WS-SM SM0.F: `dsbForSharing` is injective.  Per-domain barrier
kinds are distinct.  Discharged by case analysis on both arguments. -/
theorem dsbForSharing_injective :
    ∀ d₁ d₂ : SharingDomain, d₁ ≠ d₂ → dsbForSharing d₁ ≠ dsbForSharing d₂ := by
  intro d₁ d₂ h
  cases d₁ <;> cases d₂ <;> simp_all <;> decide

/-- WS-SM SM0.F: `dsbStForSharing` is injective. -/
theorem dsbStForSharing_injective :
    ∀ d₁ d₂ : SharingDomain, d₁ ≠ d₂ → dsbStForSharing d₁ ≠ dsbStForSharing d₂ := by
  intro d₁ d₂ h
  cases d₁ <;> cases d₂ <;> simp_all <;> decide

end SeLe4n.Kernel.Concurrency
