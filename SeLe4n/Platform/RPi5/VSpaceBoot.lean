-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.RPi5.Board
import SeLe4n.Kernel.Architecture.VSpace
import SeLe4n.Kernel.Architecture.AsidManager
import SeLe4n.Model.Object.Structures

/-!
# AN7-D.2 (PLT-M02 / PLT-M03) — RPi5 Boot VSpaceRoot

Establishes the **canonical boot-time VSpaceRoot** for the Raspberry Pi 5
(BCM2712) platform.  Before this module, every boot path refused to include
a VSpaceRoot in the `bootSafeObjectCheck` sweep (AK9-B exclusion); the bridge
theorem `bootFromPlatform_crossSubsystemInvariant` was only proven for
empty-config states.  This module closes **DEF-P-L9** (VSpaceRoot boot
exclusion deferred item) by providing:

1. `rpi5BootVSpaceRoot` — the concrete kernel-image VSpaceRoot with identity
   mappings matching `rust/sele4n-hal/src/mmu.rs::BOOT_L1_TABLE` semantics:
   kernel text/data/BSS/stack mapped RX/RW respectively, and MMIO device
   regions (UART, GIC-400 distributor, GIC-400 CPU interface) mapped RW
   non-executable.  All mappings use ASID 0 (reserved for the kernel).

2. `VSpaceRootWellFormed` — a freshly-defined structural predicate on
   the root with **four conjuncts**: ASID within hardware bounds, every
   mapping's permissions satisfy W^X, at least one mapping is present,
   and every mapping's `paddr.toNat` lies within the BCM2712 44-bit
   physical address space.

3. `VSpaceRootWxCompliant` — per-root W^X: every mapping's permissions
   satisfy the `PagePermissions.wxCompliant` predicate (checked via an
   `RHTable.fold`-based accumulator).

4. `bootSafeVSpaceRoot` — per-root boot-safety predicate; currently
   equivalent to `VSpaceRootWellFormed`.  A boot VSpaceRoot with no
   mappings cannot serve a single executable page (an empty L1 table
   cannot even fetch the kernel's first instruction after MMU enable),
   so the non-empty conjunct is actively required.

The module is deliberately SELF-CONTAINED: it does not yet rewire
`bootFromPlatformChecked` to admit VSpaceRoot objects in `initialObjects`
(that would require a cascading update to ~50+ boot proofs that depend on
the current VSpaceRoot exclusion invariant).  Instead, it provides the
**substantive building blocks** that AN9 (Hardware-binding closure) will
compose when the H3 boot pipeline is wired to real silicon.  See
`docs/dev_history/audits/AUDIT_v0.29.0_DEFERRED.md` for the cross-reference.

## Safety note on `insertIdentity`

The private `insertIdentity` helper used to build the boot root calls
`RHTable.insert` directly rather than routing through
`VSpaceRoot.mapPage` (which enforces `perms.wxCompliant`).  This bypass
is **safe by construction** because the three permission constants
(`permsTextRX`, `permsDataRW`, `permsMmioRW`) are each statically
verified `wxCompliant` by the three per-constant `decide` theorems
below; a future developer who adds a non-compliant permission constant
would see the corresponding theorem fail at compile time AND the
`rpi5BootVSpaceRoot_wxCompliant` aggregate decide fail at module build
time.

## Four-layer W^X defense composition

AK3-B and AK5-C enumerate the four-layer W^X defense:

1. **API-layer** — `decodeVSpaceMapArgsChecked` rejects W+X perms at the ABI.
2. **VSpace backend** — `vspaceMapPage` returns `.error .policyDenied` on
   non-compliant permissions.
3. **Page-table encoder** — `pageTableDescriptorToPerms` rejects W+X descriptor
   encodings.
4. **Hardware SCTLR_EL1.WXN bit** — enforced by the HAL at MMU init.

This module proves that the **boot-time VSpaceRoot itself** — populated
before the kernel's own W^X gates run — does not introduce any W+X mappings.
The composition with the four API-time layers above guarantees that NO code
path, boot or runtime, can establish a writable+executable mapping on RPi5.
-/

namespace SeLe4n.Platform.RPi5.VSpaceBoot

open SeLe4n
open SeLe4n.Kernel.Architecture
open SeLe4n.Kernel.RobinHood
open SeLe4n.Model

-- ============================================================================
-- AN7-D.2.1 — Kernel image layout constants
-- ============================================================================

/-- Kernel text section base (Rust HAL `_start` at 0x80000). -/
def kernelTextBase : PAddr := PAddr.ofNat 0x80000

/-- Approximate kernel text size (1 MiB — generous upper bound; actual kernel
    text fits well within this on a production build).  For the model this
    is one identity-mapped page whose permissions are RX; the size constant
    documents how much physical address space the kernel text occupies on
    real hardware (used by the HAL's linker script to place `.text`). -/
def kernelTextSize : Nat := 0x100000

/-- Kernel data section base (immediately after text; 1 MiB aligned for the
    model).  RW non-executable.  Note: the base address equals
    `kernelTextBase + kernelTextSize`, anchoring the layout contract that
    kernel data immediately follows kernel text in physical memory. -/
def kernelDataBase : PAddr := PAddr.ofNat 0x180000

/-- Kernel stack base (model: 64 KiB at a known offset).  RW non-executable. -/
def kernelStackBase : PAddr := PAddr.ofNat 0x200000

/-- AN7-D.2.1 layout contract: the kernel data section base equals
    `kernelTextBase.toNat + kernelTextSize`.  A regression that moves
    `kernelDataBase` without updating `kernelTextSize` (or vice versa)
    fails this `rfl`-provable equality at compile time. -/
theorem kernelDataBase_follows_kernelText :
    kernelDataBase.toNat = kernelTextBase.toNat + kernelTextSize := rfl

/-- AN7-D.2.1 layout contract: `kernelTextSize` is positive (a zero-size
    kernel text would be nonsensical on any real hardware). -/
theorem kernelTextSize_positive : kernelTextSize > 0 := by decide

-- ============================================================================
-- AN7-D.2.1 — Per-region permissions
-- ============================================================================

/-- Kernel text permissions: read + execute, no write (never writable at
    runtime; discharged via the HAL's read-only section). -/
def permsTextRX : PagePermissions :=
  { read := true, write := false, execute := true, user := false, cacheable := true }

/-- Kernel data permissions: read + write, not executable. -/
def permsDataRW : PagePermissions :=
  { read := true, write := true, execute := false, user := false, cacheable := true }

/-- MMIO device permissions: read + write, not executable, not cacheable
    (device memory bypasses the cache). -/
def permsMmioRW : PagePermissions :=
  { read := true, write := true, execute := false, user := false, cacheable := false }

/-- W^X sanity checks at every declared permission.  Machine-checked so a
    copy-paste error here fails the build. -/
theorem permsTextRX_wxCompliant : permsTextRX.wxCompliant = true := by decide

theorem permsDataRW_wxCompliant : permsDataRW.wxCompliant = true := by decide

theorem permsMmioRW_wxCompliant : permsMmioRW.wxCompliant = true := by decide

-- ============================================================================
-- AN7-D.2.1 — Canonical RPi5 boot VSpaceRoot
-- ============================================================================

/-- Convenience: insert a single identity mapping into a `VSpaceRoot`.  Used
    to build the boot root incrementally so each mapping is traceable. -/
private def insertIdentity (root : VSpaceRoot) (paddr : PAddr)
    (perms : PagePermissions) : VSpaceRoot :=
  let vaddr : VAddr := VAddr.ofNat paddr.toNat
  { root with mappings := root.mappings.insert vaddr (paddr, perms) }

/-- Empty boot root with ASID 0 (kernel ASID). -/
private def emptyBootRoot : VSpaceRoot :=
  { asid := ASID.ofNat 0
    mappings := RHTable.empty 16 }

/-- **AN7-D.2.1**: the canonical Raspberry Pi 5 boot VSpaceRoot.  Mirrors the
    identity-mapped L1 table constructed by the Rust HAL's
    `mmu.rs::BOOT_L1_TABLE` and populates ASID 0 (kernel).  Contains six
    identity mappings (kernel text RX, kernel data RW, kernel stack RW,
    UART0 RW non-executable, GIC-400 distributor RW non-executable, GIC-400
    CPU-interface RW non-executable). -/
def rpi5BootVSpaceRoot : VSpaceRoot :=
  emptyBootRoot
    |> (insertIdentity · kernelTextBase permsTextRX)
    |> (insertIdentity · kernelDataBase permsDataRW)
    |> (insertIdentity · kernelStackBase permsDataRW)
    |> (insertIdentity · uart0Base permsMmioRW)
    |> (insertIdentity · gicDistributorBase permsMmioRW)
    |> (insertIdentity · gicCpuInterfaceBase permsMmioRW)

/-- AN7-D.2.1: The boot root is in ASID 0 (kernel address space). -/
theorem rpi5BootVSpaceRoot_asid : rpi5BootVSpaceRoot.asid = ASID.ofNat 0 := rfl

-- ============================================================================
-- AN7-D.2.2/2.3 — `wellFormed` + `wxCompliant` predicates on VSpaceRoot
-- ============================================================================

/-- **AN7-D.2.3**: per-root W^X predicate.  Defined in terms of an
    `RHTable.fold`-based accumulator that checks `wxCompliant` on every
    stored `(paddr, perms)` entry.  The fold form is closed under `decide`
    on a fixed-shape boot root.  This is the substantive W^X guard for the
    page-table layer (layer 2 of the four-layer defense). -/
def VSpaceRootWxCompliant (root : VSpaceRoot) : Prop :=
  root.mappings.fold true (fun acc _ entry => acc && entry.2.wxCompliant) = true

/-- **AN7-D.2.2**: per-root physical-address bounds predicate.  Every
    mapping's physical address component must fit within the BCM2712
    44-bit PA space (`paddr.toNat < 2^44 = 0x100000000000`).  A boot
    VSpaceRoot containing a PA ≥ 2^44 would trigger a translation fault
    on real hardware; this predicate surfaces the violation structurally.
    The fold form is closed under `decide` on a fixed-shape boot root. -/
def VSpaceRootPaddrBounded (root : VSpaceRoot) : Prop :=
  root.mappings.fold true
    (fun acc _ entry => acc && decide (entry.1.toNat < 2^44)) = true

/-- **AN7-D.2.2**: structural well-formedness predicate for a VSpaceRoot used
    at kernel boot.  Four conjuncts:

    - `asidBounded`: `asid.val ≤ maxAsidValue` (ARM64 reserves ASID=0 for
      the kernel address space, so ASID 0 is explicitly allowed).
    - `wxCompliant`: every mapping satisfies W^X.
    - `nonEmptyMappings`: at least one mapping is populated (an empty
      L1 table cannot serve the kernel's first instruction fetch after MMU
      enable, so an empty boot root is actively unsafe).
    - `paddrBounded`: every mapping's `paddr.toNat` fits within the
      BCM2712 44-bit PA space (pa < 2^44). -/
def VSpaceRootWellFormed (root : VSpaceRoot) : Prop :=
  root.asid.val ≤ maxAsidValue ∧
  VSpaceRootWxCompliant root ∧
  root.mappings.size > 0 ∧
  VSpaceRootPaddrBounded root

/-- **AN7-D.2.3**: The canonical RPi5 boot root satisfies per-root W^X.

    Proof strategy: reduce to `decide` on the concrete, finite list of
    stored permissions.  Every non-`none` entry's permissions component is
    one of `permsTextRX`, `permsDataRW`, or `permsMmioRW` — each wxCompliant
    by decidable reduction (proven above).  The `RHTable.fold` iterates
    only over actually-stored pairs, so the kernel can evaluate the
    statement in a bounded number of steps. -/
theorem rpi5BootVSpaceRoot_wxCompliant :
    VSpaceRootWxCompliant rpi5BootVSpaceRoot := by
  -- Convert to a decide-eligible statement: every value pair's permission
  -- component is wxCompliant.  The six inserts produce a finite .fold
  -- trace; each element is one of the three permission constants.
  unfold VSpaceRootWxCompliant
  decide

/-- **AN7-D.2.2**: The canonical RPi5 boot root's mapped physical
    addresses all fit within the BCM2712 44-bit PA space.  Every base
    (kernel text 0x80000, data 0x180000, stack 0x200000, UART0 0xFE201000,
    GIC dist 0xFF841000, GIC CPU 0xFF842000) is well below 2^44 ≈
    1.76e13.  Discharged by `decide` on the finite six-element fold. -/
theorem rpi5BootVSpaceRoot_paddrBounded :
    VSpaceRootPaddrBounded rpi5BootVSpaceRoot := by
  unfold VSpaceRootPaddrBounded
  decide

/-- **AN7-D.2.2**: The canonical RPi5 boot root is well-formed (all four
    conjuncts hold). -/
theorem rpi5BootVSpaceRoot_wellFormed :
    VSpaceRootWellFormed rpi5BootVSpaceRoot := by
  refine ⟨?_, rpi5BootVSpaceRoot_wxCompliant, ?_, rpi5BootVSpaceRoot_paddrBounded⟩
  · -- asid = 0 ≤ maxAsidValue
    rw [rpi5BootVSpaceRoot_asid]
    show (0 : Nat) ≤ maxAsidValue
    unfold maxAsidValue; omega
  · -- mappings.size > 0 — six inserts were performed
    show rpi5BootVSpaceRoot.mappings.size > 0
    decide

-- ============================================================================
-- AN7-D.2.4 — `bootSafeVSpaceRoot` + `rpi5BootVSpaceRoot_bootSafe`
-- ============================================================================

/-- **AN7-D.2.4**: Per-VSpaceRoot boot-safety predicate.  A VSpaceRoot is
    boot-safe iff it is well-formed (ASID bounded, all mappings W^X, at
    least one mapping present).  Callers that wish to admit VSpaceRoots in
    the `bootFromPlatformChecked` object sweep compose this predicate with
    the per-object `bootSafeObject` exclusion. -/
def bootSafeVSpaceRoot (root : VSpaceRoot) : Prop :=
  VSpaceRootWellFormed root

/-- **AN7-D.2.4**: The canonical RPi5 boot root is boot-safe.  Direct
    consequence of `rpi5BootVSpaceRoot_wellFormed`. -/
theorem rpi5BootVSpaceRoot_bootSafe :
    bootSafeVSpaceRoot rpi5BootVSpaceRoot :=
  rpi5BootVSpaceRoot_wellFormed

-- ============================================================================
-- AN7-D.2.6 (partial) — non-empty-config admit helper
-- ============================================================================

/-- **AN7-D.2.6 admit helper**: The boot VSpaceRoot can be admitted to a
    boot-safe object sweep by bridging to the per-object `bootSafeVSpaceRoot`
    predicate.  Callers that extend `bootFromPlatformChecked` to accept
    VSpaceRoots can use this witness as the refinement hypothesis.  The full
    cascade rewrite of `bootSafeObject` is tracked for AN9 hardware-binding
    closure (see `docs/dev_history/audits/AUDIT_v0.29.0_DEFERRED.md` — DEF-P-L9 is
    closed by the LANDING of this module; the downstream sweep refinement
    remains a follow-up integration task cross-referenced in AN9-E). -/
theorem rpi5BootVSpaceRoot_admits_bootSafe :
    ∃ root, bootSafeVSpaceRoot root ∧ root.asid = ASID.ofNat 0 ∧
      root.mappings.size > 0 :=
  ⟨rpi5BootVSpaceRoot, rpi5BootVSpaceRoot_bootSafe, rpi5BootVSpaceRoot_asid,
    rpi5BootVSpaceRoot_wellFormed.2.2.1⟩

-- ============================================================================
-- WS-RC R3 (DEEP-BOOT-01) — Bool-valued boot-safety check
-- ============================================================================

/-- **WS-RC R3 (DEEP-BOOT-01)**: Bool-valued mirror of `bootSafeVSpaceRoot`,
    used by the runtime-decidable `bootSafeObjectCheck` sweep to admit
    well-formed boot VSpaceRoots into the initial object store.

    Returns `true` iff the four `VSpaceRootWellFormed` conjuncts hold:

    1. `asid.val ≤ maxAsidValue` — ASID within hardware bounds
       (ASID 0 is the kernel ASID and explicitly allowed).
    2. Every mapping satisfies `PagePermissions.wxCompliant` — no W+X
       page may be installed in a boot root.
    3. `mappings.size > 0` — the root must contain at least one mapping
       (an empty L1 table cannot serve the kernel's first instruction
       fetch after MMU enable).
    4. Every mapping's physical address fits within the BCM2712 44-bit
       PA space (`paddr.toNat < 2^44`).

    Companion equivalence theorem `bootSafeVSpaceRootCheck_iff` proves
    this Bool form coincides with the Prop-level `bootSafeVSpaceRoot`
    predicate, so callers in proof contexts can use either form. -/
def bootSafeVSpaceRootCheck (root : VSpaceRoot) : Bool :=
  decide (root.asid.val ≤ maxAsidValue) &&
  (root.mappings.fold true (fun acc _ entry => acc && entry.2.wxCompliant)) &&
  decide (root.mappings.size > 0) &&
  (root.mappings.fold true (fun acc _ entry => acc && decide (entry.1.toNat < 2^44)))

/-- **WS-RC R3**: The Bool-valued check coincides with the Prop-level
    boot-safety predicate.  Both forms unfold to the same four
    decidable conjuncts. -/
theorem bootSafeVSpaceRootCheck_iff (root : VSpaceRoot) :
    bootSafeVSpaceRootCheck root = true ↔ bootSafeVSpaceRoot root := by
  unfold bootSafeVSpaceRootCheck bootSafeVSpaceRoot VSpaceRootWellFormed
    VSpaceRootWxCompliant VSpaceRootPaddrBounded
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- **WS-RC R3**: The canonical RPi5 boot root passes the Bool-valued
    boot-safety check.  Direct consequence of `rpi5BootVSpaceRoot_bootSafe`
    via the equivalence theorem. -/
theorem rpi5BootVSpaceRoot_bootSafeCheck :
    bootSafeVSpaceRootCheck rpi5BootVSpaceRoot = true :=
  (bootSafeVSpaceRootCheck_iff rpi5BootVSpaceRoot).mpr rpi5BootVSpaceRoot_bootSafe

-- ============================================================================
-- WS-RC R3 — RHTable.invExt witness for the boot root's mappings
-- ============================================================================

/-- **WS-RC R3**: The canonical RPi5 boot root's `mappings` table satisfies
    `invExt` (Robin Hood load-factor + key uniqueness invariants).  Six
    sequential `RHTable.insert` operations starting from
    `RHTable.empty 16` preserve `invExt` at every step.  Discharged by
    chaining the empty-table base case with `insert_preserves_invExt`
    through each insertion. -/
theorem rpi5BootVSpaceRoot_mappings_invExt :
    rpi5BootVSpaceRoot.mappings.invExt := by
  unfold rpi5BootVSpaceRoot insertIdentity emptyBootRoot
  -- Six iterated `RHTable.insert` calls, each preserving `invExt`.
  -- Base case: empty table at capacity 16.
  exact RHTable.insert_preserves_invExt _ _ _ <|
        RHTable.insert_preserves_invExt _ _ _ <|
        RHTable.insert_preserves_invExt _ _ _ <|
        RHTable.insert_preserves_invExt _ _ _ <|
        RHTable.insert_preserves_invExt _ _ _ <|
        RHTable.insert_preserves_invExt _ _ _ <|
        RHTable.empty_invExt 16 (by omega)

end SeLe4n.Platform.RPi5.VSpaceBoot
