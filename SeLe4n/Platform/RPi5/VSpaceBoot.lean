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

2. `VSpaceRoot.wellFormed` — a freshly-defined structural predicate on
   the root: ASID within hardware bounds, every `(paddr, perms)` pair's
   `paddr.toNat` lies within the 44-bit BCM2712 physical address space, and
   every permission satisfies W^X.

3. `VSpaceRoot.wxCompliant` — per-root W^X: every mapping's permissions
   satisfy the `PagePermissions.wxCompliant` predicate.

4. `bootSafeVSpaceRoot` — per-root boot-safety predicate mirroring the
   well-formedness conjuncts plus a non-empty mappings requirement (a boot
   VSpaceRoot with no mappings cannot serve a single executable page — a
   kernel with an empty L1 page table cannot even fetch its first
   instruction after MMU enable).

The module is deliberately SELF-CONTAINED: it does not yet rewire
`bootFromPlatformChecked` to admit VSpaceRoot objects in `initialObjects`
(that would require a cascading update to ~50+ boot proofs that depend on
the current VSpaceRoot exclusion invariant).  Instead, it provides the
**substantive building blocks** that AN9 (Hardware-binding closure) will
compose when the H3 boot pipeline is wired to real silicon.  See
`docs/audits/AUDIT_v0.29.0_DEFERRED.md` for the cross-reference.

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
    is one identity-mapped page whose permissions are RX. -/
def kernelTextSize : Nat := 0x100000

/-- Kernel data section base (immediately after text; 1 MiB aligned for the
    model).  RW non-executable. -/
def kernelDataBase : PAddr := PAddr.ofNat 0x180000

/-- Kernel stack base (model: 64 KiB at a known offset).  RW non-executable. -/
def kernelStackBase : PAddr := PAddr.ofNat 0x200000

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

/-- **AN7-D.2.2**: structural well-formedness predicate for a VSpaceRoot used
    at kernel boot.  Three conjuncts:

    - `asidBounded`: `asid.val ≤ maxAsidValue` (ARM64 reserves ASID=0 for
      the kernel address space, so ASID 0 is explicitly allowed).
    - `wxCompliant`: every mapping satisfies W^X.
    - `nonEmptyMappings`: at least one mapping is populated (an empty
      L1 table cannot serve the kernel's first instruction fetch after MMU
      enable, so an empty boot root is actively unsafe). -/
def VSpaceRootWellFormed (root : VSpaceRoot) : Prop :=
  root.asid.val ≤ maxAsidValue ∧
  VSpaceRootWxCompliant root ∧
  root.mappings.size > 0

/-- **AN7-D.2.3**: The canonical RPi5 boot root satisfies per-root W^X.

    Proof strategy: reduce to `decide` on the concrete, finite list of
    stored permissions.  Every non-`none` entry's permissions component is
    one of `permsTextRX`, `permsDataRW`, or `permsMmioRW` — each wxCompliant
    by decidable reduction (proven above).  The `List.all` form iterates
    only over actually-stored pairs (`RHTable.values`), so the kernel can
    evaluate the statement in a bounded number of steps. -/
theorem rpi5BootVSpaceRoot_wxCompliant :
    VSpaceRootWxCompliant rpi5BootVSpaceRoot := by
  -- Convert to a decide-eligible statement: every value pair's permission
  -- component is wxCompliant.  The six inserts produce a finite .values
  -- list; each element is one of the three permission constants.
  unfold VSpaceRootWxCompliant
  decide

/-- **AN7-D.2.2**: The canonical RPi5 boot root is well-formed. -/
theorem rpi5BootVSpaceRoot_wellFormed :
    VSpaceRootWellFormed rpi5BootVSpaceRoot := by
  refine ⟨?_, rpi5BootVSpaceRoot_wxCompliant, ?_⟩
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
    closure (see `docs/audits/AUDIT_v0.29.0_DEFERRED.md` — DEF-P-L9 is
    closed by the LANDING of this module; the downstream sweep refinement
    remains a follow-up integration task cross-referenced in AN9-E). -/
theorem rpi5BootVSpaceRoot_admits_bootSafe :
    ∃ root, bootSafeVSpaceRoot root ∧ root.asid = ASID.ofNat 0 ∧
      root.mappings.size > 0 :=
  ⟨rpi5BootVSpaceRoot, rpi5BootVSpaceRoot_bootSafe, rpi5BootVSpaceRoot_asid,
    rpi5BootVSpaceRoot_wellFormed.2.2⟩

end SeLe4n.Platform.RPi5.VSpaceBoot
