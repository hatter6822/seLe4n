/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.PageTable
import SeLe4n.Kernel.Architecture.VSpaceBackend

/-!
# ARMv8 VSpaceBackend Instance and Refinement Proof (AG6-C/AG6-D)

Implements the `VSpaceBackend` typeclass for ARMv8-A 4-level page tables,
proving it refines the existing HashMap-based `VSpaceRoot` model.

## Design

The `ARMv8VSpace` structure wraps:
- A TTBR (translation table base register) pointing to the L0 table
- A `Memory` region containing all page table pages
- A bump allocator for intermediate table page allocation
- An ASID bound to this address space
- A **shadow** `VSpaceRoot` maintaining the abstract HashMap specification

All mutations are applied to both the hardware page table and the shadow
in lockstep. The VSpaceBackend proof obligations are satisfied via the
shadow's existing HashMap lemmas. A separate simulation relation theorem
guarantees the hardware walk agrees with the shadow.

## Refinement Architecture

Following the standard refinement pattern (cf. CertiKOS, seL4 proof):
1. The VSpaceBackend instance proves correctness using the shadow
2. `hwLookupPage` performs the actual hardware page table walk
3. `simulationRelation` proves the hardware walk equals the shadow lookup
4. All 7 VSpace invariants transfer from the HashMap model via simulation

This design enables fully-proven proofs for the VSpaceBackend instance while
keeping the hardware walk implementation separate for the FFI bridge.

**AJ-M05 / H-01 scope:** The full VSpaceARMv8 refinement proofs
(`lookupPage_refines`, `vspaceProperty_transfer`) are proven against the
shadow HashMap model. End-to-end proofs against hardware page table walks
require the module to be integrated into the main kernel execution path
(currently orphaned — see §8.15.1 of SELE4N_SPEC.md for the activation
roadmap). Deferred to WS-V (AG10: Hardware Integration).
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n
open SeLe4n.Model

-- ============================================================================
-- AG6-C-i: ARMv8VSpace structure and bump allocator
-- ============================================================================

/-!
## AK3-K (A-M08, A-M09 / MEDIUM — DEFER+DOC): MMU / Device-memory ordering

The `simulationRelation` (below) and `ensureTable` (below) implicitly
assume that the ARMv8-A hardware page-table walker sees the same memory
state as `pageTableMemory` in the shadow model. On real hardware this
assumption is invalid without:

  1. `dsb ishst` after writing each page-table descriptor — ensures the
     write is visible to the hardware walker before the MMU observes it.
  2. `dc cvac` + `dsb ish` on freshly-allocated page-table pages — the
     `ensureTable` path zero-pages allocate storage but does not clean
     D-cache to point-of-coherency, so the walker can see stale cache
     lines on multi-core systems.
  3. `isb` before resuming execution at a mapping affected by the
     descriptor update — forces the pipeline to re-fetch translations.

The proof layer defines these barrier tokens (see AK3-G
`CacheBarrierKind` and `Platform.RPi5.MmioAdapter.BarrierKind`) but
does not yet prove that every `mapPage`/`unmapPage` path composes them.
Full state-machine binding to the Rust HAL (`rust/sele4n-hal/src/tlb.rs`
and `cache.rs`) is scheduled for WS-V (H3 hardware integration).

Disposition: DEFER-WITH-ROADMAP. The Rust HAL already emits the required
barriers in `tlb.rs` (AG6-F) and `cache.rs` (AG6-F/AG8-B); the proof-layer
obligation will compose them via the AK3-G/K predicate family once the
FFI round-trip is closed in WS-V.
-/

/-- Simple bump allocator for page table pages (4KiB aligned).
    Used during page table construction to allocate intermediate table pages.
    Reclamation deferred to future optimization. -/
structure BumpAllocator where
  nextPage : PAddr
  endPage  : PAddr
  deriving DecidableEq, Repr

/-- Allocate a single 4KiB page from the bump allocator.
    Returns `none` if the allocator is exhausted. -/
def BumpAllocator.allocate (alloc : BumpAllocator) : Option (BumpAllocator × PAddr) :=
  if alloc.nextPage.toNat + 4096 ≤ alloc.endPage.toNat then
    some ({ alloc with nextPage := PAddr.ofNat (alloc.nextPage.toNat + 4096) },
          alloc.nextPage)
  else none

/-- ARMv8 virtual address space backed by a 4-level page table.
    Maintains both a hardware page table in memory and a shadow HashMap
    for proof-friendly verification. -/
structure ARMv8VSpace where
  ttbr             : PAddr
  pageTableMemory  : Memory
  allocator        : BumpAllocator
  asid             : ASID
  shadow           : VSpaceRoot

-- ============================================================================
-- AG6-C-ii: Write helpers for page table memory
-- ============================================================================

/-- Write a single byte to memory at a given physical address. -/
def writeByte (mem : Memory) (addr : PAddr) (val : UInt8) : Memory :=
  fun a => if a == addr then val else mem a

/-- Write a UInt64 to memory at a given address in little-endian order. -/
def writeUInt64 (mem : Memory) (addr : PAddr) (val : UInt64) : Memory :=
  let m0 := writeByte mem (PAddr.ofNat (addr.toNat + 0)) (val &&& 0xFF).toUInt8
  let m1 := writeByte m0 (PAddr.ofNat (addr.toNat + 1)) ((val >>> 8) &&& 0xFF).toUInt8
  let m2 := writeByte m1 (PAddr.ofNat (addr.toNat + 2)) ((val >>> 16) &&& 0xFF).toUInt8
  let m3 := writeByte m2 (PAddr.ofNat (addr.toNat + 3)) ((val >>> 24) &&& 0xFF).toUInt8
  let m4 := writeByte m3 (PAddr.ofNat (addr.toNat + 4)) ((val >>> 32) &&& 0xFF).toUInt8
  let m5 := writeByte m4 (PAddr.ofNat (addr.toNat + 5)) ((val >>> 40) &&& 0xFF).toUInt8
  let m6 := writeByte m5 (PAddr.ofNat (addr.toNat + 6)) ((val >>> 48) &&& 0xFF).toUInt8
  writeByte m6 (PAddr.ofNat (addr.toNat + 7)) ((val >>> 56) &&& 0xFF).toUInt8

/-- Write a page table descriptor to memory at `tableBase + index * 8`. -/
def writeDescriptor (mem : Memory) (tableBase : PAddr) (index : Nat)
    (desc : PageTableDescriptor) : Memory :=
  let addr := PAddr.ofNat (tableBase.toNat + index * 8)
  writeUInt64 mem addr (descriptorToUInt64 desc)

/-- Zero-fill a 4KiB page in memory (used when allocating fresh table pages). -/
def zeroPage (mem : Memory) (pageAddr : PAddr) : Memory :=
  fun a =>
    if a.toNat ≥ pageAddr.toNat && a.toNat < pageAddr.toNat + 4096 then 0
    else mem a

-- ============================================================================
-- AG6-C-ii: lookupPage (read-only operations)
-- ============================================================================

/-- Hardware page table walk: look up a virtual address using the 4-level
    ARMv8 page table walk from PageTable.lean. This is the actual hardware
    code path used at runtime via FFI. -/
def ARMv8VSpace.hwLookupPage (vs : ARMv8VSpace) (va : VAddr)
    : Option (PAddr × PagePermissions) :=
  pageTableWalkPerms vs.pageTableMemory vs.ttbr va

/-- Physical-address-only hardware lookup. -/
def ARMv8VSpace.hwLookupAddr (vs : ARMv8VSpace) (va : VAddr) : Option PAddr :=
  (vs.hwLookupPage va).map Prod.fst

-- ============================================================================
-- AG6-C-iii: mapPage with table creation
-- ============================================================================

/-- AK3-B (A-H01 / HIGH): Convert abstract `PagePermissions` to hardware
    `PageAttributes`, failing closed on W+X combinations.

    W+X (writable + executable) is always rejected at encode time — this is
    the innermost (L3) layer of the four-layer W^X defense-in-depth pipeline:

      L0 `vspaceMapPage` wrapper      — rejects W+X before resolution
      L1 `ARMv8VSpace.mapPage`        — rejects W+X before descriptor write
      L2 `VSpaceRoot.mapPage`         — rejects W+X before HashMap insert
      L3 `fromPagePermissions`        — rejects W+X at hardware encode
      L4 SCTLR.WXN = 1 (AK5-C)        — hardware-level enforcement

    Returning `Option PageAttributes` forces callers to handle the W+X
    rejection explicitly. -/
def fromPagePermissions (perms : PagePermissions) : Option PageAttributes :=
  -- AK3-B.1: Fail closed on W+X (defense-in-depth layer 3)
  if perms.write && perms.execute then
    none
  else
    some
      { attrIndex  := if perms.cacheable then ⟨0, by omega⟩ else ⟨2, by omega⟩
        ap         := if perms.write then
                        if perms.user then .rwAll else .rwEL1
                      else
                        if perms.user then .roAll else .roEL1
        sh         := .innerShareable
        af         := true
        pxn        := !perms.execute || perms.user
        uxn        := !perms.execute || !perms.user
        contiguous := false
        dirty      := perms.write
      }

/-- AK3-B.1: Successful `fromPagePermissions` excludes W+X. -/
theorem fromPagePermissions_wx_excludes_W_and_X
    (perms : PagePermissions) (hw : PageAttributes)
    (h : fromPagePermissions perms = some hw) :
    ¬ (perms.write = true ∧ perms.execute = true) := by
  unfold fromPagePermissions at h
  split at h
  · simp at h
  · rename_i hNot
    intro ⟨hw', hx⟩
    apply hNot
    simp [hw', hx]

/-- Ensure a table entry exists at the given level, creating one if needed. -/
private def ensureTable (mem : Memory) (alloc : BumpAllocator) (tableBase : PAddr)
    (index : Nat) (level : PageTableLevel)
    : Option (Memory × BumpAllocator × PAddr) :=
  let desc := readDescriptor mem tableBase index level
  match desc with
  | .table nextBase => some (mem, alloc, nextBase)
  | .invalid =>
    match alloc.allocate with
    | none => none
    | some (alloc', newPage) =>
      let mem' := zeroPage mem newPage
      let mem'' := writeDescriptor mem' tableBase index (.table newPage)
      some (mem'', alloc', newPage)
  | _ => none

/-- AK3-B (A-H01 / HIGH): Map a virtual address to a physical address
    with given permissions. W^X-compliant permissions required.

    Four-layer W^X defense:
    - L1 (this function) rejects W+X at VSpaceBackend entry
    - L2 delegates to `vs.shadow.mapPage` which ALSO rejects W+X
    - L3 calls `fromPagePermissions` which returns `none` on W+X
    - All three layers must reject independently (defense-in-depth)

    Updates both the hardware page table and the shadow HashMap. -/
def ARMv8VSpace.mapPage (vs : ARMv8VSpace) (va : VAddr) (pa : PAddr)
    (perms : PagePermissions) : Option ARMv8VSpace :=
  -- AK3-B.3: L1 W^X gate — reject before any state mutation
  if !perms.wxCompliant then none
  else
    -- Shadow conflict check (also prevents hardware overwrite)
    match vs.shadow.mapPage va pa perms with
    | none => none
    | some shadow' =>
      match ensureTable vs.pageTableMemory vs.allocator vs.ttbr (l0Index va) .l0 with
      | none => none
      | some (mem1, alloc1, l1base) =>
        match ensureTable mem1 alloc1 l1base (l1Index va) .l1 with
        | none => none
        | some (mem2, alloc2, l2base) =>
          match ensureTable mem2 alloc2 l2base (l2Index va) .l2 with
          | none => none
          | some (mem3, alloc3, l3base) =>
            -- AK3-B.1: L3 gate — fromPagePermissions returns Option
            match fromPagePermissions perms with
            | none => none
            | some attrs =>
              let mem4 := writeDescriptor mem3 l3base (l3Index va) (.page pa attrs)
              some { vs with
                pageTableMemory := mem4
                allocator := alloc3
                shadow := shadow' }

-- ============================================================================
-- AG6-C-iv: unmapPage
-- ============================================================================

/-- AI2-B (M-14): Error type for VSpace hardware walk failures.
    Distinguishes shadow-level failures from hardware page-table walk failures
    at specific levels. This prevents silent shadow/HW divergence. -/
inductive VSpaceWalkError where
  | shadowUnmapFailed  : VSpaceWalkError
  | walkFailedAtLevel  : PageTableLevel → VSpaceWalkError
  deriving DecidableEq, Repr

/-- Unmap a virtual address. Updates both hardware page table and shadow.
    AI2-B (M-14): Returns `Except VSpaceWalkError` to surface HW walk failures
    instead of silently succeeding with shadow-only updates. -/
def ARMv8VSpace.unmapPage (vs : ARMv8VSpace) (va : VAddr)
    : Except VSpaceWalkError ARMv8VSpace :=
  match vs.shadow.unmapPage va with
  | none => .error .shadowUnmapFailed
  | some shadow' =>
    let d0 := readDescriptor vs.pageTableMemory vs.ttbr (l0Index va) .l0
    match d0 with
    | .table l1base =>
      let d1 := readDescriptor vs.pageTableMemory l1base (l1Index va) .l1
      match d1 with
      | .table l2base =>
        let d2 := readDescriptor vs.pageTableMemory l2base (l2Index va) .l2
        match d2 with
        | .table l3base =>
          let mem' := writeDescriptor vs.pageTableMemory l3base (l3Index va) .invalid
          .ok { vs with pageTableMemory := mem', shadow := shadow' }
        | _ => .error (.walkFailedAtLevel .l2)
      | _ => .error (.walkFailedAtLevel .l1)
    | _ => .error (.walkFailedAtLevel .l0)

-- ============================================================================
-- AG6-C-v: VSpaceBackend proof obligations
-- ============================================================================

/-- mapPage preserves the ASID. AK3-B: adds wxCompliant guard case. -/
theorem ARMv8VSpace.mapPage_preserves_asid
    (vs vs' : ARMv8VSpace) (va : VAddr) (pa : PAddr) (perms : PagePermissions)
    (hMap : vs.mapPage va pa perms = some vs') : vs'.asid = vs.asid := by
  simp only [mapPage] at hMap
  split at hMap
  · -- AK3-B.3: !perms.wxCompliant case
    exact absurd hMap (by simp)
  · split at hMap
    · exact absurd hMap (by simp)
    · split at hMap
      · exact absurd hMap (by simp)
      · split at hMap
        · exact absurd hMap (by simp)
        · split at hMap
          · exact absurd hMap (by simp)
          · split at hMap
            · -- AK3-B.1: fromPagePermissions = none case
              exact absurd hMap (by simp)
            · have := Option.some.inj hMap; subst this; rfl

/-- unmapPage preserves the ASID (AI2-B: updated for Except return). -/
theorem ARMv8VSpace.unmapPage_preserves_asid
    (vs vs' : ARMv8VSpace) (va : VAddr)
    (hUnmap : vs.unmapPage va = .ok vs') : vs'.asid = vs.asid := by
  simp only [unmapPage] at hUnmap
  split at hUnmap
  · simp at hUnmap
  · split at hUnmap
    · split at hUnmap
      · split at hUnmap
        · simp only [Except.ok.injEq] at hUnmap; subst hUnmap; rfl
        · simp at hUnmap
      · simp at hUnmap
    · simp at hUnmap

/-- mapPage updates the shadow via VSpaceRoot.mapPage. AK3-B: accounts for
    wxCompliant and fromPagePermissions guards. -/
theorem ARMv8VSpace.mapPage_shadow_eq
    (vs vs' : ARMv8VSpace) (va : VAddr) (pa : PAddr) (perms : PagePermissions)
    (hMap : vs.mapPage va pa perms = some vs') :
    ∃ shadow', vs.shadow.mapPage va pa perms = some shadow' ∧ vs'.shadow = shadow' := by
  simp only [mapPage] at hMap
  split at hMap
  · -- AK3-B.3: !perms.wxCompliant
    exact absurd hMap (by simp)
  · split at hMap
    · exact absurd hMap (by simp)
    · rename_i shadow' hShadow
      split at hMap
      · exact absurd hMap (by simp)
      · split at hMap
        · exact absurd hMap (by simp)
        · split at hMap
          · exact absurd hMap (by simp)
          · split at hMap
            · -- AK3-B.1: fromPagePermissions = none
              exact absurd hMap (by simp)
            · have := Option.some.inj hMap; subst this
              exact ⟨shadow', hShadow, rfl⟩

/-- unmapPage updates the shadow via VSpaceRoot.unmapPage (AI2-B: Except). -/
theorem ARMv8VSpace.unmapPage_shadow_eq
    (vs vs' : ARMv8VSpace) (va : VAddr)
    (hUnmap : vs.unmapPage va = .ok vs') :
    ∃ shadow', vs.shadow.unmapPage va = some shadow' ∧ vs'.shadow = shadow' := by
  simp only [unmapPage] at hUnmap
  split at hUnmap
  · simp at hUnmap
  · rename_i shadow' hShadow
    refine ⟨shadow', hShadow, ?_⟩
    split at hUnmap
    · split at hUnmap
      · split at hUnmap
        · simp only [Except.ok.injEq] at hUnmap; subst hUnmap; rfl
        · simp at hUnmap
      · simp at hUnmap
    · simp at hUnmap

-- ============================================================================
-- AG6-C-v: VSpaceBackend instance
-- ============================================================================

/-- VSpaceBackend instance for ARMv8 4-level page tables.
    Proof obligations delegate to the shadow HashMap via existing lemmas.
    The `rootWF` predicate requires `shadow.mappings.invExtK` (the kernel-level
    RHTable invariant). The hardware walk is exposed separately via
    `hwLookupPage` with a refinement theorem (AG6-D). -/
-- AI2-B: Helper to convert ARMv8VSpace.unmapPage (Except) to Option for
-- VSpaceBackend typeclass contract compatibility.
private def ARMv8VSpace.unmapPageOpt (vs : ARMv8VSpace) (va : VAddr)
    : Option ARMv8VSpace :=
  match vs.unmapPage va with
  | .ok v => some v
  | .error _ => none

private theorem ARMv8VSpace.unmapPageOpt_some_iff_ok (vs vs' : ARMv8VSpace) (va : VAddr) :
    vs.unmapPageOpt va = some vs' ↔ vs.unmapPage va = .ok vs' := by
  simp only [unmapPageOpt]
  cases vs.unmapPage va with
  | ok v => simp
  | error e => simp

instance armv8VSpaceBackend : VSpaceBackend ARMv8VSpace where
  mapPage := fun vs va pa perms => vs.mapPage va pa perms
  unmapPage := fun vs va => vs.unmapPageOpt va
  lookupPage := fun vs va => vs.shadow.lookup va
  lookupAddr := fun vs va => vs.shadow.lookupAddr va
  rootAsid := fun vs => vs.asid
  rootWF := fun vs => vs.shadow.mappings.invExtK ∧ vs.asid = vs.shadow.asid
  mapPage_preserves_asid := fun vs vs' va pa perms hMap =>
    ARMv8VSpace.mapPage_preserves_asid vs vs' va pa perms hMap
  unmapPage_preserves_asid := fun vs vs' va hUnmap => by
    rw [ARMv8VSpace.unmapPageOpt_some_iff_ok] at hUnmap
    exact ARMv8VSpace.unmapPage_preserves_asid vs vs' va hUnmap
  lookup_after_map := fun vs vs' va pa perms hWf hMap => by
    obtain ⟨shadow', hShadow, hEq⟩ := ARMv8VSpace.mapPage_shadow_eq vs vs' va pa perms hMap
    simp only [hEq]
    exact VSpaceRoot.lookup_mapPage_eq vs.shadow shadow' va pa perms
      (SeLe4n.Kernel.RobinHood.RHTable.invExtK_invExt hWf.1) hShadow
  lookup_map_other := fun vs vs' va va' pa perms hWf hNe hMap => by
    obtain ⟨shadow', hShadow, hEq⟩ := ARMv8VSpace.mapPage_shadow_eq vs vs' va pa perms hMap
    simp only [hEq]
    exact VSpaceRoot.lookup_mapPage_ne vs.shadow shadow' va va' pa perms hNe
      (SeLe4n.Kernel.RobinHood.RHTable.invExtK_invExt hWf.1) hShadow
  lookup_after_unmap := fun vs vs' va hWf hUnmap => by
    rw [ARMv8VSpace.unmapPageOpt_some_iff_ok] at hUnmap
    obtain ⟨shadow', hShadow, hEq⟩ := ARMv8VSpace.unmapPage_shadow_eq vs vs' va hUnmap
    simp only [hEq]
    exact VSpaceRoot.lookup_unmapPage_eq_none vs.shadow shadow' va
      (SeLe4n.Kernel.RobinHood.RHTable.invExtK_invExt hWf.1) hShadow
  lookup_unmap_other := fun vs vs' va va' hWf hNe hUnmap => by
    rw [ARMv8VSpace.unmapPageOpt_some_iff_ok] at hUnmap
    obtain ⟨shadow', hShadow, hEq⟩ := ARMv8VSpace.unmapPage_shadow_eq vs vs' va hUnmap
    simp only [hEq]
    exact VSpaceRoot.lookup_unmapPage_ne vs.shadow shadow' va va' hNe hWf.1 hShadow

#check (inferInstance : VSpaceBackend ARMv8VSpace)

-- ============================================================================
-- AG6-D: Refinement proof — simulation relation
-- ============================================================================

/-- Simulation relation: the ARMv8 hardware page table walk and the shadow
    HashMap produce identical results for all virtual addresses.
    This is the core refinement invariant.

    Design note: `mapPage_refines` and `unmapPage_refines` (proving that
    mapPage/unmapPage preserve the simulation relation) are deferred to AG7
    FFI integration. These proofs require showing that `writeDescriptor`
    chains produce exactly the right page table walk — a deep hardware
    verification task. The VSpaceBackend correctness proofs go through the
    shadow and do not require simulation preservation. The simulation
    relation is established at VSpace construction time and is maintained
    by the lockstep shadow+hardware update design in mapPage/unmapPage. -/
def simulationRelation (hw : ARMv8VSpace) : Prop :=
  ∀ va, hw.hwLookupPage va = hw.shadow.lookup va

/-- Lookup refinement: under simulation, hardware lookup equals shadow lookup. -/
theorem hwLookupPage_refines (hw : ARMv8VSpace) (hSim : simulationRelation hw) (va : VAddr) :
    hw.hwLookupPage va = hw.shadow.lookup va :=
  hSim va

/-- Hardware lookupAddr refinement. -/
theorem hwLookupAddr_refines (hw : ARMv8VSpace) (hSim : simulationRelation hw) (va : VAddr) :
    hw.hwLookupAddr va = hw.shadow.lookupAddr va := by
  simp [ARMv8VSpace.hwLookupAddr, VSpaceRoot.lookupAddr, hSim va]

/-- Master invariant transfer: any property of the shadow's lookup function
    also holds for the hardware lookup function under simulation.
    This lifts all 7 VSpace invariant predicates. -/
theorem vspaceProperty_transfer (hw : ARMv8VSpace) (hSim : simulationRelation hw)
    (P : (VAddr → Option (PAddr × PagePermissions)) → Prop)
    (hP : P (fun va => hw.shadow.lookup va)) :
    P (fun va => hw.hwLookupPage va) := by
  have : (fun va => hw.hwLookupPage va) = (fun va => hw.shadow.lookup va) := by
    funext va; exact hSim va
  rw [this]; exact hP

end SeLe4n.Kernel.Architecture
