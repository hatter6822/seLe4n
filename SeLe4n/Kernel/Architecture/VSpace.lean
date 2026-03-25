/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State

/-!
WS-C3 proof-surface note:

Determinism of pure Lean definitions is a meta-property of evaluation, so object-level
tautologies of the form `f x = f x` are not accepted as semantic evidence in this model.
VSpace semantic obligations are tracked via TPI-001 in
`docs/dev_history/audits/AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md`.
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Model

/-- Logical relation: object `rootId` is a VSpace root bound to `asid`. -/
def asidBoundToRoot (st : SystemState) (asid : SeLe4n.ASID) (rootId : SeLe4n.ObjId) : Prop :=
  ∃ root, st.objects[rootId]? = some (KernelObject.vspaceRoot root) ∧ root.asid = asid

/-- WS-G3/F-P06: Locate the root object id carrying `asid` via O(1) hash lookup.
    Falls back to object-store validation to ensure the entry is still a valid VSpaceRoot. -/
def resolveAsidRoot (st : SystemState) (asid : SeLe4n.ASID) : Option (SeLe4n.ObjId × VSpaceRoot) :=
  match st.asidTable[asid]? with
  | some oid =>
    match st.objects[oid]? with
    | some (.vspaceRoot root) => if root.asid = asid then some (oid, root) else none
    | _ => none
  | none => none

/-- WS-H11/A-05: Default physical address space bound (ARM64 52-bit LPA maximum).
    Used as the upper bound for model-level reasoning. Platform-specific bounds
    (e.g., 44-bit for BCM2712) are enforced via `physicalAddressBoundForConfig`. -/
def physicalAddressBound : Nat := 2^52

/-- U2-D/U-H07: Platform-specific physical address bound derived from `MachineConfig`.
    BCM2712 (RPi5) uses 44-bit PA, meaning addresses in [2^44, 2^52) pass the default
    model bound but are invalid on hardware. This function provides the platform bound. -/
def physicalAddressBoundForConfig (config : MachineConfig) : Nat :=
  2^config.physicalAddressWidth

/-- U2-D: Well-formedness: platform PA width must not exceed ARM64 LPA maximum (52 bits). -/
theorem physicalAddressBoundForConfig_le_default (config : MachineConfig)
    (h : config.physicalAddressWidth ≤ 52) :
    physicalAddressBoundForConfig config ≤ physicalAddressBound := by
  unfold physicalAddressBoundForConfig physicalAddressBound
  exact Nat.pow_le_pow_right (by omega) h

/-- WS-H11/S6-B: Core VSpace map transition — page table only, no TLB flush.

**Internal proof decomposition helper.** This function operates on the page table
without touching the TLB. It is used by invariant proofs that need to reason
about page table updates independently from TLB effects.

**All external callers must use `vspaceMapPageWithFlush` or
`vspaceMapPageCheckedWithFlush`** to maintain `tlbConsistent` on hardware.
Direct use of this function in production dispatch paths will cause stale TLB
entries on ARM64 (use-after-unmap vulnerability). -/
def vspaceMapPage (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (perms : PagePermissions := PagePermissions.readOnly) : Kernel Unit :=
  fun st =>
    match resolveAsidRoot st asid with
    | none => .error .asidNotBound
    | some (rootId, root) =>
        if !perms.wxCompliant then .error .policyDenied
        else
          match root.mapPage vaddr paddr perms with
          | none => .error .mappingConflict
          | some root' =>
              storeObject rootId (.vspaceRoot root') st

/-- WS-H11/A-05/S6-B: Address-bounds-checked VSpace map — no TLB flush.

**Internal proof decomposition helper.** Use `vspaceMapPageCheckedWithFlush`
for production paths. See `vspaceMapPage` for rationale. -/
def vspaceMapPageChecked (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (perms : PagePermissions := PagePermissions.readOnly) : Kernel Unit :=
  fun st =>
    if !vaddr.isCanonical then .error .addressOutOfBounds
    else if !(paddr.toNat < physicalAddressBound) then .error .addressOutOfBounds
    else vspaceMapPage asid vaddr paddr perms st

/-- S6-B: Core VSpace unmap transition — page table only, no TLB flush.

**Internal proof decomposition helper.** Use `vspaceUnmapPageWithFlush` for
production paths. Direct use without TLB flush creates stale entries on ARM64. -/
def vspaceUnmapPage (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) : Kernel Unit :=
  fun st =>
    match resolveAsidRoot st asid with
    | none => .error .asidNotBound
    | some (rootId, root) =>
        match root.unmapPage vaddr with
        | none => .error .translationFault
        | some root' =>
            storeObject rootId (.vspaceRoot root') st

/-- WS-H11: Deterministic VSpace translation helper returning physical address and permissions. -/
def vspaceLookupFull (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) :
    Kernel (SeLe4n.PAddr × PagePermissions) :=
  fun st =>
    match resolveAsidRoot st asid with
    | none => .error .asidNotBound
    | some (_, root) =>
        match root.lookup vaddr with
        | none => .error .translationFault
        | some entry => .ok (entry, st)

/-- Deterministic VSpace translation helper with explicit failure on unresolved mappings.
Returns only the physical address for backward compatibility. -/
def vspaceLookup (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) : Kernel SeLe4n.PAddr :=
  fun st =>
    match resolveAsidRoot st asid with
    | none => .error .asidNotBound
    | some (_, root) =>
        match root.lookupAddr vaddr with
        | none => .error .translationFault
        | some paddr => .ok (paddr, st)

-- ============================================================================
-- R7-A.3/M-17: TLB-flushing VSpace operations
-- ============================================================================

/-- R7-A.3/M-17/S6-A: **Production entry point** — VSpace map with integrated TLB flush.

    Composes page table insertion with a full TLB flush, ensuring `tlbConsistent`
    is preserved through the combined operation. All production dispatch paths
    (syscall API, platform adapters) must use this function or
    `vspaceMapPageCheckedWithFlush`.

    The core `vspaceMapPage` is retained as an internal proof decomposition
    helper — it operates on page tables only and does not touch the TLB. -/
def vspaceMapPageWithFlush (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (perms : PagePermissions := PagePermissions.readOnly) : Kernel Unit :=
  fun st =>
    match vspaceMapPage asid vaddr paddr perms st with
    | .error e => .error e
    | .ok ((), st') =>
        .ok ((), { st' with tlb := adapterFlushTlb st'.tlb })

/-- R7-A.3/M-17/S6-A: **Production entry point** — VSpace unmap with integrated TLB flush.

    Composes page table removal with a full TLB invalidation. After unmapping a
    virtual address, all TLB entries are cleared, preventing use-after-unmap
    attacks on hardware. A full flush is conservative but simple; hardware
    platforms may refine to per-ASID or per-VAddr flushes via
    `adapterFlushTlbByVAddr`. -/
def vspaceUnmapPageWithFlush (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) : Kernel Unit :=
  fun st =>
    match vspaceUnmapPage asid vaddr st with
    | .error e => .error e
    | .ok ((), st') =>
        .ok ((), { st' with tlb := adapterFlushTlb st'.tlb })

/-- R7-A.3/M-17/S6-A: **Production entry point** — address-bounds-checked map with TLB flush.
This is the recommended entry point for user-space-initiated VSpace map operations. -/
def vspaceMapPageCheckedWithFlush (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions := PagePermissions.readOnly) : Kernel Unit :=
  fun st =>
    if !vaddr.isCanonical then .error .addressOutOfBounds
    else if !(paddr.toNat < physicalAddressBound) then .error .addressOutOfBounds
    else vspaceMapPageWithFlush asid vaddr paddr perms st

/-- U2-D/U-H07: **Platform-aware production entry point** — bounds-checked map with TLB flush
    using platform-specific physical address width from `MachineConfig`.
    BCM2712 (RPi5) uses 44-bit PA, meaning addresses in [2^44, 2^52) are rejected
    by this function but accepted by the default `vspaceMapPageCheckedWithFlush`.
    Use this function when a `MachineConfig` is available (runtime dispatch paths). -/
def vspaceMapPageCheckedWithFlushPlatform (config : MachineConfig)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions := PagePermissions.readOnly) : Kernel Unit :=
  fun st =>
    if !vaddr.isCanonical then .error .addressOutOfBounds
    else if !(paddr.toNat < physicalAddressBoundForConfig config) then .error .addressOutOfBounds
    else vspaceMapPageWithFlush asid vaddr paddr perms st

-- ============================================================================
-- T6-L/M-ARCH-4: Targeted TLB flush operations
-- ============================================================================

/-- T6-L/M-ARCH-4: Per-ASID TLB flush — invalidates all TLB entries for a
    specific ASID. On ARM64 this corresponds to `TLBI ASIDE1, <asid>`.
    More efficient than full flush when only one address space is modified.
    Delegates to `Model.adapterFlushTlbByAsid`. -/
def tlbFlushByASID (asid : SeLe4n.ASID) : Kernel Unit :=
  fun st => .ok ((), { st with tlb := adapterFlushTlbByAsid st.tlb asid })

/-- T6-L/M-ARCH-4: Per-page TLB flush — invalidates all TLB entries for a
    specific (ASID, VAddr) pair. On ARM64 this corresponds to
    `TLBI VAE1, <asid, vaddr>`. Most efficient targeted flush.
    Delegates to `Model.adapterFlushTlbByVAddr`. -/
def tlbFlushByPage (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) : Kernel Unit :=
  fun st => .ok ((), { st with tlb := adapterFlushTlbByVAddr st.tlb asid vaddr })

/-- T6-L/M-ARCH-4: Combined ASID+page flush — a convenience alias for the
    most common targeted flush pattern (invalidate one page in one address space).
    Equivalent to `tlbFlushByPage`. -/
abbrev tlbFlushByASIDPage := tlbFlushByPage

/-- T6-L: Full TLB flush as a kernel operation. Conservative fallback when
    the ASID or VAddr of the affected mapping is unknown.
    Marked as the fallback — callers should prefer targeted flushes when the
    ASID and VAddr are available. -/
def tlbFlushAll : Kernel Unit :=
  fun st => .ok ((), { st with tlb := adapterFlushTlb st.tlb })

/-- T6-L: Full flush removes all entries. -/
theorem tlbFlushAll_empty (st : SystemState) :
    (adapterFlushTlb st.tlb).entries = [] := by
  simp [adapterFlushTlb, TlbState.empty]

/-- T6-L: Per-ASID flush does not affect the non-TLB state. -/
theorem tlbFlushByASID_state_frame (asid : SeLe4n.ASID) (st st' : SystemState)
    (hStep : tlbFlushByASID asid st = .ok ((), st')) :
    st'.objects = st.objects ∧ st'.scheduler = st.scheduler ∧
    st'.machine = st.machine := by
  unfold tlbFlushByASID at hStep
  cases hStep; exact ⟨rfl, rfl, rfl⟩

/-- T6-L: Per-page flush does not affect the non-TLB state. -/
theorem tlbFlushByPage_state_frame (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (st st' : SystemState)
    (hStep : tlbFlushByPage asid vaddr st = .ok ((), st')) :
    st'.objects = st.objects ∧ st'.scheduler = st.scheduler ∧
    st'.machine = st.machine := by
  unfold tlbFlushByPage at hStep
  cases hStep; exact ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- resolveAsidRoot extraction and characterization lemmas (F-08 / TPI-001)
-- ============================================================================

/-- ASID roots in the bounded discovery window are unique. -/
def vspaceAsidRootsUnique (st : SystemState) : Prop :=
  ∀ (oid₁ oid₂ : SeLe4n.ObjId) (root₁ root₂ : VSpaceRoot),
    st.objects[oid₁]? = some (KernelObject.vspaceRoot root₁) →
    st.objects[oid₂]? = some (KernelObject.vspaceRoot root₂) →
    root₁.asid = root₂.asid →
    oid₁ = oid₂

/-- WS-G3: Extract concrete object-store and ASID table facts from a successful
    `resolveAsidRoot` result. Pure definitional — no invariant hypothesis needed. -/
theorem resolveAsidRoot_some_implies_obj
    (st : SystemState) (asid : SeLe4n.ASID)
    (rootId : SeLe4n.ObjId) (root : VSpaceRoot)
    (hResolve : resolveAsidRoot st asid = some (rootId, root)) :
    st.asidTable[asid]? = some rootId ∧
    st.objects[rootId]? = some (KernelObject.vspaceRoot root) ∧
    root.asid = asid := by
  unfold resolveAsidRoot at hResolve
  cases hTable : st.asidTable[asid]? with
  | none => simp [hTable] at hResolve
  | some oid =>
      simp only [hTable] at hResolve
      cases hObj : st.objects[oid]? with
      | none => simp [hObj] at hResolve
      | some obj =>
          cases obj with
          | vspaceRoot r =>
              simp only [hObj] at hResolve
              by_cases hAsidEq : r.asid = asid
              · simp only [hAsidEq, ite_true] at hResolve
                have hPairEq := Option.some.inj hResolve
                have hOidEq : oid = rootId := congrArg Prod.fst hPairEq
                have hRootEq : r = root := congrArg Prod.snd hPairEq
                subst hOidEq; subst hRootEq
                exact ⟨rfl, hObj, hAsidEq⟩
              · simp only [hAsidEq, ite_false] at hResolve; cases hResolve
          | tcb _ => simp [hObj] at hResolve
          | cnode _ => simp [hObj] at hResolve
          | endpoint _ => simp [hObj] at hResolve
          | notification _ => simp [hObj] at hResolve
          | untyped _ => simp [hObj] at hResolve

/-- WS-G3/F-P06: Characterization lemma — given the ASID table entry and object-store
    evidence, `resolveAsidRoot` returns exactly the expected root.

    This replaces `resolveAsidRoot_of_unique_root` — no ASID uniqueness or objectIndex
    membership needed, just the table entry and object-store facts. -/
theorem resolveAsidRoot_of_asidTable_entry
    (st : SystemState) (asid : SeLe4n.ASID)
    (rootId : SeLe4n.ObjId) (root : VSpaceRoot)
    (hTable : st.asidTable[asid]? = some rootId)
    (hObj : st.objects[rootId]? = some (KernelObject.vspaceRoot root))
    (hAsid : root.asid = asid) :
    resolveAsidRoot st asid = some (rootId, root) := by
  unfold resolveAsidRoot
  simp [hTable, hObj, hAsid]

-- ============================================================================
-- storeObject preservation lemmas for VSpace operations
-- ============================================================================

/-- After `storeObject` at a rootId that was already in objectIndex, the objectIndex is unchanged.
    Requires objectIndexSet to be consistent (contains id ↔ id ∈ objectIndex). -/
theorem storeObject_objectIndex_eq_of_mem
    (st st' : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (_hMem : id ∈ st.objectIndex)
    (hSync : st.objectIndexSet.contains id = true)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objectIndex = st.objectIndex := by
  unfold storeObject at hStore
  cases hStore
  simp [hSync]

end SeLe4n.Kernel.Architecture
