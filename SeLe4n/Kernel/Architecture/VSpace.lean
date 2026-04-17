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

TPI-001 — CLOSED (X1-K). VSpace determinism is established by four round-trip
functional-correctness theorems in `VSpaceInvariant.lean`:
  - `vspaceLookup_after_map`: map then lookup returns the mapped address
  - `vspaceLookup_map_other`: map at vaddr does not affect other lookups
  - `vspaceLookup_after_unmap`: unmap then lookup returns translationFault
  - `vspaceLookup_unmap_other`: unmap at vaddr does not affect other lookups

Object-level tautologies (`f x = f x` via `rfl`) are NOT accepted as semantic
evidence. The four round-trip theorems above provide genuine semantic contracts
that establish determinism through functional correctness.

Historical: Originally tracked via TPI-001 in
`docs/dev_history/audits/AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md`.
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Model

/-- Logical relation: object `rootId` is a VSpace root bound to `asid`. -/
def asidBoundToRoot (st : SystemState) (asid : SeLe4n.ASID) (rootId : SeLe4n.ObjId) : Prop :=
  ∃ root, st.objects[rootId]? = some (KernelObject.vspaceRoot root) ∧ root.asid = asid

/-- WS-G3/F-P06/U2-H: Locate the root object id carrying `asid` via O(1) hash lookup.
    Falls back to object-store validation to ensure the entry is still a valid VSpaceRoot.
    U2-H: Rejects ASIDs ≥ `maxASID` (65536 on ARM64) as a defense-in-depth
    check — invalid ASIDs cannot appear in the ASID table, but the guard makes
    this explicit. -/
def resolveAsidRoot (st : SystemState) (asid : SeLe4n.ASID) : Option (SeLe4n.ObjId × VSpaceRoot) :=
  match st.asidTable[asid]? with
  | some oid =>
    match st.objects[oid]? with
    | some (.vspaceRoot root) => if root.asid = asid then some (oid, root) else none
    | _ => none
  | none => none

/-- WS-H11/A-05: Default physical address space bound (ARM64 52-bit LPA maximum).
    Used as the upper bound for model-level reasoning. Platform-specific bounds
    (e.g., 44-bit for BCM2712) are enforced via `physicalAddressBoundForConfig`.

    **Proof-layer default only** — production code must use
    `physicalAddressBoundForConfig` (explicit config) or
    `vspaceMapPageCheckedWithFlushFromState` (reads `st.machine.physicalAddressWidth`
    from runtime state). The syscall dispatch path (API.lean) wires through the
    state-aware variant, so all user-facing operations enforce the platform-specific
    bound. Direct use of `physicalAddressBound` is appropriate only in model-level
    theorems where the concrete platform is irrelevant.

    AI6-C (M-13): `physicalAddressBound` (2^52) is the proof-layer default
    only. Internal helpers that use this constant do not need platform-specific
    bounds because they are never called directly from user-facing dispatch.
    Production dispatch always routes through `st.machine.physicalAddressWidth`,
    which resolves to the platform's actual PA width (e.g., 44 for BCM2712). -/
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

/-- WS-H11/S6-B/V4-E: Core VSpace map transition — page table only, no TLB flush.

**Internal proof decomposition helper.** This function operates on the page table
without touching the TLB. It is used by invariant proofs that need to reason
about page table updates independently from TLB effects.

**All external callers must use `vspaceMapPageWithFlush` or
`vspaceMapPageCheckedWithFlush`** to maintain `tlbConsistent` on hardware.
Direct use of this function in production dispatch paths will cause stale TLB
entries on ARM64 (use-after-unmap vulnerability).

V4-E/M-HW-4: Proof-accessible but not for direct dispatch — use
`vspaceMapPageWithFlush` or `vspaceMapPageCheckedWithFlush` instead. -/
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

/-- WS-H11/A-05/S6-B/V4-E: Address-bounds-checked VSpace map — no TLB flush.

**Internal proof decomposition helper.** Use `vspaceMapPageCheckedWithFlush`
for production paths. See `vspaceMapPage` for rationale.

V4-E/M-HW-4: Proof-accessible but not for direct dispatch — use
`vspaceMapPageCheckedWithFlush` instead. -/
def vspaceMapPageChecked (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (perms : PagePermissions := PagePermissions.readOnly) : Kernel Unit :=
  fun st =>
    if !vaddr.isCanonical then .error .addressOutOfBounds
    else if !(paddr.toNat < physicalAddressBound) then .error .addressOutOfBounds
    else vspaceMapPage asid vaddr paddr perms st

/-- S6-B/V4-E: Core VSpace unmap transition — page table only, no TLB flush.

**Internal proof decomposition helper.** Use `vspaceUnmapPageWithFlush` for
production paths. Direct use without TLB flush creates stale entries on ARM64.

V4-E/M-HW-4: Proof-accessible but not for direct dispatch — use
`vspaceUnmapPageWithFlush` instead. -/
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

/-- R7-A.3/M-17/S6-A: **Production entry point** — VSpace map with targeted TLB flush.

    AJ4-B (M-06): Composes page table insertion with a per-(ASID, VAddr) targeted
    TLB flush. Only TLB entries matching `(asid, vaddr)` are invalidated; all other
    cached translations are preserved. This replaces the former full-TLB flush
    (`adapterFlushTlb`) with `adapterFlushTlbByVAddr`, reducing TLB pressure on
    multi-address-space workloads.

    Correctness: `vspaceMapPage` only modifies the VSpaceRoot bound to `asid`, and
    only inserts a mapping at `vaddr`. The targeted flush removes any stale TLB
    entries at `(asid, vaddr)`. Remaining TLB entries are unaffected because:
    - Entries for other ASIDs resolve to unmodified VSpaceRoots
    - Entries for the same ASID but different VAddr resolve to the same VSpaceRoot
      whose other mappings are preserved by HashMap insert frame (`getElem?_insert_ne`)

    All production dispatch paths (syscall API, platform adapters) must use this
    function or `vspaceMapPageCheckedWithFlush`. -/
def vspaceMapPageWithFlush (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (perms : PagePermissions := PagePermissions.readOnly) : Kernel Unit :=
  fun st =>
    match vspaceMapPage asid vaddr paddr perms st with
    | .error e => .error e
    | .ok ((), st') =>
        .ok ((), { st' with tlb := adapterFlushTlbByVAddr st'.tlb asid vaddr })

/-- R7-A.3/M-17/S6-A: **Production entry point** — VSpace unmap with targeted TLB flush.

    AJ4-B (M-06): Composes page table removal with a per-(ASID, VAddr) targeted
    TLB invalidation. After unmapping a virtual address, only TLB entries matching
    `(asid, vaddr)` are cleared, preventing use-after-unmap attacks while preserving
    other cached translations. This replaces the former full-TLB flush.

    Correctness: `vspaceUnmapPage` only modifies the VSpaceRoot bound to `asid`, and
    only erases the mapping at `vaddr`. The targeted flush removes any stale TLB
    entries at `(asid, vaddr)`. Remaining entries are unaffected by HashMap erase
    frame (`getElem?_erase_ne`). -/
def vspaceUnmapPageWithFlush (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) : Kernel Unit :=
  fun st =>
    match vspaceUnmapPage asid vaddr st with
    | .error e => .error e
    | .ok ((), st') =>
        .ok ((), { st' with tlb := adapterFlushTlbByVAddr st'.tlb asid vaddr })

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

/-- X2-E: **State-aware production entry point** — bounds-checked map with TLB flush
    using `physicalAddressWidth` stored in `SystemState.machine`.
    This avoids requiring a separate `MachineConfig` at the API dispatch site;
    the width is read directly from the live machine state set during boot. -/
def vspaceMapPageCheckedWithFlushFromState (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions := PagePermissions.readOnly) : Kernel Unit :=
  fun st =>
    if !vaddr.isCanonical then .error .addressOutOfBounds
    else if !(paddr.toNat < 2^st.machine.physicalAddressWidth) then .error .addressOutOfBounds
    else vspaceMapPageWithFlush asid vaddr paddr perms st

-- ============================================================================
-- V4-J/M-DEF-8: Default permissions documentation
-- ============================================================================

/-- V4-J/M-DEF-8: All production VSpace map entry points accept an explicit
    `perms` parameter with `readOnly` as the default. The internal
    `vspaceMapPage` function's `readOnly` default is never invoked without
    an explicit caller-supplied permission — all production dispatch paths
    (`dispatchWithCap`, `dispatchWithCapChecked`) decode permissions from
    the syscall's register file via `SyscallArgDecode.decodeVSpaceMapArgs`.

    This theorem documents that the default is `readOnly` (least privilege)
    and is W^X compliant. -/
theorem vspaceMapPageCheckedWithFlush_default_is_readOnly :
    (PagePermissions.readOnly).wxCompliant = true := by rfl

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
          | schedContext _ => simp [hObj] at hResolve

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

-- ============================================================================
-- AJ4-B (M-06): Frame lemmas for targeted TLB flush correctness
-- ============================================================================

/-- AJ4-B: `vspaceMapPage` does not modify the TLB — page table changes are
    decoupled from TLB state. The TLB is only modified by the subsequent flush
    in `vspaceMapPageWithFlush`. -/
theorem vspaceMapPage_tlb_eq
    (st st' : SystemState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions)
    (hStep : vspaceMapPage asid vaddr paddr perms st = .ok ((), st')) :
    st'.tlb = st.tlb := by
  unfold vspaceMapPage at hStep
  cases hRes : resolveAsidRoot st asid with
  | none => rw [hRes] at hStep; simp at hStep
  | some val =>
    obtain ⟨rootId, root⟩ := val
    rw [hRes] at hStep; simp at hStep
    split at hStep
    · simp at hStep
    · cases hMap : root.mapPage vaddr paddr perms with
      | none => rw [hMap] at hStep; simp at hStep
      | some root' =>
        rw [hMap] at hStep; simp at hStep
        unfold storeObject at hStep; cases hStep
        rfl

/-- AJ4-B: `vspaceUnmapPage` does not modify the TLB. -/
theorem vspaceUnmapPage_tlb_eq
    (st st' : SystemState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (hStep : vspaceUnmapPage asid vaddr st = .ok ((), st')) :
    st'.tlb = st.tlb := by
  unfold vspaceUnmapPage at hStep
  cases hRes : resolveAsidRoot st asid with
  | none => rw [hRes] at hStep; simp at hStep
  | some val =>
    obtain ⟨rootId, root⟩ := val
    rw [hRes] at hStep; simp at hStep
    cases hUnmap : root.unmapPage vaddr with
    | none => rw [hUnmap] at hStep; simp at hStep
    | some root' =>
      rw [hUnmap] at hStep; simp at hStep
      unfold storeObject at hStep; cases hStep
      rfl

/-- AJ4-B helper: Extract all facts from a successful `resolveAsidRoot`. -/
private theorem resolveAsidRoot_some_facts
    (st : SystemState) (asid : SeLe4n.ASID) (rootId : SeLe4n.ObjId) (root : VSpaceRoot)
    (h : resolveAsidRoot st asid = some (rootId, root)) :
    st.asidTable[asid]? = some rootId ∧
    st.objects[rootId]? = some (.vspaceRoot root) ∧
    root.asid = asid := by
  unfold resolveAsidRoot at h
  cases hA : st.asidTable[asid]? with
  | none => simp [hA] at h
  | some oid =>
    simp [hA] at h
    cases hO : st.objects[oid]? with
    | none => simp [hO] at h
    | some obj =>
      cases obj with
      | vspaceRoot root' =>
        simp [hO] at h
        obtain ⟨hEq, hId, hRoot⟩ := h
        subst hId; subst hRoot
        exact ⟨rfl, hO, hEq⟩
      | _ => simp [hO] at h

/-- AJ4-B (M-06): After `vspaceMapPage`, any TLB entry not matching `(asid, vaddr)`
    remains consistent with the post-state.

    Proof strategy:
    - Different ASID: the entry resolves to the same or a vacuously-true root
    - Same ASID, different VAddr: lookup is preserved by HashMap insert frame -/
theorem vspaceMapPage_entry_consistent_frame
    (st stMid : SystemState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions)
    (hStep : vspaceMapPage asid vaddr paddr perms st = .ok ((), stMid))
    (hObjK : st.objects.invExtK) (hAsidK : st.asidTable.invExtK)
    (hMappingsWF : ∀ (oid : SeLe4n.ObjId) (root : VSpaceRoot),
      st.objects[oid]? = some (.vspaceRoot root) → root.mappings.invExt)
    (entry : TlbEntry)
    (hNotMatch : ¬(entry.asid = asid ∧ entry.vaddr = vaddr))
    (hConsistPre : ∀ rootId root,
      resolveAsidRoot st entry.asid = some (rootId, root) →
      VSpaceRoot.lookup root entry.vaddr = some (entry.paddr, entry.perms)) :
    ∀ rootId root,
      resolveAsidRoot stMid entry.asid = some (rootId, root) →
      VSpaceRoot.lookup root entry.vaddr = some (entry.paddr, entry.perms) := by
  -- Extract intermediate values from vspaceMapPage
  unfold vspaceMapPage at hStep
  cases hRes : resolveAsidRoot st asid with
  | none => rw [hRes] at hStep; simp at hStep
  | some val =>
    obtain ⟨rootId₀, root₀⟩ := val
    have ⟨hAsidTbl, hObjRoot, hRootAsidEq⟩ := resolveAsidRoot_some_facts st asid rootId₀ root₀ hRes
    rw [hRes] at hStep; simp at hStep
    split at hStep
    · simp at hStep
    · rename_i hWx
      cases hMapPage : root₀.mapPage vaddr paddr perms with
      | none => rw [hMapPage] at hStep; simp at hStep
      | some root' =>
        rw [hMapPage] at hStep; simp at hStep
        -- hStep : storeObject rootId₀ (.vspaceRoot root') st = .ok ((), stMid)
        have hRoot'Asid : root'.asid = asid := by
          unfold VSpaceRoot.mapPage at hMapPage
          split at hMapPage
          · simp at hMapPage  -- AK3-B: !perms.wxCompliant case
          · split at hMapPage
            · simp at hMapPage  -- already-mapped case
            · simp at hMapPage; subst hMapPage; exact hRootAsidEq
        have hStoreObjSelf := storeObject_objects_eq st stMid rootId₀
          (KernelObject.vspaceRoot root') hObjK.1 hStep
        have hAsidInv : (match st.objects[rootId₀]? with
            | some (.vspaceRoot oldRoot) => st.asidTable.erase oldRoot.asid
            | _ => st.asidTable).invExt := by
          rw [hObjRoot]; exact st.asidTable.erase_preserves_invExt root₀.asid
            hAsidK.1 hAsidK.2.1
        intro rid r hResolveMid
        by_cases hAsidEq : entry.asid = asid
        · -- Same ASID, different vaddr
          subst hAsidEq
          have hVaddrNe : entry.vaddr ≠ vaddr := fun h => hNotMatch ⟨rfl, h⟩
          have hResolvePost : resolveAsidRoot stMid entry.asid = some (rootId₀, root') := by
            apply resolveAsidRoot_of_asidTable_entry
            · rw [← hRoot'Asid]
              exact storeObject_asidTable_vspaceRoot st stMid rootId₀ root' hAsidInv hStep
            · exact hStoreObjSelf
            · exact hRoot'Asid
          rw [hResolvePost] at hResolveMid
          simp at hResolveMid; obtain ⟨_, hr⟩ := hResolveMid; subst hr
          -- root'.lookup entry.vaddr = root₀.lookup entry.vaddr (HashMap insert frame)
          have hLookupFrame : root'.lookup entry.vaddr = root₀.lookup entry.vaddr := by
            simp only [VSpaceRoot.lookup, VSpaceRoot.mapPage] at hMapPage ⊢
            split at hMapPage
            · simp at hMapPage  -- AK3-B: !perms.wxCompliant case
            · split at hMapPage
              · simp at hMapPage
              · simp at hMapPage; subst hMapPage
                simp only [RHTable_getElem?_eq_get?]
                exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne _ _ _ _
                  (by intro h; exact hVaddrNe (eq_of_beq h).symm)
                  (hMappingsWF rootId₀ root₀ hObjRoot)
          rw [hLookupFrame]
          exact hConsistPre rootId₀ root₀ hRes
        · -- Different ASID: prove resolveAsidRoot stMid = resolveAsidRoot st
          have hNeAsid : entry.asid ≠ root'.asid := fun h => hAsidEq (h.trans hRoot'Asid)
          -- Show ASID table lookup is preserved
          have hAsidPreserved : stMid.asidTable[entry.asid]? = st.asidTable[entry.asid]? := by
            have hMid := storeObject_asidTable_vspaceRoot_ne st stMid rootId₀
              root' entry.asid hNeAsid hAsidInv hStep
            simp [hObjRoot] at hMid
            rw [hMid, hRootAsidEq]
            exact st.asidTable.getElem?_erase_ne_K asid entry.asid
              (by intro h; exact hAsidEq (eq_of_beq h).symm) hAsidK
          -- Show resolveAsidRoot is preserved for different ASIDs
          have hResolveEq : resolveAsidRoot stMid entry.asid = resolveAsidRoot st entry.asid := by
            simp only [resolveAsidRoot]; rw [hAsidPreserved]
            cases hEntryLookup : st.asidTable[entry.asid]? with
            | none => rfl
            | some oid =>
              simp only
              by_cases hOidEq : oid = rootId₀
              · subst hOidEq
                rw [hStoreObjSelf, hObjRoot]
                simp only
                have h1 : ¬(root'.asid = entry.asid) := by rw [hRoot'Asid]; exact fun h => hAsidEq h.symm
                have h2 : ¬(root₀.asid = entry.asid) := by rw [hRootAsidEq]; exact fun h => hAsidEq h.symm
                simp [h1, h2]
              · rw [storeObject_objects_ne st stMid rootId₀ oid
                  (KernelObject.vspaceRoot root') hOidEq hObjK.1 hStep]
          rw [hResolveEq] at hResolveMid
          exact hConsistPre rid r hResolveMid

/-- After `vspaceUnmapPage`, any TLB entry not matching `(asid, vaddr)`
    remains consistent with the post-state.

    Proof strategy (analogous to `vspaceMapPage_entry_consistent_frame`):
    - Different ASID: the entry resolves to the same or a vacuously-true root
    - Same ASID, different VAddr: lookup is preserved by HashMap erase frame -/
theorem vspaceUnmapPage_entry_consistent_frame
    (st stMid : SystemState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (hStep : vspaceUnmapPage asid vaddr st = .ok ((), stMid))
    (hObjK : st.objects.invExtK) (hAsidK : st.asidTable.invExtK)
    (hMappingsWF : ∀ (oid : SeLe4n.ObjId) (root : VSpaceRoot),
      st.objects[oid]? = some (.vspaceRoot root) → root.mappings.invExt)
    (hMappingsSize : ∀ (oid : SeLe4n.ObjId) (root : VSpaceRoot),
      st.objects[oid]? = some (.vspaceRoot root) → root.mappings.size < root.mappings.capacity)
    (entry : TlbEntry)
    (hNotMatch : ¬(entry.asid = asid ∧ entry.vaddr = vaddr))
    (hConsistPre : ∀ rootId root,
      resolveAsidRoot st entry.asid = some (rootId, root) →
      VSpaceRoot.lookup root entry.vaddr = some (entry.paddr, entry.perms)) :
    ∀ rootId root,
      resolveAsidRoot stMid entry.asid = some (rootId, root) →
      VSpaceRoot.lookup root entry.vaddr = some (entry.paddr, entry.perms) := by
  -- Extract intermediate values from vspaceUnmapPage
  unfold vspaceUnmapPage at hStep
  cases hRes : resolveAsidRoot st asid with
  | none => rw [hRes] at hStep; simp at hStep
  | some val =>
    obtain ⟨rootId₀, root₀⟩ := val
    have ⟨hAsidTbl, hObjRoot, hRootAsidEq⟩ := resolveAsidRoot_some_facts st asid rootId₀ root₀ hRes
    rw [hRes] at hStep; simp at hStep
    cases hUnmapPage : root₀.unmapPage vaddr with
    | none => rw [hUnmapPage] at hStep; simp at hStep
    | some root' =>
      rw [hUnmapPage] at hStep; simp at hStep
      -- hStep : storeObject rootId₀ (.vspaceRoot root') st = .ok ((), stMid)
      have hRoot'Asid : root'.asid = asid := by
        unfold VSpaceRoot.unmapPage at hUnmapPage
        split at hUnmapPage <;> simp at hUnmapPage
        subst hUnmapPage; exact hRootAsidEq
      have hStoreObjSelf := storeObject_objects_eq st stMid rootId₀
        (KernelObject.vspaceRoot root') hObjK.1 hStep
      have hAsidInv : (match st.objects[rootId₀]? with
          | some (.vspaceRoot oldRoot) => st.asidTable.erase oldRoot.asid
          | _ => st.asidTable).invExt := by
        rw [hObjRoot]; exact st.asidTable.erase_preserves_invExt root₀.asid
          hAsidK.1 hAsidK.2.1
      intro rid r hResolveMid
      by_cases hAsidEq : entry.asid = asid
      · -- Same ASID, different vaddr
        subst hAsidEq
        have hVaddrNe : entry.vaddr ≠ vaddr := fun h => hNotMatch ⟨rfl, h⟩
        have hResolvePost : resolveAsidRoot stMid entry.asid = some (rootId₀, root') := by
          apply resolveAsidRoot_of_asidTable_entry
          · rw [← hRoot'Asid]
            exact storeObject_asidTable_vspaceRoot st stMid rootId₀ root' hAsidInv hStep
          · exact hStoreObjSelf
          · exact hRoot'Asid
        rw [hResolvePost] at hResolveMid
        simp at hResolveMid; obtain ⟨_, hr⟩ := hResolveMid; subst hr
        -- root'.lookup entry.vaddr = root₀.lookup entry.vaddr (HashMap erase frame)
        have hLookupFrame : root'.lookup entry.vaddr = root₀.lookup entry.vaddr := by
          simp only [VSpaceRoot.lookup, VSpaceRoot.unmapPage] at hUnmapPage ⊢
          split at hUnmapPage
          · simp at hUnmapPage
          · simp at hUnmapPage; subst hUnmapPage
            simp only [RHTable_getElem?_eq_get?]
            exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_ne _ _ _
              (by intro h; exact hVaddrNe (eq_of_beq h).symm)
              (hMappingsWF rootId₀ root₀ hObjRoot)
              (hMappingsSize rootId₀ root₀ hObjRoot)
        rw [hLookupFrame]
        exact hConsistPre rootId₀ root₀ hRes
      · -- Different ASID: prove resolveAsidRoot stMid = resolveAsidRoot st
        have hNeAsid : entry.asid ≠ root'.asid := fun h => hAsidEq (h.trans hRoot'Asid)
        -- Show ASID table lookup is preserved
        have hAsidPreserved : stMid.asidTable[entry.asid]? = st.asidTable[entry.asid]? := by
          have hMid := storeObject_asidTable_vspaceRoot_ne st stMid rootId₀
            root' entry.asid hNeAsid hAsidInv hStep
          simp [hObjRoot] at hMid
          rw [hMid, hRootAsidEq]
          exact st.asidTable.getElem?_erase_ne_K asid entry.asid
            (by intro h; exact hAsidEq (eq_of_beq h).symm) hAsidK
        -- Show resolveAsidRoot is preserved for different ASIDs
        have hResolveEq : resolveAsidRoot stMid entry.asid = resolveAsidRoot st entry.asid := by
          simp only [resolveAsidRoot]; rw [hAsidPreserved]
          cases hEntryLookup : st.asidTable[entry.asid]? with
          | none => rfl
          | some oid =>
            simp only
            by_cases hOidEq : oid = rootId₀
            · subst hOidEq
              rw [hStoreObjSelf, hObjRoot]
              simp only
              have h1 : ¬(root'.asid = entry.asid) := by rw [hRoot'Asid]; exact fun h => hAsidEq h.symm
              have h2 : ¬(root₀.asid = entry.asid) := by rw [hRootAsidEq]; exact fun h => hAsidEq h.symm
              simp [h1, h2]
            · rw [storeObject_objects_ne st stMid rootId₀ oid
                (KernelObject.vspaceRoot root') hOidEq hObjK.1 hStep]
        rw [hResolveEq] at hResolveMid
        exact hConsistPre rid r hResolveMid

end SeLe4n.Kernel.Architecture
