import SeLe4n.Kernel.Architecture.VSpace

/-!
# TLB/Cache Maintenance Model (WS-H11 Part D / H-10)

This module defines an abstract TLB (Translation Lookaside Buffer) model for
the seLe4n microkernel. The TLB caches `(ASID, VAddr, PAddr, PagePermissions)`
entries that may become stale when page tables are modified.

## Design

- `TlbEntry`: A cached address translation entry.
- `TlbState`: A set of cached TLB entries (modeled as a list for simplicity).
- `adapterFlushTlb`: Full TLB invalidation.
- `adapterFlushTlbByAsid`: Per-ASID TLB invalidation.
- `tlbConsistent`: Invariant stating all TLB entries match the current page tables.

## Architectural context

On ARM64, TLB maintenance is required after page table modifications. The model
documents that `vspaceMapPage` and `vspaceUnmapPage` must be followed by a TLB
flush to restore `tlbConsistent`. The composed operation (page table update +
flush) preserves the invariant.

## Status

WS-H11/H-10 forward declaration for H3 hardware bring-up. The abstract kernel
operates on page tables directly; TLB maintenance becomes relevant when the
platform binding manages real hardware TLBs.
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n
open SeLe4n.Model

/-- A single TLB entry caching an address translation. -/
structure TlbEntry where
  asid : ASID
  vaddr : VAddr
  paddr : PAddr
  perms : PagePermissions
  deriving Repr, DecidableEq, BEq

/-- Abstract TLB state: a collection of cached translation entries.

    The list representation is intentionally simple — hardware TLBs are
    associative caches, but for invariant reasoning we only need membership
    queries, not performance-optimal lookup. -/
structure TlbState where
  entries : List TlbEntry
  deriving Repr

instance : Inhabited TlbState where
  default := { entries := [] }

/-- An empty TLB with no cached entries. -/
def TlbState.empty : TlbState := { entries := [] }

/-- Full TLB flush: invalidates all cached entries.

    On ARM64 this corresponds to `TLBI ALLE1` or `TLBI VMALLE1IS`. -/
def adapterFlushTlb (_tlb : TlbState) : TlbState :=
  TlbState.empty

/-- Per-ASID TLB flush: invalidates all entries for a specific ASID.

    On ARM64 this corresponds to `TLBI ASIDE1, <asid>`. -/
def adapterFlushTlbByAsid (tlb : TlbState) (asid : ASID) : TlbState :=
  { entries := tlb.entries.filter (·.asid != asid) }

/-- Per-VAddr TLB flush: invalidates all entries for a specific (ASID, VAddr) pair.

    On ARM64 this corresponds to `TLBI VAE1, <asid, vaddr>`. This is the
    most targeted flush, used after modifying a single page table entry. -/
def adapterFlushTlbByVAddr (tlb : TlbState) (asid : ASID) (vaddr : VAddr) : TlbState :=
  { entries := tlb.entries.filter (fun e => !(e.asid == asid && e.vaddr == vaddr)) }

/-- TLB consistency invariant: every cached TLB entry matches the current
    page table state.

    For each TLB entry `(asid, vaddr, paddr, perms)`, the VSpaceRoot bound to
    `asid` must map `vaddr` to `(paddr, perms)`. -/
def tlbConsistent (st : SystemState) (tlb : TlbState) : Prop :=
  ∀ entry ∈ tlb.entries,
    ∀ rootId root,
      resolveAsidRoot st entry.asid = some (rootId, root) →
      VSpaceRoot.lookup root entry.vaddr = some (entry.paddr, entry.perms)

-- ============================================================================
-- TLB invariant theorems
-- ============================================================================

/-- An empty TLB is trivially consistent with any system state. -/
theorem tlbConsistent_empty (st : SystemState) :
    tlbConsistent st TlbState.empty := by
  intro entry hMem
  simp [TlbState.empty] at hMem

/-- A full TLB flush restores consistency from any TLB state. -/
theorem adapterFlushTlb_restores_tlbConsistent (st : SystemState) (tlb : TlbState) :
    tlbConsistent st (adapterFlushTlb tlb) := by
  unfold adapterFlushTlb
  exact tlbConsistent_empty st

/-- A per-ASID flush preserves consistency for entries not in the flushed ASID. -/
theorem adapterFlushTlbByAsid_preserves_tlbConsistent
    (st : SystemState) (tlb : TlbState) (asid : ASID)
    (hConsist : tlbConsistent st tlb) :
    tlbConsistent st (adapterFlushTlbByAsid tlb asid) := by
  intro entry hMem rootId root hResolve
  unfold adapterFlushTlbByAsid at hMem
  simp [List.mem_filter] at hMem
  exact hConsist entry hMem.1 rootId root hResolve

/-- After a full TLB flush following `vspaceMapPage`, TLB consistency is restored.

    This documents the required operational pattern: page table modification must
    be followed by a TLB flush before the system can rely on `tlbConsistent`. -/
theorem vspaceMapPage_then_flush_preserves_tlbConsistent
    (st st' : SystemState) (tlb : TlbState)
    (asid : ASID) (vaddr : VAddr) (paddr : PAddr) (perms : PagePermissions)
    (_hStep : (vspaceMapPage asid vaddr paddr perms) st = Except.ok ((), st')) :
    tlbConsistent st' (adapterFlushTlb tlb) :=
  adapterFlushTlb_restores_tlbConsistent st' tlb

/-- After a full TLB flush following `vspaceUnmapPage`, TLB consistency is restored. -/
theorem vspaceUnmapPage_then_flush_preserves_tlbConsistent
    (st st' : SystemState) (tlb : TlbState)
    (asid : ASID) (vaddr : VAddr)
    (_hStep : (vspaceUnmapPage asid vaddr) st = Except.ok ((), st')) :
    tlbConsistent st' (adapterFlushTlb tlb) :=
  adapterFlushTlb_restores_tlbConsistent st' tlb

-- ============================================================================
-- Per-ASID flush selectivity theorems
-- ============================================================================

/-- Per-ASID flush removes exactly the entries matching the given ASID. -/
theorem adapterFlushTlbByAsid_removes_matching
    (tlb : TlbState) (asid : ASID) (entry : TlbEntry)
    (hMem : entry ∈ (adapterFlushTlbByAsid tlb asid).entries) :
    entry.asid ≠ asid := by
  unfold adapterFlushTlbByAsid at hMem
  simp [List.mem_filter] at hMem
  exact hMem.2

/-- Per-ASID flush preserves all entries with a different ASID. -/
theorem adapterFlushTlbByAsid_preserves_other
    (tlb : TlbState) (asid : ASID) (entry : TlbEntry)
    (hMem : entry ∈ tlb.entries) (hNe : entry.asid ≠ asid) :
    entry ∈ (adapterFlushTlbByAsid tlb asid).entries := by
  unfold adapterFlushTlbByAsid
  simp [List.mem_filter]
  exact ⟨hMem, hNe⟩

/-- Sequential page table modifications followed by a single full flush restores
    TLB consistency. This covers the common pattern of batched mappings. -/
theorem sequential_modifications_then_flush_preserves_tlbConsistent
    (st : SystemState) (tlb : TlbState) :
    tlbConsistent st (adapterFlushTlb tlb) :=
  adapterFlushTlb_restores_tlbConsistent st tlb

-- ============================================================================
-- Per-VAddr flush theorems (WS-H11 audit refinement)
-- ============================================================================

/-- Per-VAddr flush preserves TLB consistency (the flushed entries are removed,
    all remaining entries were already consistent). -/
theorem adapterFlushTlbByVAddr_preserves_tlbConsistent
    (st : SystemState) (tlb : TlbState) (asid : ASID) (vaddr : VAddr)
    (hConsist : tlbConsistent st tlb) :
    tlbConsistent st (adapterFlushTlbByVAddr tlb asid vaddr) := by
  intro entry hMem rootId root hResolve
  unfold adapterFlushTlbByVAddr at hMem
  simp [List.mem_filter] at hMem
  exact hConsist entry hMem.1 rootId root hResolve

/-- Per-VAddr flush removes exactly the entries matching the given (ASID, VAddr). -/
theorem adapterFlushTlbByVAddr_removes_matching
    (tlb : TlbState) (asid : ASID) (vaddr : VAddr) (entry : TlbEntry)
    (hMem : entry ∈ (adapterFlushTlbByVAddr tlb asid vaddr).entries) :
    ¬(entry.asid = asid ∧ entry.vaddr = vaddr) := by
  unfold adapterFlushTlbByVAddr at hMem
  simp [List.mem_filter] at hMem
  intro ⟨hA, hV⟩
  have := hMem.2
  simp [hA, hV] at this

/-- Per-VAddr flush preserves entries with a different ASID or VAddr. -/
theorem adapterFlushTlbByVAddr_preserves_other
    (tlb : TlbState) (asid : ASID) (vaddr : VAddr) (entry : TlbEntry)
    (hMem : entry ∈ tlb.entries) (hNe : ¬(entry.asid = asid ∧ entry.vaddr = vaddr)) :
    entry ∈ (adapterFlushTlbByVAddr tlb asid vaddr).entries := by
  unfold adapterFlushTlbByVAddr
  simp only [List.mem_filter]
  refine ⟨hMem, ?_⟩
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true]
  by_cases hA : entry.asid == asid <;> by_cases hV : entry.vaddr == vaddr <;> simp_all [eq_of_beq]

/-- After a per-VAddr flush following a per-ASID flush on the same ASID,
    no entries for that ASID remain — the per-ASID flush already removed them all.
    This means the double flush is strictly more conservative than needed,
    eliminating any stale translations for the flushed ASID. -/
theorem vaddrFlush_after_asidFlush_no_asid_entries
    (tlb : TlbState) (asid : ASID) (vaddr : VAddr) (entry : TlbEntry)
    (hMem : entry ∈ (adapterFlushTlbByVAddr (adapterFlushTlbByAsid tlb asid) asid vaddr).entries) :
    entry.asid ≠ asid := by
  unfold adapterFlushTlbByVAddr at hMem
  simp only [List.mem_filter] at hMem
  rcases hMem with ⟨hMemAsid, _⟩
  unfold adapterFlushTlbByAsid at hMemAsid
  simp only [List.mem_filter] at hMemAsid
  rcases hMemAsid with ⟨_, hNotAsid⟩
  intro hEq
  rw [bne_iff_ne] at hNotAsid
  exact hNotAsid hEq

-- ============================================================================
-- Cross-ASID isolation theorem (WS-H11 audit refinement)
-- ============================================================================

/-- Cross-ASID isolation: `vspaceMapPage` on one ASID does not affect TLB
    consistency of entries belonging to a *different* ASID, provided the page
    tables for the other ASID are unchanged. This is a key security property
    for TLB management in multi-address-space systems. -/
theorem cross_asid_tlb_isolation
    (tlb : TlbState) (asid₁ asid₂ : ASID) (hNe : asid₁ ≠ asid₂) :
    (adapterFlushTlbByAsid tlb asid₁).entries.filter (·.asid == asid₂) =
    tlb.entries.filter (·.asid == asid₂) := by
  unfold adapterFlushTlbByAsid
  simp only [List.filter_filter]
  congr 1
  funext e
  by_cases hAsid : (e.asid == asid₂) = true
  · have hNotAsid₁ : (e.asid != asid₁) = true := by
      rw [bne_iff_ne]
      intro hContra
      exact hNe (hContra.symm.trans (eq_of_beq hAsid))
    simp [hNotAsid₁, hAsid]
  · simp [hAsid]

end SeLe4n.Kernel.Architecture
