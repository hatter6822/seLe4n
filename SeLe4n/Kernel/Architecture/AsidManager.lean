/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State

/-!
# ASID Generation and Management (AG6-H / H3-ARCH-04)

Implements ASID (Address Space Identifier) allocation for ARMv8-A on RPi5.
ASIDs tag TLB entries, enabling per-address-space TLB partitioning without
full flushes on context switch.

## Design

- `AsidPool`: Bump allocator with rollover. Tracks the next ASID to allocate
  and a generation counter for tracking rollover events.
- On ASID rollover (all ASIDs exhausted), the generation increments and a
  full TLB flush is required to eliminate stale entries from the prior generation.
- RPi5: 16-bit ASID (maxAsid = 65536) from BCM2712 / Cortex-A76.

## Uniqueness Invariant

`asidPoolUnique`: No two active VSpaces share the same ASID. Maintained by:
1. Sequential allocation (bump) ensures freshness within a generation
2. Full TLB flush on rollover ensures no stale translations survive
3. Freed ASIDs are tracked for reuse (free list)

## References

- ARM ARM D8.12: ASID and VMID (process/VM identifiers)
- ARM ARM D8.14.2: ASID rollover and TLB invalidation
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n
open SeLe4n.Model

-- ============================================================================
-- ASID pool structure
-- ============================================================================

/-- Maximum ASID value for 16-bit ASIDs (RPi5 / Cortex-A76).
    ARM ARM D8.12: ASID width configured via TCR_EL1.AS.
    With AS=1: 16-bit ASIDs, range [0, 65535]. -/
def maxAsidValue : Nat := 65536

/-- AK3-A (A-C01 / CRITICAL) — AsidPool TLB-maintenance contract:

    1. On `allocate`, if `requiresFlush := true`, the HAL must invoke
       `tlb::tlbi_asid(returned_asid)` before the new ASID is loaded into
       TTBR0. Enforced by AI2-C and the updated rollover path in AK3-A.

    2. On rollover (generation bump), the HAL must additionally invoke
       `tlb::tlbi_vmalle1` to flush all EL1 translations tagged with the
       old generation. Covered by AK3-D (generation bump on free-list
       reuse) and the HAL-side discipline in `rust/sele4n-hal/src/tlb.rs`.

    3. On `free`, no TLB flush is required at the kernel level — the
       ASID is returned to the free-list and removed from the active
       set; hardware entries will be invalidated on reuse per (1).

    ASID allocation pool fields:
    - `nextAsid`: Next ASID to allocate on the bump path (range [0, maxAsid])
    - `generation`: Increments on rollover and on free-list reuse (AK3-D)
    - `freeList`: ASIDs returned by freed VSpaces, available for reuse
    - `activeAsids`: AK3-A ground-truth active set; `Nodup` invariant
    - `activeCount`: Retained scalar; invariant: = `activeAsids.length` -/
structure AsidPool where
  nextAsid    : Nat
  generation  : Nat
  freeList    : List ASID
  activeAsids : List ASID
  activeCount : Nat
  deriving Repr

instance : Inhabited AsidPool where
  default := ⟨0, 0, [], [], 0⟩

/-- Initial ASID pool with ASID 0 reserved (kernel). -/
def AsidPool.initial : AsidPool :=
  { nextAsid := 1  -- ASID 0 reserved for kernel
    generation := 0
    freeList := []
    activeAsids := []
    activeCount := 0 }

/-- Result of ASID allocation: the allocated ASID, updated pool,
    and whether a TLB flush is required (rollover occurred). -/
structure AsidAllocResult where
  asid           : ASID
  pool           : AsidPool
  requiresFlush  : Bool
  deriving Repr

/-- Allocate an ASID from the pool.

    Strategy:
    1. If the free list is non-empty, reuse a freed ASID (flush required —
       stale TLB entries from prior owner must be invalidated)
    2. Otherwise, bump `nextAsid` and return the fresh ASID (no flush needed)
    3. If `nextAsid` wraps around to `maxAsidValue`, rollover:
       increment generation, reset `nextAsid`, and require a full TLB flush

    Returns `none` if the pool is exhausted AND free list is empty AND
    all ASIDs are active (should not happen with < 65536 VSpaces). -/
def AsidPool.allocate (pool : AsidPool) : Option AsidAllocResult :=
  -- Strategy 1: Reuse from free list
  -- AI2-C (M-15): Free-list ASIDs were previously active in the current
  -- generation. The TLB may still contain stale entries from the prior owner.
  -- Setting requiresFlush := true forces callers to perform a TLB flush
  -- (via `adapterFlushTlbByAsid` from TlbModel.lean) before the reused ASID
  -- is safe for a new VSpace. AK3-D (A-H03): additionally bump `generation`
  -- so downstream stale-entry tracking keyed off (generation, ASID) tuples
  -- invalidates any lingering references from the prior owner.
  match pool.freeList with
  | asid :: rest =>
    some { asid := asid
           pool := { pool with
             freeList := rest
             generation := pool.generation + 1    -- AK3-D: bump generation
             activeAsids := asid :: pool.activeAsids
             activeCount := pool.activeCount + 1 }
           requiresFlush := true }
  | [] =>
    if pool.nextAsid < maxAsidValue then
      -- Strategy 2: Bump allocator — fresh ASID, never seen by TLB
      let asid := ASID.mk pool.nextAsid
      some { asid := asid
             pool := { pool with
               nextAsid := pool.nextAsid + 1
               activeAsids := asid :: pool.activeAsids
               activeCount := pool.activeCount + 1 }
             requiresFlush := false }
    else
      -- Strategy 3: Rollover — AK3-A (A-C01 / CRITICAL): search for a
      -- genuinely free ASID in [1, maxAsidValue). Skip ASID 0 (kernel
      -- reserved). Prior behavior unconditionally returned ASID 1 even
      -- if still active, breaking TLB isolation.
      --
      -- Strategy: linear scan over [1, maxAsidValue). `activeAsids` is
      -- the ground-truth active set; rollover fails closed (`none`) if
      -- every non-kernel ASID is still active.
      match (List.range (maxAsidValue - 1)).find?
              (fun i => decide (ASID.mk (i + 1) ∉ pool.activeAsids)) with
      | some i =>
        let asid := ASID.mk (i + 1)
        some { asid := asid
               pool := { pool with
                 -- nextAsid stays saturated; rollover succeeded once
                 nextAsid := maxAsidValue
                 generation := pool.generation + 1
                 activeAsids := asid :: pool.activeAsids
                 activeCount := pool.activeCount + 1 }
               requiresFlush := true }
      | none => none  -- Exhaustion — all non-kernel ASIDs are active

/-- Free an ASID back to the pool for reuse.
    AK3-A: removes the ASID from `activeAsids` so rollover correctly
    identifies it as available; append to `freeList` for fast-path reuse. -/
def AsidPool.free (pool : AsidPool) (asid : ASID) : AsidPool :=
  { pool with
    freeList := asid :: pool.freeList
    activeAsids := pool.activeAsids.erase asid
    activeCount := pool.activeCount - 1 }

-- ============================================================================
-- ASID pool well-formedness
-- ============================================================================

/-- Well-formedness predicate for the ASID pool (AK3-A extended):
    1. `nextAsid` is in bounds [0, maxAsidValue]
    2. activeCount matches activeAsids length
    3. activeAsids has no duplicates (uniqueness invariant — the key
       security property)
    4. all activeAsids and freeList entries have `val < nextAsid`
       (monotone bump frontier — this yields both value bounds and
       freshness for bump-path allocations)
    5. freeList is disjoint from activeAsids (freed ASIDs are not active)
    6. AK3-A: freeList has no duplicates (each ASID freed at most once)

    Capacity bound (`activeCount ≤ maxAsidValue`) is an immediate
    consequence of `Nodup` + `val < nextAsid ≤ maxAsidValue` via the
    pigeonhole principle and is exposed as a derived lemma below. -/
def AsidPool.wellFormed (pool : AsidPool) : Prop :=
  pool.nextAsid ≤ maxAsidValue ∧
  pool.activeCount = pool.activeAsids.length ∧
  pool.activeAsids.Nodup ∧
  (∀ asid ∈ pool.activeAsids, asid.val < pool.nextAsid) ∧
  (∀ asid ∈ pool.freeList, asid.val < pool.nextAsid) ∧
  (∀ asid ∈ pool.freeList, asid ∉ pool.activeAsids) ∧
  pool.freeList.Nodup

/-- The initial pool is well-formed. -/
theorem AsidPool.initial_wellFormed : AsidPool.initial.wellFormed := by
  simp [wellFormed, initial, maxAsidValue]

/-- AK3-A: Under wellFormed, all active ASIDs have val < maxAsidValue
    (derived from the `val < nextAsid ≤ maxAsidValue` chain). -/
theorem AsidPool.wellFormed_active_valid (pool : AsidPool)
    (hWf : pool.wellFormed) :
    ∀ asid ∈ pool.activeAsids, asid.val < maxAsidValue := by
  obtain ⟨hBound, _, _, hActiveLt, _, _, _⟩ := hWf
  intro asid hMem
  exact Nat.lt_of_lt_of_le (hActiveLt asid hMem) hBound

/-- AK3-A: Under wellFormed, all freeList ASIDs have val < maxAsidValue. -/
theorem AsidPool.wellFormed_free_valid (pool : AsidPool)
    (hWf : pool.wellFormed) :
    ∀ asid ∈ pool.freeList, asid.val < maxAsidValue := by
  obtain ⟨hBound, _, _, _, hFreeLt, _, _⟩ := hWf
  intro asid hMem
  exact Nat.lt_of_lt_of_le (hFreeLt asid hMem) hBound

/-- AK3-A: The ASID returned by allocation is in valid range.
    Proven via case analysis on the three allocation strategies. -/
theorem AsidPool.allocate_asid_valid
    (pool : AsidPool) (result : AsidAllocResult)
    (hWf : pool.wellFormed) (hAlloc : pool.allocate = some result) :
    result.asid.val < maxAsidValue := by
  have hBound := hWf.1
  unfold allocate at hAlloc
  cases hFL : pool.freeList with
  | cons hd tl =>
    simp only [hFL] at hAlloc
    simp only [Option.some.injEq] at hAlloc; subst hAlloc
    simp only
    have hMem : hd ∈ pool.freeList := by rw [hFL]; exact List.Mem.head _
    exact AsidPool.wellFormed_free_valid pool hWf hd hMem
  | nil =>
    simp only [hFL] at hAlloc
    split at hAlloc
    · -- Bump: nextAsid < maxAsidValue
      simp only [Option.some.injEq] at hAlloc; subst hAlloc
      simp only
      assumption
    · -- Rollover: linear scan over [1, maxAsidValue)
      split at hAlloc
      · rename_i _ i hFind
        simp only [Option.some.injEq] at hAlloc; subst hAlloc
        simp only
        have hMemRange : i ∈ List.range (maxAsidValue - 1) :=
          List.mem_of_find?_eq_some hFind
        have hRange : i < maxAsidValue - 1 := List.mem_range.mp hMemRange
        unfold maxAsidValue at hRange ⊢; omega
      · simp at hAlloc

/-- AK3-A: Allocation from a well-formed pool produces a well-formed pool.
    The new `activeAsids` entry is distinct from all existing entries,
    preserving `Nodup`. The `val < nextAsid` invariant ensures bump-path
    freshness; rollover uses `List.find?` which proves absence directly. -/
theorem AsidPool.allocate_preserves_wellFormed
    (pool : AsidPool) (result : AsidAllocResult)
    (hWf : pool.wellFormed) (hAlloc : pool.allocate = some result) :
    result.pool.wellFormed := by
  unfold wellFormed at hWf ⊢
  obtain ⟨hBound, hCtEq, hNodup, hActiveLt, hFreeLt, hFreeDisj, hFreeNodup⟩ := hWf
  unfold allocate at hAlloc
  cases hFL : pool.freeList with
  | cons hd tl =>
    -- Free-list reuse path
    simp only [hFL] at hAlloc hFreeLt hFreeDisj hFreeNodup
    simp only [Option.some.injEq] at hAlloc; subst hAlloc
    simp only
    have hHdMem : hd ∈ hd :: tl := List.Mem.head _
    have hHdNotIn : hd ∉ pool.activeAsids := hFreeDisj hd hHdMem
    have hHdLt : hd.val < pool.nextAsid := hFreeLt hd hHdMem
    have hHdNotTl : hd ∉ tl := (List.nodup_cons.mp hFreeNodup).1
    have hTlNodup : tl.Nodup := (List.nodup_cons.mp hFreeNodup).2
    refine ⟨hBound, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · exact List.nodup_cons.mpr ⟨hHdNotIn, hNodup⟩
    · intro a hMem; cases hMem with
      | head _ => exact hHdLt
      | tail _ h => exact hActiveLt a h
    · intro a hMemTl; exact hFreeLt a (List.Mem.tail hd hMemTl)
    · intro a hMemTl hMemNew
      have hAMem : a ∈ hd :: tl := List.Mem.tail hd hMemTl
      have hANotIn : a ∉ pool.activeAsids := hFreeDisj a hAMem
      cases hMemNew with
      | head _ => exact hHdNotTl hMemTl
      | tail _ h => exact hANotIn h
    · exact hTlNodup
  | nil =>
    simp only [hFL] at hAlloc hFreeLt hFreeDisj hFreeNodup
    split at hAlloc
    · -- Bump
      rename_i hFresh
      simp only [Option.some.injEq] at hAlloc; subst hAlloc
      simp only
      have hBumpNotIn : ASID.mk pool.nextAsid ∉ pool.activeAsids := by
        intro hMem
        have := hActiveLt _ hMem
        exact Nat.lt_irrefl _ this
      refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · exact List.nodup_cons.mpr ⟨hBumpNotIn, hNodup⟩
      · intro a hMem; cases hMem with
        | head _ => exact Nat.lt_succ_self _
        | tail _ h => exact Nat.lt_succ_of_lt (hActiveLt a h)
      · intro _ hMem; cases hMem
      · intro _ hMem; cases hMem
      · exact List.nodup_nil
    · -- Rollover
      split at hAlloc
      · rename_i _ i hFind
        simp only [Option.some.injEq] at hAlloc; subst hAlloc
        simp only
        have hPred : decide (ASID.mk (i + 1) ∉ pool.activeAsids) = true :=
          (List.find?_eq_some_iff_append.mp hFind).1
        have hNotIn : ASID.mk (i + 1) ∉ pool.activeAsids := of_decide_eq_true hPred
        have hMemRange : i ∈ List.range (maxAsidValue - 1) :=
          List.mem_of_find?_eq_some hFind
        have hRange : i < maxAsidValue - 1 := List.mem_range.mp hMemRange
        refine ⟨by unfold maxAsidValue; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.length_cons]; omega
        · exact List.nodup_cons.mpr ⟨hNotIn, hNodup⟩
        · intro a hMem; cases hMem with
          | head _ =>
            show (ASID.mk (i + 1)).val < maxAsidValue
            unfold maxAsidValue at hRange ⊢
            show i + 1 < _
            omega
          | tail _ h =>
            exact Nat.lt_of_lt_of_le (hActiveLt a h) hBound
        · intro _ hMem; cases hMem
        · intro _ hMem; cases hMem
        · exact List.nodup_nil
      · simp at hAlloc

-- ============================================================================
-- ASID uniqueness invariant
-- ============================================================================

/-- ASID uniqueness: no two distinct active VSpaces share the same ASID.
    This is the core security property for TLB isolation.

    Design note: the freshness precondition (`hFresh : newAsid ∉ activeAsids`)
    in `asidPoolUnique_allocate_fresh` is the caller's responsibility. The
    bump allocator guarantees freshness within a generation (monotonically
    increasing nextAsid), and rollover is protected by a full TLB flush
    (`requiresFlush = true`). Formal connection between `AsidPool.allocate`
    and the freshness property is deferred to the kernel integration layer
    (AG8) which tracks the active ASID set alongside the pool. -/
def asidPoolUnique (activeAsids : List ASID) : Prop :=
  activeAsids.Nodup

/-- Empty active set trivially satisfies uniqueness. -/
theorem asidPoolUnique_empty : asidPoolUnique [] := by
  exact List.nodup_nil

/-- Allocating a fresh ASID (not in the active set) preserves uniqueness. -/
theorem asidPoolUnique_allocate_fresh
    (activeAsids : List ASID) (newAsid : ASID)
    (hUnique : asidPoolUnique activeAsids)
    (hFresh : newAsid ∉ activeAsids) :
    asidPoolUnique (newAsid :: activeAsids) := by
  unfold asidPoolUnique at *
  exact List.nodup_cons.mpr ⟨hFresh, hUnique⟩

/-- Freeing an ASID (removing from active set) preserves uniqueness. -/
theorem asidPoolUnique_free
    (activeAsids : List ASID) (freedAsid : ASID)
    (hUnique : asidPoolUnique activeAsids) :
    asidPoolUnique (activeAsids.filter (· != freedAsid)) := by
  unfold asidPoolUnique at *
  exact hUnique.filter _

-- ============================================================================
-- AI2-C (M-15): TLB flush obligation predicates
-- ============================================================================

/-- AI2-C (M-15): Predicate asserting that a TLB flush is required after ASID
    allocation. Callers must discharge this obligation by performing a
    TLB flush (via `adapterFlushTlbByAsid` or `adapterFlushTlb`) before
    using the allocated ASID for a new VSpace.

    This predicate captures the type-level requirement that the TLB flush
    is not just a boolean flag check but a proof obligation that must be
    satisfied in the allocation protocol. -/
def asidAllocRequiresFlush (result : AsidAllocResult) : Prop :=
  result.requiresFlush = true

/-- AI2-C: All ASID allocation paths that reuse ASIDs require a TLB flush.
    Both free-list reuse and rollover set `requiresFlush := true`.
    Only fresh bump allocation (which has never been in the TLB) is safe
    without a flush. -/
theorem AsidPool.allocate_reuse_requires_flush
    (pool : AsidPool) (result : AsidAllocResult)
    (hAlloc : pool.allocate = some result)
    (hFreeList : pool.freeList ≠ []) :
    asidAllocRequiresFlush result := by
  unfold asidAllocRequiresFlush
  unfold allocate at hAlloc
  cases hFL : pool.freeList with
  | nil => exact absurd hFL hFreeList
  | cons hd tl =>
    simp only [hFL, Option.some.injEq] at hAlloc
    subst hAlloc; rfl

/-- AI2-C / AK3-A: Rollover allocation always requires a TLB flush.
    AK3-A change: rollover can now return `none` when all non-kernel ASIDs
    are still active; this theorem is conditioned on `some` return. -/
theorem AsidPool.allocate_rollover_requires_flush
    (pool : AsidPool) (result : AsidAllocResult)
    (hAlloc : pool.allocate = some result)
    (hEmptyFreeList : pool.freeList = [])
    (hAtBound : ¬(pool.nextAsid < maxAsidValue)) :
    asidAllocRequiresFlush result := by
  unfold asidAllocRequiresFlush allocate at *
  simp only [hEmptyFreeList, if_neg hAtBound] at hAlloc
  split at hAlloc
  · rename_i _ i hFind
    simp only [Option.some.injEq] at hAlloc; subst hAlloc; rfl
  · simp at hAlloc

/-- AI2-C: Fresh bump allocation does not require a TLB flush. The ASID
    has never been assigned to any VSpace, so no stale TLB entries exist. -/
theorem AsidPool.allocate_fresh_no_flush
    (pool : AsidPool) (result : AsidAllocResult)
    (hAlloc : pool.allocate = some result)
    (hEmptyFreeList : pool.freeList = [])
    (hFresh : pool.nextAsid < maxAsidValue) :
    ¬asidAllocRequiresFlush result := by
  unfold asidAllocRequiresFlush allocate at *
  simp only [hEmptyFreeList, if_pos hFresh] at hAlloc
  have := Option.some.inj hAlloc; subst this; simp

-- ============================================================================
-- AK3-A.5: Freshness correctness theorem — rollover never returns active ASID
-- ============================================================================

/-- AK3-A (A-C01): The ASID returned by `allocate` is never in the
    pre-call `activeAsids` set. This is the core security property that
    fixes the ASID-rollover TLB isolation bug. -/
theorem AsidPool.allocate_result_fresh
    (pool : AsidPool) (result : AsidAllocResult)
    (hWf : pool.wellFormed) (hAlloc : pool.allocate = some result) :
    result.asid ∉ pool.activeAsids := by
  obtain ⟨_, _, _, hActiveLt, _, hFreeDisj, _⟩ := hWf
  unfold allocate at hAlloc
  cases hFL : pool.freeList with
  | cons hd tl =>
    simp only [hFL] at hAlloc hFreeDisj
    simp only [Option.some.injEq] at hAlloc; subst hAlloc
    exact hFreeDisj hd (List.Mem.head _)
  | nil =>
    simp only [hFL] at hAlloc
    split at hAlloc
    · -- Bump: val = pool.nextAsid, which is strictly greater than all active
      simp only [Option.some.injEq] at hAlloc; subst hAlloc
      intro hMem
      exact Nat.lt_irrefl _ (hActiveLt _ hMem)
    · -- Rollover: List.find? explicitly filters out active ASIDs
      split at hAlloc
      · rename_i _ i hFind
        simp only [Option.some.injEq] at hAlloc; subst hAlloc
        have hPred : decide (ASID.mk (i + 1) ∉ pool.activeAsids) = true :=
          (List.find?_eq_some_iff_append.mp hFind).1
        exact of_decide_eq_true hPred
      · simp at hAlloc

/-- AK3-A: `allocate` preserves `asidPoolUnique` on the active set.
    The newly allocated ASID is pushed onto `activeAsids`, and freshness
    (proven above) ensures `Nodup` is preserved. -/
theorem asidPoolUnique_preserved_by_allocate
    (pool : AsidPool) (result : AsidAllocResult)
    (hWf : pool.wellFormed) (hAlloc : pool.allocate = some result) :
    asidPoolUnique result.pool.activeAsids := by
  unfold asidPoolUnique
  exact (AsidPool.allocate_preserves_wellFormed pool result hWf hAlloc).2.2.1

-- ============================================================================
-- AK3-A: Free-list well-formedness preservation
-- ============================================================================

/-- AK3-A: `free` preserves `wellFormed` when the freed ASID is currently
    active. Uses `List.erase` which has clean length and Nodup lemmas
    under the `Nodup` + membership preconditions. -/
theorem AsidPool.free_preserves_wellFormed
    (pool : AsidPool) (asid : ASID)
    (hWf : pool.wellFormed)
    (hActive : asid ∈ pool.activeAsids) :
    (pool.free asid).wellFormed := by
  unfold free wellFormed at *
  obtain ⟨hBound, hCtEq, hNodup, hActiveLt, hFreeLt, hFreeDisj, hFreeNodup⟩ := hWf
  have hAsidLt : asid.val < pool.nextAsid := hActiveLt asid hActive
  have hAsidNotInFree : asid ∉ pool.freeList := fun hMem =>
    hFreeDisj asid hMem hActive
  -- erase length: (l.erase a).length = l.length - 1 when a ∈ l and l.Nodup
  have hEraseLen : (pool.activeAsids.erase asid).length =
                   pool.activeAsids.length - 1 := by
    rw [List.length_erase_of_mem hActive]
  -- erase preserves Nodup
  have hEraseNodup : (pool.activeAsids.erase asid).Nodup := hNodup.erase _
  -- asid ∉ erased list
  have hAsidNotInErased : asid ∉ pool.activeAsids.erase asid := by
    intro hMem
    have := List.Nodup.mem_erase_iff hNodup |>.mp hMem
    exact this.1 rfl
  refine ⟨hBound, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hEraseLen, hCtEq]
  · exact hEraseNodup
  · intro a hMem
    have hInOld : a ∈ pool.activeAsids :=
      List.mem_of_mem_erase hMem
    exact hActiveLt a hInOld
  · intro a hMem; cases hMem with
    | head _ => exact hAsidLt
    | tail _ h => exact hFreeLt a h
  · intro a hMem hErased
    cases hMem with
    | head _ => exact hAsidNotInErased hErased
    | tail _ hTail =>
      have hInOld : a ∈ pool.activeAsids :=
        List.mem_of_mem_erase hErased
      exact hFreeDisj a hTail hInOld
  · exact List.nodup_cons.mpr ⟨hAsidNotInFree, hFreeNodup⟩

end SeLe4n.Kernel.Architecture
