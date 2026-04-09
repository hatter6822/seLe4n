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

/-- ASID allocation pool with bump allocator and generation tracking.
    - `nextAsid`: Next ASID to allocate (range [0, maxAsid))
    - `generation`: Increments on each rollover (full ASID space exhausted)
    - `freeList`: ASIDs returned by freed VSpaces, available for reuse
    - `activeCount`: Number of currently allocated ASIDs -/
structure AsidPool where
  nextAsid    : Nat
  generation  : Nat
  freeList    : List ASID
  activeCount : Nat
  deriving Repr

/-- Initial ASID pool with ASID 0 reserved (kernel). -/
def AsidPool.initial : AsidPool :=
  { nextAsid := 1  -- ASID 0 reserved for kernel
    generation := 0
    freeList := []
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
    1. If the free list is non-empty, reuse a freed ASID (no flush needed)
    2. Otherwise, bump `nextAsid` and return the fresh ASID
    3. If `nextAsid` wraps around to `maxAsidValue`, rollover:
       increment generation, reset `nextAsid`, and require a full TLB flush

    Returns `none` if the pool is exhausted AND free list is empty AND
    all ASIDs are active (should not happen with < 65536 VSpaces). -/
def AsidPool.allocate (pool : AsidPool) : Option AsidAllocResult :=
  -- Strategy 1: Reuse from free list
  match pool.freeList with
  | asid :: rest =>
    some { asid := asid
           pool := { pool with freeList := rest, activeCount := pool.activeCount + 1 }
           requiresFlush := false }
  | [] =>
    -- Guard: all ASIDs exhausted (should not happen with < 65536 VSpaces)
    if pool.activeCount ≥ maxAsidValue then
      none
    else if pool.nextAsid < maxAsidValue then
      -- Strategy 2: Bump allocator
      some { asid := ASID.mk pool.nextAsid
             pool := { pool with
               nextAsid := pool.nextAsid + 1
               activeCount := pool.activeCount + 1 }
             requiresFlush := false }
    else
      -- Strategy 3: Rollover — requires full TLB flush
      some { asid := ASID.mk 1  -- Start from 1 (0 is reserved)
             pool := { pool with
               nextAsid := 2
               generation := pool.generation + 1
               activeCount := pool.activeCount + 1 }
             requiresFlush := true }

/-- Free an ASID back to the pool for reuse. -/
def AsidPool.free (pool : AsidPool) (asid : ASID) : AsidPool :=
  { pool with
    freeList := asid :: pool.freeList
    activeCount := pool.activeCount - 1 }

-- ============================================================================
-- ASID pool well-formedness
-- ============================================================================

/-- Well-formedness predicate for the ASID pool:
    1. `nextAsid` is in bounds [0, maxAsidValue]
    2. All free list ASIDs are in valid range
    3. Active count is consistent -/
def AsidPool.wellFormed (pool : AsidPool) : Prop :=
  pool.nextAsid ≤ maxAsidValue ∧
  (∀ asid ∈ pool.freeList, asid.val < maxAsidValue) ∧
  pool.activeCount + pool.freeList.length ≤ maxAsidValue

/-- The initial pool is well-formed. -/
theorem AsidPool.initial_wellFormed : AsidPool.initial.wellFormed := by
  simp [wellFormed, initial, maxAsidValue]

/-- Allocation from a well-formed pool produces a well-formed pool.
    Proof via case analysis on the three allocation strategies. -/
theorem AsidPool.allocate_preserves_wellFormed
    (pool : AsidPool) (result : AsidAllocResult)
    (hWf : pool.wellFormed) (hAlloc : pool.allocate = some result) :
    result.pool.wellFormed := by
  unfold wellFormed at hWf ⊢
  obtain ⟨hBound, hFreeValid, hCount⟩ := hWf
  simp only [allocate] at hAlloc
  cases hFL : pool.freeList with
  | cons hd tl =>
    simp only [hFL] at hAlloc hFreeValid hCount
    simp only [Option.some.injEq] at hAlloc; subst hAlloc
    simp only
    refine ⟨hBound, ?_, ?_⟩
    · intro a hMem; exact hFreeValid a (List.mem_cons_of_mem hd hMem)
    · simp only [List.length_cons] at hCount; omega
  | nil =>
    simp only [hFL] at hAlloc hCount
    simp only [List.length_nil] at hCount
    split at hAlloc
    · -- Exhaustion guard: none returned, contradiction
      simp at hAlloc
    · split at hAlloc
      · -- Bump
        simp only [Option.some.injEq] at hAlloc; subst hAlloc
        simp only [List.length_nil]
        refine ⟨by omega, ?_, by omega⟩
        · intro _ hMem; simp at hMem
      · -- Rollover
        simp only [Option.some.injEq] at hAlloc; subst hAlloc
        simp only [List.length_nil]
        refine ⟨by unfold maxAsidValue; omega, ?_, by omega⟩
        · intro _ hMem; simp at hMem

/-- The ASID returned by allocation is in valid range. -/
theorem AsidPool.allocate_asid_valid
    (pool : AsidPool) (result : AsidAllocResult)
    (hWf : pool.wellFormed) (hAlloc : pool.allocate = some result) :
    result.asid.val < maxAsidValue := by
  obtain ⟨hBound, hFreeValid, _⟩ := hWf
  simp only [allocate] at hAlloc
  cases hFL : pool.freeList with
  | cons hd tl =>
    simp only [hFL] at hAlloc hFreeValid
    simp only [Option.some.injEq] at hAlloc; subst hAlloc
    simp only
    exact hFreeValid hd (List.Mem.head tl)
  | nil =>
    simp only [hFL] at hAlloc
    split at hAlloc
    · simp at hAlloc
    · split at hAlloc
      · -- Bump: nextAsid < maxAsidValue
        simp only [Option.some.injEq] at hAlloc; subst hAlloc
        simp only
        assumption
      · -- Rollover: ASID.mk 1, trivially < 65536
        simp only [Option.some.injEq] at hAlloc; subst hAlloc
        simp only [maxAsidValue]; omega

-- ============================================================================
-- ASID uniqueness invariant
-- ============================================================================

/-- ASID uniqueness: no two distinct active VSpaces share the same ASID.
    This is the core security property for TLB isolation. -/
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

end SeLe4n.Kernel.Architecture
