/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State

/-!
# AG8-B: Cache Coherency Model (H3-ARCH-07)

Abstract model of ARM64 data cache and instruction cache state. This module
provides the formal vocabulary for reasoning about cache coherency in the
context of page table modifications, self-modifying code, and DMA.

## Scope

This is a **specification-level** model. The Rust HAL layer (`cache.rs`)
provides the actual DC CIVAC / DC CVAC / DC IVAC / DC ZVA / IC IALLU
instructions. This Lean model captures:

1. Cache line state (invalid, clean, dirty)
2. D-cache and I-cache coherency predicates
3. Cache maintenance operation semantics
4. Preservation theorems for kernel operations

## Hardware Reference

Cortex-A76 (RPi5):
- L1 D-cache: 64 KB, 4-way, 64-byte lines
- L1 I-cache: 64 KB, 4-way, 64-byte lines
- L2 unified: 512 KB, 8-way, 64-byte lines

Cache maintenance is required:
- After page table modifications (DC CIVAC on PT pages, then TLBI + DSB + ISB)
- Before DMA reads (DC CIVAC to flush dirty lines)
- After DMA writes (DC IVAC to discard stale lines)
- For self-modifying code (DC CVAC + IC IALLU + ISB)

## Non-modeled aspects

- Cache associativity and replacement policy (abstracted away)
- Cache partitioning (MPAM — deferred to WS-W)
- Speculative prefetch effects
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Model

-- ============================================================================
-- Cache line state model
-- ============================================================================

/-- Cache line state per the MOESI-like protocol used by Cortex-A76.
Simplified to three abstract states sufficient for single-core H3. -/
inductive CacheLineState where
  /-- Line not present in cache. Read will fetch from memory. -/
  | invalid
  /-- Line present and matches memory. Safe to evict without writeback. -/
  | clean
  /-- Line present and modified. Memory is stale. Must writeback before
      eviction or before other agents (DMA, page table walker) read memory. -/
  | dirty
  deriving Repr, DecidableEq, BEq

/-- Abstract cache state. Maps physical addresses (at cache-line granularity)
to their cache line state. The abstract model uses function representation;
the hardware uses set-associative lookup. -/
structure CacheState where
  /-- D-cache line state per address (64-byte aligned). -/
  dcache : SeLe4n.PAddr → CacheLineState
  /-- I-cache line state per address (64-byte aligned). -/
  icache : SeLe4n.PAddr → CacheLineState

-- ============================================================================
-- Cache coherency predicates
-- ============================================================================

/-- D-cache coherent: every dirty line in the D-cache has been written back
to memory. Equivalently: no cache line is in the `dirty` state for any
address that has been modified since the last clean. -/
def dcacheCoherent (cs : CacheState) : Prop :=
  ∀ addr : SeLe4n.PAddr, cs.dcache addr ≠ .dirty

/-- I-cache coherent with memory: the I-cache contains no stale entries.
Every valid I-cache line matches the current memory content. In the abstract
model, this is captured by requiring no I-cache lines are present that were
fetched before a code modification (all `invalid` or matching memory). -/
def icacheCoherent (cs : CacheState) : Prop :=
  ∀ addr : SeLe4n.PAddr, cs.icache addr ≠ .dirty

/-- Full cache coherency: both D-cache and I-cache are coherent. This is the
invariant that must hold at kernel entry/exit boundaries and after any
operation that modifies page tables or executable code. -/
def cacheCoherent (cs : CacheState) : Prop :=
  dcacheCoherent cs ∧ icacheCoherent cs

-- ============================================================================
-- Cache maintenance operations (abstract model)
-- ============================================================================

/-- DC CVAC: Clean by VA to Point of Coherency.
Writes back the D-cache line containing `addr` to memory if dirty,
then marks it clean. Does not invalidate. -/
def dcClean (cs : CacheState) (addr : SeLe4n.PAddr) : CacheState :=
  { cs with dcache := fun a => if a = addr then
      match cs.dcache a with
      | .dirty => .clean
      | other => other
    else cs.dcache a }

/-- DC IVAC: Invalidate by VA to Point of Coherency.
Discards the D-cache line containing `addr`. If the line was dirty,
data is LOST (caller must clean first if data preservation needed). -/
def dcInvalidate (cs : CacheState) (addr : SeLe4n.PAddr) : CacheState :=
  { cs with dcache := fun a => if a = addr then .invalid else cs.dcache a }

/-- DC CIVAC: Clean and Invalidate by VA to Point of Coherency.
Writes back if dirty, then invalidates. This is the safe "flush" operation
that guarantees memory is up-to-date and the cache line is evicted. -/
def dcCleanInvalidate (cs : CacheState) (addr : SeLe4n.PAddr) : CacheState :=
  { cs with dcache := fun a => if a = addr then .invalid else cs.dcache a }

/-- IC IALLU: Invalidate all I-cache to Point of Unification.
Discards all I-cache lines, forcing re-fetch from memory on next
instruction fetch. Required after modifying executable code. -/
def icInvalidateAll (cs : CacheState) : CacheState :=
  { cs with icache := fun _ => .invalid }

/-- DC ZVA: Zero by VA. Allocates a cache line and zeros it without
reading memory. The line becomes dirty (contains zeros, memory may differ). -/
def dcZeroByVA (cs : CacheState) (addr : SeLe4n.PAddr) : CacheState :=
  { cs with dcache := fun a => if a = addr then .dirty else cs.dcache a }

-- ============================================================================
-- Default (empty) cache state
-- ============================================================================

/-- Default cache state: all lines invalid (cold cache). -/
def CacheState.empty : CacheState where
  dcache := fun _ => .invalid
  icache := fun _ => .invalid

-- ============================================================================
-- Preservation theorems
-- ============================================================================

/-- DC CIVAC on all addresses produces a fully D-cache coherent state.
In practice, the kernel only flushes specific ranges — this theorem
shows the property holds for individual lines. -/
theorem dcCleanInvalidate_makes_line_invalid (cs : CacheState) (addr : SeLe4n.PAddr) :
    (dcCleanInvalidate cs addr).dcache addr = .invalid := by
  simp [dcCleanInvalidate]

/-- IC IALLU produces a fully I-cache coherent state. -/
theorem icInvalidateAll_coherent (cs : CacheState) :
    icacheCoherent (icInvalidateAll cs) := by
  intro addr
  simp [icInvalidateAll]

/-- Empty cache is coherent. -/
theorem empty_cacheCoherent : cacheCoherent CacheState.empty := by
  constructor
  · intro addr; simp [CacheState.empty]
  · intro addr; simp [CacheState.empty]

/-- DC clean preserves I-cache state. Cache maintenance on D-cache
does not affect I-cache lines (they are separate structures). -/
theorem dcClean_preserves_icache (cs : CacheState) (addr : SeLe4n.PAddr) :
    (dcClean cs addr).icache = cs.icache := by
  simp [dcClean]

/-- DC CIVAC preserves I-cache state. -/
theorem dcCleanInvalidate_preserves_icache (cs : CacheState) (addr : SeLe4n.PAddr) :
    (dcCleanInvalidate cs addr).icache = cs.icache := by
  simp [dcCleanInvalidate]

/-- DC clean does not introduce dirty lines for other addresses. -/
theorem dcClean_frame (cs : CacheState) (addr other : SeLe4n.PAddr)
    (hNe : other ≠ addr) :
    (dcClean cs addr).dcache other = cs.dcache other := by
  simp [dcClean, hNe]

/-- DC CIVAC does not affect other addresses. -/
theorem dcCleanInvalidate_frame (cs : CacheState) (addr other : SeLe4n.PAddr)
    (hNe : other ≠ addr) :
    (dcCleanInvalidate cs addr).dcache other = cs.dcache other := by
  simp [dcCleanInvalidate, hNe]

/-- DC CVAC preserves D-cache coherency: cleaning a line can only transition
dirty→clean, which maintains the ≠dirty invariant for all addresses. -/
theorem dcClean_preserves_dcacheCoherent (cs : CacheState) (addr : SeLe4n.PAddr)
    (h : dcacheCoherent cs) :
    dcacheCoherent (dcClean cs addr) := by
  intro other
  simp only [dcClean]
  split
  · -- other = addr
    subst_vars
    split <;> simp_all
  · -- other ≠ addr
    exact h other

/-- DC CIVAC preserves D-cache coherency: invalidating a line produces
`.invalid`, which trivially satisfies ≠dirty. -/
theorem dcCleanInvalidate_preserves_dcacheCoherent (cs : CacheState) (addr : SeLe4n.PAddr)
    (h : dcacheCoherent cs) :
    dcacheCoherent (dcCleanInvalidate cs addr) := by
  intro other
  simp only [dcCleanInvalidate]
  split
  · simp
  · exact h other

-- ============================================================================
-- DC IVAC (dcInvalidate) theorems
-- ============================================================================

/-- DC IVAC makes the target line invalid. -/
theorem dcInvalidate_makes_line_invalid (cs : CacheState) (addr : SeLe4n.PAddr) :
    (dcInvalidate cs addr).dcache addr = .invalid := by
  simp [dcInvalidate]

/-- DC IVAC does not affect other addresses (frame). -/
theorem dcInvalidate_frame (cs : CacheState) (addr other : SeLe4n.PAddr)
    (hNe : other ≠ addr) :
    (dcInvalidate cs addr).dcache other = cs.dcache other := by
  simp [dcInvalidate, hNe]

/-- DC IVAC preserves I-cache state (separate structure). -/
theorem dcInvalidate_preserves_icache (cs : CacheState) (addr : SeLe4n.PAddr) :
    (dcInvalidate cs addr).icache = cs.icache := by
  simp [dcInvalidate]

/-- DC IVAC preserves D-cache coherency: invalidating a line produces
`.invalid`, which satisfies ≠dirty. -/
theorem dcInvalidate_preserves_dcacheCoherent (cs : CacheState) (addr : SeLe4n.PAddr)
    (h : dcacheCoherent cs) :
    dcacheCoherent (dcInvalidate cs addr) := by
  intro other
  simp only [dcInvalidate]
  split
  · simp
  · exact h other

-- ============================================================================
-- DC ZVA (dcZeroByVA) theorems
-- ============================================================================

/-- DC ZVA does not affect other addresses (frame). -/
theorem dcZeroByVA_frame (cs : CacheState) (addr other : SeLe4n.PAddr)
    (hNe : other ≠ addr) :
    (dcZeroByVA cs addr).dcache other = cs.dcache other := by
  simp [dcZeroByVA, hNe]

/-- DC ZVA preserves I-cache state (separate structure). -/
theorem dcZeroByVA_preserves_icache (cs : CacheState) (addr : SeLe4n.PAddr) :
    (dcZeroByVA cs addr).icache = cs.icache := by
  simp [dcZeroByVA]

/-- DC ZVA introduces a dirty line at the target address. This is the only
operation that can BREAK `dcacheCoherent` — the caller must clean/invalidate
afterwards if coherency is required. -/
theorem dcZeroByVA_makes_line_dirty (cs : CacheState) (addr : SeLe4n.PAddr) :
    (dcZeroByVA cs addr).dcache addr = .dirty := by
  simp [dcZeroByVA]

-- ============================================================================
-- Composed protocol theorems
-- ============================================================================

/-- Page table update protocol: after DC CIVAC on a page table page followed
by IC IALLU, the resulting cache state is I-cache coherent.

**Note**: In this abstract model, the I-cache coherency conclusion depends
only on `icInvalidateAll` (which unconditionally sets all I-cache lines to
`.invalid`). The `dcCleanInvalidate` step is required on hardware to ensure
the D-cache writes back to memory before the I-cache refetches, but this
D→memory→I relationship is not captured in the current 3-state model (see
module header "Non-modeled aspects"). The composed statement documents the
required protocol even though the formal proof only uses the IC IALLU step. -/
theorem pageTableUpdate_icache_coherent (cs : CacheState) (ptAddr : SeLe4n.PAddr) :
    icacheCoherent (icInvalidateAll (dcCleanInvalidate cs ptAddr)) := by
  exact icInvalidateAll_coherent _

end SeLe4n.Kernel.Architecture
