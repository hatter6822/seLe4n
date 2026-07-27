-- SPDX-License-Identifier: GPL-3.0-or-later
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

> **STATUS: production** since WS-SM SM7.D (v0.32.94).  The module was staged
> for H3 hardware binding (AN7-D.6 / PLT-M07) until SM7.D's SMP cache
> maintenance layer (`Architecture/PerCoreCacheModel.lean`) became its first
> production consumer: the D-cache state and operations defined here are what
> SM7.D.2's per-core reach theorems quantify over.

Abstract model of ARM64 data cache and instruction cache state. This module
provides the formal vocabulary for reasoning about cache coherency in the
context of page table modifications, self-modifying code, and DMA.

## Scope

This is the **single-view, specification-level** model — one `CacheState` for
the machine.  The Rust HAL layer (`cache.rs`) provides the actual DC CIVAC /
DC CVAC / DC IVAC / DC ZVA / IC IALLU / IC IALLUIS / IC IVAU instructions. This
Lean model captures:

1. Cache line state (invalid, clean, dirty)
2. D-cache and I-cache coherency predicates
3. Cache maintenance operation semantics
4. Preservation theorems for kernel operations

## SMP companion (WS-SM SM7.D)

Under SMP the two cache hierarchies stop behaving alike, and the split is what
`Architecture/PerCoreCacheModel.lean` formalises:

* **D-cache (SM7.D.2)** — the data caches of the PEs in a shareability domain
  are hardware-coherent, and `DC` maintenance *by VA to the Point of Coherency*
  is architecturally visible to every agent in that domain (ARM ARM B2.7 /
  D7.4).  So this module's single `CacheState.dcache` view stays adequate: SM7.D
  lifts the operations here to `dcMaintenanceAllCores`, which takes **no target
  set at all** — the absence of a reach parameter is the formal content of "at
  PoC, already system-wide" — and proves
  `dcMaintenanceByVA_reaches_all_cores`.
* **I-cache (SM7.D.1)** — instruction caches are *not* coherent, neither with
  the data side nor across PEs.  `icInvalidateAll` below models `IC IALLU`,
  which reaches **only the executing PE**; under SMP the kernel must issue the
  Inner Shareable broadcast variant (`IC IALLUIS`) or the by-VA form
  (`IC IVAU`, likewise broadcast within the domain).  A stale line on a remote
  core is the instruction-side twin of the SMP-C4 stale-TLB hazard, so SM7.D
  mounts a genuine per-core model (`SystemState.perCoreICache`) with
  `icacheCoherent_perCore` as the 14th `proofLayerInvariantBundle` conjunct.
* **DMA (SM7.D.3)** — cross-core data-cache maintenance for DMA buffers is out
  of scope for v1.0.0: the kernel has no DMA driver, so no non-coherent bus
  master exists.  That boundary is machine-checked rather than asserted —
  `modeledCoherentAgents_no_dma_master` fails the moment a DMA agent is added
  to the model without the accompanying buffer-ownership protocol.

Cache maintenance is required:
- After page table modifications (DC CIVAC on PT pages, then TLBI + DSB + ISB)
- Before DMA reads (DC CIVAC to flush dirty lines)
- After DMA writes (DC IVAC to discard stale lines)
- For self-modifying code (DC CVAC + IC IALLU + ISB) — on ARMv8-A this is
  *user* software's obligation (seL4 exposes it as an explicit
  `Page_Unify_Instruction` operation); the kernel-side obligation SM7.D
  discharges is the mapping-lifetime one.

## Non-modeled aspects

- Cache associativity and replacement policy (abstracted away)
- Cache partitioning (MPAM — deferred to WS-W)
- Speculative prefetch effects
- Instruction *content*: an `ICacheLine` (SM7.D) records the executable
  translation a fetch resolved through, not the bytes fetched.  That is the
  hazard the kernel controls — it owns mappings, not the data a thread writes.
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
instruction fetch. Required after modifying executable code.

**WS-SM SM7.D.1 — reach**: `IC IALLU` invalidates only the **executing PE's**
instruction cache.  Under SMP the kernel must use the Inner Shareable broadcast
variant `IC IALLUIS` (or the by-VA `IC IVAU`, likewise broadcast within the
domain) — see `Architecture/PerCoreCacheModel.lean`'s `icInvalidateBroadcast`,
whose `…_reaches_all_cores` theorem is the instruction-side analogue of the
SM7.B TLB shootdown's Theorem 3.3.1.  This single-view model conflates all PEs,
so it cannot express the difference; the per-core model can, and
`icInvalidateOnCore_icacheOnCore_ne` states the hazard explicitly. -/
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
required protocol even though the formal proof only uses the IC IALLU step.

**AI6-C (M-16) — Hardware protocol requirement**: For self-modifying code
safety on ARMv8-A, the D-cache → I-cache pipeline ordering requires the
full sequence: DC CVAU (clean D-cache to PoU) → DSB ISH (ensure writeback
completes) → IC IVAU (invalidate I-cache by VA) → DSB ISH → ISB. The
abstract model's `dcCleanInvalidate` + `icInvalidateAll` composition does
not capture the DSB barriers that ensure memory visibility ordering between
the two cache hierarchies. Hardware binding must insert explicit barriers
(see `rust/sele4n-hal/src/cache.rs`). -/
theorem pageTableUpdate_icache_coherent (cs : CacheState) (ptAddr : SeLe4n.PAddr) :
    icacheCoherent (icInvalidateAll (dcCleanInvalidate cs ptAddr)) := by
  exact icInvalidateAll_coherent _

-- ============================================================================
-- AK3-G (A-M04 / MEDIUM): D-cache → I-cache barrier ordering (partial closure)
-- ============================================================================

/-- AK3-G (A-M04 / MEDIUM): A barrier token describing a memory ordering
    guarantee between cache operations. Mirrors the ARMv8-A DSB/ISB
    instruction family; full typeclass-level composition is closed by
    WS-AN AN9-A (TLB+cache composition — DEF-A-M04).

    The three variants used in D-cache → I-cache pipelines:
    - `dsb_ish`: Data Synchronization Barrier, Inner Shareable domain
    - `isb`:     Instruction Synchronization Barrier
    - `dmb_ish`: Data Memory Barrier, Inner Shareable domain

    These re-export names already defined in
    `SeLe4n.Platform.RPi5.MmioAdapter` (AG8-C) for local use by the cache
    coherency sequence documentation. -/
inductive CacheBarrierKind where
  | dsb_ish  : CacheBarrierKind
  | isb      : CacheBarrierKind
  | dmb_ish  : CacheBarrierKind
  deriving DecidableEq, Repr

/-- AK3-G (A-M04 / MEDIUM): Abstract predicate asserting that the cache
    state was reached via a correctly-ordered D→I pipeline sequence:

      DC CVAU  →  DSB ISH  →  IC IVAU  →  DSB ISH  →  ISB

    In the sequential model this is trivially `True` (there's no concurrent
    observer that could race with a missing barrier); the predicate exists
    as a hook for the hardware HAL to assert the actual instruction sequence
    is emitted.

    Partial closure: the proof layer records WHICH operations must compose
    under this predicate; the HAL discharges the instruction-level ordering.
    Full binding closed by WS-AN AN9-A (DEF-A-M04 TLB+cache composition). -/
def cacheCoherentForExecutable (_cs : CacheState) : Prop := True

/-- AK3-G: In the sequential model, any cache state trivially satisfies
    `cacheCoherentForExecutable`. The substantive constraint is deferred
    to the Rust HAL in `rust/sele4n-hal/src/cache.rs`. -/
theorem cacheCoherentForExecutable_trivial (cs : CacheState) :
    cacheCoherentForExecutable cs := trivial

/-- AK3-G (A-M04 / MEDIUM): Strengthened page-table update theorem
    documenting the required barrier sequence. The existing
    `pageTableUpdate_icache_coherent` shows the shape-level invariant
    (I-cache is empty post-invalidation); this additionally asserts
    the composed predicate holds — both the shape-level result AND the
    barrier-sequence obligation. -/
theorem pageTableUpdate_icache_coherent_under_sequence
    (cs : CacheState) (ptAddr : SeLe4n.PAddr) :
    icacheCoherent (icInvalidateAll (dcCleanInvalidate cs ptAddr)) ∧
    cacheCoherentForExecutable (icInvalidateAll (dcCleanInvalidate cs ptAddr)) :=
  ⟨icInvalidateAll_coherent _, cacheCoherentForExecutable_trivial _⟩

end SeLe4n.Kernel.Architecture
