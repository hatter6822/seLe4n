-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Prelude

/-!
# WS-SM SM7.D.1 — Typed instruction-cache maintenance operand

The pure `ICacheInvalidation` inductive, its FFI tag/operand encoders, and its
join-semilattice, extracted from `PerCoreCacheModel.lean` so that state-layer
consumers can name an instruction-cache maintenance operation **without**
pulling the per-core cache model's import closure.

This mirrors, one-for-one, the reason `TlbInvalidation.lean` was extracted from
`TlbiForSharing.lean` at SM7.A: `Model/State.lean` mounts the SM7.D.1 pending
maintenance ledger (`SystemState.pendingIcacheMaintenance`), whose payload is an
`ICacheInvalidation`, and `Model/State.lean` sits far below the architecture
layer in the import graph.

Everything here is pure data plus `rfl`- and `decide`-class theorems; the
per-core cache *model* (`icacheLineMatches`, `applyICacheInvalidation`,
`icInvalidateBroadcast`, …) stays in `PerCoreCacheModel.lean`, which imports
this module.  All definitions keep their fully-qualified names
(`SeLe4n.Kernel.Architecture.ICacheInvalidation…`), so every pre-existing
consumer and surface anchor resolves unchanged.

## Encoding contract

The op-tag/operand encoding **MUST** stay in lockstep with
`rust/sele4n-hal/src/ffi.rs::cache_ic_maintenance` and
`rust/sele4n-hal/src/cache.rs::decode_icache_invalidation`:

  opTag : 0 = Iallu (invalidate all), 1 = IvauPage (invalidate one page)
  paddr : page-aligned physical address (RES0 for Iallu)

A future encoding change requires updating the Rust `match` arms, the encoders
here, and the `tests/SmpCacheMaintenanceSuite.lean` runtime checks in the same
PR.

## Granularity contract (ARM ARM C6.2.88)

`IC IVAU` invalidates **one cache line** — 64 bytes on Cortex-A76 — not one
page.  The model's operand is deliberately *page*-granular, because that is the
granularity at which the kernel reasons (a `VSpaceRoot.lookup` yields a page
base, and mappings are created and destroyed per page).  The HAL therefore
**expands** one `ivauPage` operand into `icacheLinesPerPage` consecutive
`IC IVAU` instructions followed by a single `DSB ISH` + `ISB`
(`cache::ic_invalidate_page_inner_shareable`), exactly as seL4's
`invalidateCacheRange_I` does.  `icacheLinesPerPage_covers_page` below pins the
arithmetic on the Lean side; `test_ic_invalidate_page_line_count` pins it on the
Rust side.  Naming the constructor `ivauPage` rather than `ivau` is deliberate:
a reader must not infer single-line semantics from the model's operand.
-/

namespace SeLe4n.Kernel.Architecture

/-- **WS-SM SM7.D.1**: ARMv8-A 4 KiB translation granule, in bytes.  The unit
the kernel's mappings — and hence the SM7.D maintenance operands — are
expressed in. -/
def pageBytes : Nat := 4096

/-- **WS-SM SM7.D.1**: Cortex-A76 instruction/data cache line size, in bytes
(from `CTR_EL0`).  Pinned against `rust/sele4n-hal/src/cache.rs`'s
`CACHE_LINE_SIZE`. -/
def cacheLineBytes : Nat := 64

/-- **WS-SM SM7.D.1**: how many `IC IVAU` instructions the HAL must issue to
cover one page.  The expansion factor between the model's page-granular operand
and the architecture's line-granular instruction. -/
def icacheLinesPerPage : Nat := pageBytes / cacheLineBytes

/-- **WS-SM SM7.D.1** (the granularity contract, machine-checked): the HAL's
per-page `IC IVAU` loop covers exactly one page — no line of the page is
skipped, and no line beyond it is touched.  A change to either constant that
broke the division would fail here rather than silently under-invalidating. -/
theorem icacheLinesPerPage_covers_page :
    icacheLinesPerPage * cacheLineBytes = pageBytes := by decide

/-- **WS-SM SM7.D.1**: the concrete expansion factor on this platform. -/
theorem icacheLinesPerPage_eq : icacheLinesPerPage = 64 := by decide

/-- **WS-SM SM7.D.1**: typed instruction-cache maintenance selector, mirroring
`TlbInvalidation`'s design (SM1.E.4) for the instruction side.

* `iallu`          — `IC IALLU{IS}`: invalidate the entire instruction cache to
  the Point of Unification.  No operand.
* `ivauPage paddr` — invalidate every instruction-cache line of the 4 KiB page
  based at `paddr`, to the Point of Unification.  ARMv8-A instruction caches
  behave as PIPT to software (ARM ARM D7.2), so the operand that decides *which*
  lines are hit is the **physical** address; the `IC IVAU` instruction itself
  takes a VA and the hardware translates it.  See the module header's
  granularity contract: the HAL expands this into `icacheLinesPerPage`
  instructions.

The *reach* of an operation — this PE only, or every PE in the shareability
domain — is **not** part of the operand: it is the difference between
`icInvalidateOnCore` and `icInvalidateBroadcast`, exactly as SM1.E separates
`TlbInvalidation` from the `SharingDomain`-tagged dispatcher. -/
inductive ICacheInvalidation where
  /-- `IC IALLU{IS}` — invalidate every instruction-cache line. -/
  | iallu
  /-- Invalidate every instruction-cache line of the page based at `paddr`
      (expanded by the HAL into `icacheLinesPerPage` `IC IVAU` instructions). -/
  | ivauPage (paddr : SeLe4n.PAddr)
  deriving DecidableEq, Repr, Inhabited

/-- **WS-SM SM7.D.1**: encode an `ICacheInvalidation` to its FFI op tag.
`0 = Iallu`, `1 = IvauPage`; the operand is carried by
`ICacheInvalidation.toPaddr` (`0` for the operand-free variant). -/
@[inline] def ICacheInvalidation.toOpTag : ICacheInvalidation → UInt32
  | .iallu      => 0
  | .ivauPage _ => 1

/-- **WS-SM SM7.D.1**: extract the physical-address operand, returning `0` for
the operand-free `iallu`. -/
@[inline] def ICacheInvalidation.toPaddr : ICacheInvalidation → UInt64
  | .iallu        => 0
  | .ivauPage p   => UInt64.ofNat p.toNat

/-- **WS-SM SM7.D.1**: `toOpTag` produces every value in `[0, 2)` — the
bound the Rust dispatcher's two-arm match relies on. -/
theorem ICacheInvalidation.toOpTag_in_range (op : ICacheInvalidation) :
    op.toOpTag.toNat < 2 := by
  cases op <;> simp [ICacheInvalidation.toOpTag]

/-- **WS-SM SM7.D.1**: distinct constructors map to distinct op tags — the
structural witness that the Rust match arms cover the enum without overlap. -/
theorem ICacheInvalidation.toOpTag_distinct_constructors :
    ICacheInvalidation.iallu.toOpTag ≠
      (ICacheInvalidation.ivauPage (SeLe4n.PAddr.ofNat 0)).toOpTag := by
  decide

/-- **WS-SM SM7.D.1**: `iallu` encodes to op tag 0. -/
theorem ICacheInvalidation.iallu_opTag : ICacheInvalidation.iallu.toOpTag = 0 := rfl
/-- **WS-SM SM7.D.1**: `ivauPage` encodes to op tag 1. -/
theorem ICacheInvalidation.ivauPage_opTag (p : SeLe4n.PAddr) :
    (ICacheInvalidation.ivauPage p).toOpTag = 1 := rfl
/-- **WS-SM SM7.D.1**: `iallu` carries a zero operand. -/
theorem ICacheInvalidation.iallu_zero_operand :
    ICacheInvalidation.iallu.toPaddr = 0 := rfl
/-- **WS-SM SM7.D.1**: `ivauPage p` carries `p` as its physical-address
operand. -/
theorem ICacheInvalidation.ivauPage_toPaddr (p : SeLe4n.PAddr) :
    (ICacheInvalidation.ivauPage p).toPaddr = UInt64.ofNat p.toNat := rfl

-- ============================================================================
-- SM7.D.1 — The operand join (the pending-maintenance ledger's algebra)
-- ============================================================================

/-- **WS-SM SM7.D.1**: the join of two maintenance operands — the weakest
operand that is at least as strong as both.

`iallu` is the top element; two page operands join to themselves when equal and
to `iallu` otherwise (the model has no multi-page operand, and collapsing to the
full invalidate is the *sound* direction — over-invalidation costs re-fetches,
under-invalidation is the hazard).  This is the same
collapse-to-the-strongest-operand discipline as SM7.A's
`enqueueShootdownOrCoalesce`, and it is what makes
`SystemState.pendingIcacheMaintenance` a single `Option` with no capacity
bound to thread. -/
def ICacheInvalidation.join : ICacheInvalidation → ICacheInvalidation →
    ICacheInvalidation
  | .iallu, _ => .iallu
  | _, .iallu => .iallu
  | .ivauPage p, .ivauPage q => if p = q then .ivauPage p else .iallu

/-- **WS-SM SM7.D.1**: the join is idempotent. -/
@[simp] theorem ICacheInvalidation.join_self (op : ICacheInvalidation) :
    op.join op = op := by
  cases op <;> simp [ICacheInvalidation.join]

/-- **WS-SM SM7.D.1**: `iallu` absorbs on the left. -/
@[simp] theorem ICacheInvalidation.iallu_join (op : ICacheInvalidation) :
    ICacheInvalidation.iallu.join op = .iallu := rfl

/-- **WS-SM SM7.D.1**: `iallu` absorbs on the right. -/
@[simp] theorem ICacheInvalidation.join_iallu (op : ICacheInvalidation) :
    op.join .iallu = .iallu := by
  cases op <;> rfl

/-- **WS-SM SM7.D.1**: the join is commutative — the ledger's accumulation
order is a convention, not a semantic choice. -/
theorem ICacheInvalidation.join_comm (a b : ICacheInvalidation) :
    a.join b = b.join a := by
  cases a <;> cases b <;> simp only [ICacheInvalidation.join] <;>
    split <;> rename_i h <;> simp_all [eq_comm]

/-- **WS-SM SM7.D.1**: accumulate one operand into the pending-maintenance
ledger.  `none` (nothing owed yet) absorbs the operand; an existing entry joins
with it. -/
def joinIcacheMaintenance : Option ICacheInvalidation → ICacheInvalidation →
    Option ICacheInvalidation
  | none,   op => some op
  | some a, op => some (a.join op)

/-- **WS-SM SM7.D.1**: accumulating into an empty ledger records the operand
exactly — the case every live seam hits (one broadcast per syscall), so the
runtime emits the model's *precise* operand, not a collapsed one. -/
@[simp] theorem joinIcacheMaintenance_none (op : ICacheInvalidation) :
    joinIcacheMaintenance none op = some op := rfl

/-- **WS-SM SM7.D.1**: the ledger is never emptied by accumulation — once a
transition owes maintenance, the ledger holds an operand until the runtime
drains it. -/
theorem joinIcacheMaintenance_isSome (l : Option ICacheInvalidation)
    (op : ICacheInvalidation) : (joinIcacheMaintenance l op).isSome := by
  cases l <;> rfl

end SeLe4n.Kernel.Architecture
