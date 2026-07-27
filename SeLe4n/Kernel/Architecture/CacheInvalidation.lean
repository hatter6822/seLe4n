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

  opTag : 0 = Iallu (invalidate all), 1 = IvauPage (invalidate one page),
          2 = UnifyPage (clean D-cache to PoU, then invalidate one page)
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
  /-- **WS-SM SM7.D**: unify the instruction and data views of the page based at
      `paddr` — the full ARMv8-A data-to-instruction sequence `DC CVAU` →
      `DSB ISH` → `IC IVAU` → `DSB ISH` → `ISB`, over the whole page.

      The *removal* semantics are `ivauPage`'s: the same lines disappear.  What
      differs is the emitted sequence, which additionally pushes the page's
      **stores** to the Point of Unification first — necessary when the memory
      was just written (freshly loaded or JIT-generated code), because an
      instruction fetch reads at PoU and would otherwise observe the old
      content, even on the PE that performed the store.  (`TlbInvalidation`
      likewise distinguishes `vae1` from `vale1`, which agree on which entries
      they retire and differ only in the instruction emitted.)

      This is the operand of the `.vspaceUnifyInstruction` syscall — seLe4n's
      equivalent of seL4's `Page_Unify_Instruction`, and the mechanism by which
      user software discharges the code-modification obligation ARMv8-A places
      on it. -/
  | unifyPage (paddr : SeLe4n.PAddr)
  deriving DecidableEq, Repr, Inhabited

/-- **WS-SM SM7.D.1**: encode an `ICacheInvalidation` to its FFI op tag.
`0 = Iallu`, `1 = IvauPage`; the operand is carried by
`ICacheInvalidation.toPaddr` (`0` for the operand-free variant). -/
@[inline] def ICacheInvalidation.toOpTag : ICacheInvalidation → UInt32
  | .iallu       => 0
  | .ivauPage _  => 1
  | .unifyPage _ => 2

/-- **WS-SM SM7.D.1**: extract the physical-address operand, returning `0` for
the operand-free `iallu`. -/
@[inline] def ICacheInvalidation.toPaddr : ICacheInvalidation → UInt64
  | .iallu        => 0
  | .ivauPage p   => UInt64.ofNat p.toNat
  | .unifyPage p  => UInt64.ofNat p.toNat

/-- **WS-SM SM7.D.1**: `toOpTag` produces every value in `[0, 3)` — the
bound the Rust dispatcher's three-arm match relies on. -/
theorem ICacheInvalidation.toOpTag_in_range (op : ICacheInvalidation) :
    op.toOpTag.toNat < 3 := by
  cases op <;> simp [ICacheInvalidation.toOpTag]

/-- **WS-SM SM7.D.1**: distinct constructors map to distinct op tags — the
structural witness that the Rust match arms cover the enum without overlap. -/
theorem ICacheInvalidation.toOpTag_distinct_constructors :
    (ICacheInvalidation.iallu.toOpTag ≠
      (ICacheInvalidation.ivauPage (SeLe4n.PAddr.ofNat 0)).toOpTag) ∧
    (ICacheInvalidation.iallu.toOpTag ≠
      (ICacheInvalidation.unifyPage (SeLe4n.PAddr.ofNat 0)).toOpTag) ∧
    ((ICacheInvalidation.ivauPage (SeLe4n.PAddr.ofNat 0)).toOpTag ≠
      (ICacheInvalidation.unifyPage (SeLe4n.PAddr.ofNat 0)).toOpTag) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

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
/-- **WS-SM SM7.D**: `unifyPage` encodes to op tag 2. -/
theorem ICacheInvalidation.unifyPage_opTag (p : SeLe4n.PAddr) :
    (ICacheInvalidation.unifyPage p).toOpTag = 2 := rfl
/-- **WS-SM SM7.D**: `unifyPage p` carries `p` as its physical-address
operand. -/
theorem ICacheInvalidation.unifyPage_toPaddr (p : SeLe4n.PAddr) :
    (ICacheInvalidation.unifyPage p).toPaddr = UInt64.ofNat p.toNat := rfl

-- ============================================================================
-- SM7.D.1 — The ledger's algebra: a *coverage* preorder, not a join
-- ============================================================================

/-- **WS-SM SM7.D**: `a.covers b` — performing `a` discharges everything `b`
would have discharged.

This replaces the earlier single-operand *join*.  A join needs a top element,
and the obvious candidate — `iallu` (`IC IALLUIS`, invalidate every instruction
cache in the domain) — is **not** one: it invalidates instruction caches but
performs no `DC CVAU`, so it does not discharge a `unifyPage`'s clean to the
Point of Unification.  Collapsing `unifyPage p` into `iallu` would drop that
clean and leave a freshly written instruction fetchable in its *old* form —
an under-maintenance, the one direction that is unsafe.  Since there is also
no single operand covering two distinct `unifyPage`s, the maintenance owed by a
state is fundamentally a *list*, and this relation is only what lets the ledger
drop an entry that a later one already subsumes.

The relation is deliberately conservative: it holds only where the emitted
instruction sequence provably does at least as much.
- `iallu` covers `iallu` and any `ivauPage` (a domain-wide invalidate subsumes
  a page invalidate) but **not** `unifyPage` (no clean).
- `ivauPage p` covers only `ivauPage p`.
- `unifyPage p` covers `unifyPage p` and `ivauPage p` (same lines invalidated,
  plus the clean) but not `iallu` (narrower invalidation scope). -/
def ICacheInvalidation.covers : ICacheInvalidation → ICacheInvalidation → Bool
  | .iallu,       .iallu       => true
  | .iallu,       .ivauPage _  => true
  | .iallu,       .unifyPage _ => false
  | .ivauPage p,  .ivauPage q  => p == q
  | .ivauPage _,  .iallu       => false
  | .ivauPage _,  .unifyPage _ => false
  | .unifyPage p, .unifyPage q => p == q
  | .unifyPage p, .ivauPage q  => p == q
  | .unifyPage _, .iallu       => false

/-- **WS-SM SM7.D**: coverage is reflexive — re-recording the same operand
records nothing new. -/
@[simp] theorem ICacheInvalidation.covers_refl (op : ICacheInvalidation) :
    op.covers op = true := by
  cases op <;> simp [ICacheInvalidation.covers]

/-- **WS-SM SM7.D**: `iallu` covers every *invalidation* operand. -/
@[simp] theorem ICacheInvalidation.iallu_covers_ivauPage (p : SeLe4n.PAddr) :
    ICacheInvalidation.iallu.covers (.ivauPage p) = true := rfl

/-- **WS-SM SM7.D**: `unifyPage` covers the bare invalidate of the same page —
the clean-then-invalidate sequence does strictly more. -/
@[simp] theorem ICacheInvalidation.unifyPage_covers_ivauPage (p : SeLe4n.PAddr) :
    (ICacheInvalidation.unifyPage p).covers (.ivauPage p) = true := by
  simp [ICacheInvalidation.covers]

/-- **WS-SM SM7.D**: the defect this design exists to rule out — `iallu` does
**not** cover a `unifyPage`.  `IC IALLUIS` invalidates instruction caches; it
issues no `DC CVAU`, so a store still sitting in a data cache is not pushed to
the Point of Unification and a later fetch reads the stale content.  Stated as
a theorem so a future "simplification" that makes `iallu` a top element fails
here rather than silently under-maintaining. -/
theorem ICacheInvalidation.iallu_not_covers_unifyPage (p : SeLe4n.PAddr) :
    ICacheInvalidation.iallu.covers (.unifyPage p) = false := rfl

/-- **WS-SM SM7.D**: distinct pages are incomparable — neither operand
discharges the other, so the ledger must keep both. -/
theorem ICacheInvalidation.ivauPage_not_covers_of_ne
    {p q : SeLe4n.PAddr} (h : p ≠ q) :
    (ICacheInvalidation.ivauPage p).covers (.ivauPage q) = false := by
  simp [ICacheInvalidation.covers, h]

/-- **WS-SM SM7.D**: coverage is transitive, so dropping a covered entry can
never lose an obligation transitively. -/
theorem ICacheInvalidation.covers_trans {a b c : ICacheInvalidation}
    (hab : a.covers b = true) (hbc : b.covers c = true) : a.covers c = true := by
  cases a <;> cases b <;> cases c <;>
    simp_all [ICacheInvalidation.covers]

/-- **WS-SM SM7.D**: accumulate one operand into the pending-maintenance
ledger.

The ledger is a **list**, appended in the order the transitions recorded, and
drained wholesale by the runtime.  Nothing is ever collapsed away except an
operand already *covered* by an entry the ledger holds — the only reduction
that provably discharges the dropped obligation.  A transition that records
maintenance therefore always leaves the ledger owing at least that operand
(`recordIcacheMaintenanceList_covered`), whatever it already held. -/
def recordIcacheMaintenanceList (ops : List ICacheInvalidation)
    (op : ICacheInvalidation) : List ICacheInvalidation :=
  if ops.any (fun a => a.covers op) then ops else ops ++ [op]

/-- **WS-SM SM7.D**: recording into an empty ledger records the operand
verbatim — the case every live seam hits (one maintenance-bearing transition
per syscall, drained at the syscall boundary), so the runtime emits the model's
*precise* operand. -/
@[simp] theorem recordIcacheMaintenanceList_nil (op : ICacheInvalidation) :
    recordIcacheMaintenanceList [] op = [op] := rfl

/-- **WS-SM SM7.D**: the ledger is never emptied by accumulation. -/
theorem recordIcacheMaintenanceList_ne_nil (ops : List ICacheInvalidation)
    (op : ICacheInvalidation) : recordIcacheMaintenanceList ops op ≠ [] := by
  unfold recordIcacheMaintenanceList
  split
  · rename_i h
    intro hnil
    simp [hnil] at h
  · simp

/-- **WS-SM SM7.D**: the exactness property the closure rests on — after
recording `op`, the ledger holds an entry that covers `op`.  Draining the
ledger therefore discharges every obligation any transition recorded, with no
appeal to an ordering on operands. -/
theorem recordIcacheMaintenanceList_covered (ops : List ICacheInvalidation)
    (op : ICacheInvalidation) :
    ∃ a ∈ recordIcacheMaintenanceList ops op, a.covers op = true := by
  unfold recordIcacheMaintenanceList
  split
  · rename_i h
    obtain ⟨a, ha, hcov⟩ := List.any_eq_true.mp h
    exact ⟨a, ha, hcov⟩
  · exact ⟨op, by simp, by simp⟩

/-- **WS-SM SM7.D**: recording preserves every entry already owed — an earlier
obligation is never dropped by a later record. -/
theorem recordIcacheMaintenanceList_mem_of_mem {ops : List ICacheInvalidation}
    {a : ICacheInvalidation} (op : ICacheInvalidation) (h : a ∈ ops) :
    a ∈ recordIcacheMaintenanceList ops op := by
  unfold recordIcacheMaintenanceList
  split
  · exact h
  · exact List.mem_append_left _ h

/-- **WS-SM SM7.D**: recording appends at most one entry.  Together with the
per-syscall drain (`clearIcacheMaintenance`, applied in the same atomic step
that commits the transition), this bounds the ledger at the number of
maintenance-bearing transitions in one syscall — one — so no capacity
invariant is needed. -/
theorem recordIcacheMaintenanceList_length_le (ops : List ICacheInvalidation)
    (op : ICacheInvalidation) :
    (recordIcacheMaintenanceList ops op).length ≤ ops.length + 1 := by
  unfold recordIcacheMaintenanceList
  split
  · omega
  · simp

end SeLe4n.Kernel.Architecture
