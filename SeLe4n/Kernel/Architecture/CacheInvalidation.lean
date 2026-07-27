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
          2 = UnifyPage (clean D-cache to PoU, then invalidate one page),
          3 = CleanRangeIallu (clean a byte range to PoU, then invalidate all)
  paddr : physical address — page-aligned for tags 1 and 2, the range base for
          tag 3, RES0 for Iallu
  size  : byte length of the range (tag 3 only; RES0 otherwise)

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
expressed in.

Defined as `SeLe4n.pageBytes` rather than a second literal: the mapping
constructors enforce page alignment against that constant (PR #845 review, P2),
and the maintenance operands must be expressed in the *same* granule or the
alignment they guarantee would not be the alignment this module assumes.
Definitional, so every existing proof about `pageBytes` is unaffected. -/
def pageBytes : Nat := SeLe4n.pageBytes

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
  /-- **WS-SM SM7.D**: clean the byte range `[base, base + size)` to the Point
      of Unification, then invalidate **every** instruction cache in the domain
      — `DC CVAU` over the range → `DSB ISH` → `IC IALLUIS` → `DSB ISH` → `ISB`.

      The re-type operand.  A re-type *scrubs* the target's backing memory
      (`scrubObjectMemory` zeroes `[objId × allocSize, + allocSize)`) and then
      installs a different object over it.  Those zeroing stores land in the
      data cache; until a `DC CVAU` pushes them to the Point of Unification an
      instruction fetch of the same physical memory still reads the **previous
      owner's** content, because fetches read at the PoU.  `IC IALLUIS` alone
      does not close that: it drops instruction lines but performs no clean, so
      the very next fetch re-fills from the stale PoU copy.  seL4's
      `clearMemory` is `memzero` followed by `cleanCacheRange_PoU` for exactly
      this reason.

      The two halves are one operand rather than two ledger entries precisely
      so the ordering cannot be lost: the clean **must** complete before the
      invalidate is observed, and bundling them makes that the HAL routine's
      internal `DSB ISH` rather than a property of accumulation order.  This is
      the same reasoning that makes `unifyPage` distinct from `ivauPage`.

      The invalidation half is domain-wide rather than by-VA because the
      abstract state cannot enumerate which *mappings* alias the re-purposed
      frame, and instruction caches are physically tagged (ARM ARM D7.2) — so a
      line stays hittable through any later executable mapping of the frame, in
      any address space.  Over-invalidation costs re-fetches; under-invalidation
      is the hazard. -/
  | cleanRangeIallu (base : SeLe4n.PAddr) (size : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- **WS-SM SM7.D.1**: encode an `ICacheInvalidation` to its FFI op tag.
`0 = Iallu`, `1 = IvauPage`, `2 = UnifyPage`, `3 = CleanRangeIallu`; the
operands are carried by `ICacheInvalidation.toPaddr` / `.toSize` (`0` for the
variants that do not use them). -/
@[inline] def ICacheInvalidation.toOpTag : ICacheInvalidation → UInt32
  | .iallu              => 0
  | .ivauPage _         => 1
  | .unifyPage _        => 2
  | .cleanRangeIallu .. => 3

/-- **WS-SM SM7.D.1**: extract the physical-address operand, returning `0` for
the operand-free `iallu`. -/
@[inline] def ICacheInvalidation.toPaddr : ICacheInvalidation → UInt64
  | .iallu                 => 0
  | .ivauPage p            => UInt64.ofNat p.toNat
  | .unifyPage p           => UInt64.ofNat p.toNat
  | .cleanRangeIallu b _   => UInt64.ofNat b.toNat

/-- **WS-SM SM7.D**: extract the byte-length operand.  Only `cleanRangeIallu`
carries one — the page-granular operands take their length from the
architecture's translation granule (`pageBytes`), and `iallu` has no extent at
all — so every other constructor encodes `0`, which the HAL treats as RES0. -/
@[inline] def ICacheInvalidation.toSize : ICacheInvalidation → UInt64
  | .iallu                => 0
  | .ivauPage _           => 0
  | .unifyPage _          => 0
  | .cleanRangeIallu _ s  => UInt64.ofNat s

/-- **WS-SM SM7.D.1**: `toOpTag` produces every value in `[0, 4)` — the
bound the Rust dispatcher's four-arm match relies on. -/
theorem ICacheInvalidation.toOpTag_in_range (op : ICacheInvalidation) :
    op.toOpTag.toNat < 4 := by
  cases op <;> simp [ICacheInvalidation.toOpTag]

/-- **WS-SM SM7.D.1**: distinct constructors map to distinct op tags — the
structural witness that the Rust match arms cover the enum without overlap.

Stated over the enumeration rather than as pairwise disequalities so that
adding a constructor extends the list by one entry instead of the quadratic
blow-up of pairs. -/
theorem ICacheInvalidation.toOpTag_distinct_constructors :
    [ICacheInvalidation.iallu.toOpTag,
     (ICacheInvalidation.ivauPage (SeLe4n.PAddr.ofNat 0)).toOpTag,
     (ICacheInvalidation.unifyPage (SeLe4n.PAddr.ofNat 0)).toOpTag,
     (ICacheInvalidation.cleanRangeIallu (SeLe4n.PAddr.ofNat 0) 0).toOpTag].Nodup := by
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
/-- **WS-SM SM7.D**: `cleanRangeIallu` encodes to op tag 3. -/
theorem ICacheInvalidation.cleanRangeIallu_opTag (b : SeLe4n.PAddr) (s : Nat) :
    (ICacheInvalidation.cleanRangeIallu b s).toOpTag = 3 := rfl
/-- **WS-SM SM7.D**: `cleanRangeIallu b s` carries `b` as its address operand
and `s` as its length — the only constructor for which `toSize` is live. -/
theorem ICacheInvalidation.cleanRangeIallu_operands (b : SeLe4n.PAddr) (s : Nat) :
    (ICacheInvalidation.cleanRangeIallu b s).toPaddr = UInt64.ofNat b.toNat ∧
    (ICacheInvalidation.cleanRangeIallu b s).toSize = UInt64.ofNat s :=
  ⟨rfl, rfl⟩
/-- **WS-SM SM7.D**: every page-granular or extent-free operand encodes a zero
length — the HAL reads `size` only for tag 3, and this pins that the others
never smuggle one in. -/
theorem ICacheInvalidation.toSize_zero_of_not_range :
    ICacheInvalidation.iallu.toSize = 0 ∧
    (∀ p : SeLe4n.PAddr, (ICacheInvalidation.ivauPage p).toSize = 0) ∧
    (∀ p : SeLe4n.PAddr, (ICacheInvalidation.unifyPage p).toSize = 0) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl⟩

/-- **WS-SM SM7.D**: `unifyPage` encodes to op tag 2. -/
theorem ICacheInvalidation.unifyPage_opTag (p : SeLe4n.PAddr) :
    (ICacheInvalidation.unifyPage p).toOpTag = 2 := rfl
/-- **WS-SM SM7.D**: `unifyPage p` carries `p` as its physical-address
operand. -/
theorem ICacheInvalidation.unifyPage_toPaddr (p : SeLe4n.PAddr) :
    (ICacheInvalidation.unifyPage p).toPaddr = UInt64.ofNat p.toNat := rfl

/-- **WS-SM SM7.D**: does this operand invalidate the *whole* instruction cache
of every PE it reaches, rather than a named page?

The two operands that emit `IC IALLUIS` — the bare `iallu` and the re-type's
`cleanRangeIallu` — answer `true`.  Stated as a predicate so the theorems that
depend only on "the post-state instruction caches are cold"
(`applyICacheInvalidation_domainWide`, and through it the re-type seams' 14th-
conjunct proofs) hold for both without case-splitting, and so a future operand
that is *not* domain-wide cannot silently inherit those conclusions. -/
@[inline] def ICacheInvalidation.isDomainWide : ICacheInvalidation → Bool
  | .iallu              => true
  | .ivauPage _         => false
  | .unifyPage _        => false
  | .cleanRangeIallu .. => true

-- ============================================================================
-- SM7.D.1 — The ledger's algebra: a *coverage* preorder, not a join
-- ============================================================================

/-- **WS-SM SM7.D**: does the byte range `[base, base + size)` contain
`[b, b + s)`?  The containment test the range operand's coverage rests on:
cleaning a superset of a range discharges the smaller clean, because `DC CVAU`
is per-line and cleaning extra lines is always safe (it writes back data that
was going to be written back anyway) — never the reverse. -/
def byteRangeContains (base : SeLe4n.PAddr) (size : Nat)
    (b : SeLe4n.PAddr) (s : Nat) : Bool :=
  decide (base.toNat ≤ b.toNat ∧ b.toNat + s ≤ base.toNat + size)

/-- **WS-SM SM7.D**: range containment, unfolded to arithmetic. -/
theorem byteRangeContains_iff {base b : SeLe4n.PAddr} {size s : Nat} :
    byteRangeContains base size b s = true ↔
      base.toNat ≤ b.toNat ∧ b.toNat + s ≤ base.toNat + size := by
  simp [byteRangeContains]

/-- **WS-SM SM7.D**: every range contains itself. -/
@[simp] theorem byteRangeContains_refl (base : SeLe4n.PAddr) (size : Nat) :
    byteRangeContains base size base size = true := by
  simp [byteRangeContains]

/-- **WS-SM SM7.D**: range containment is transitive — the arithmetic behind
`ICacheInvalidation.covers_trans` on the range arms. -/
theorem byteRangeContains_trans {a b c : SeLe4n.PAddr} {sa sb sc : Nat}
    (hab : byteRangeContains a sa b sb = true)
    (hbc : byteRangeContains b sb c sc = true) :
    byteRangeContains a sa c sc = true := by
  rw [byteRangeContains_iff] at hab hbc ⊢
  omega

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
  a page invalidate) but **not** `unifyPage` or `cleanRangeIallu` (no clean).
- `ivauPage p` covers only `ivauPage p`.
- `unifyPage p` covers `unifyPage p` and `ivauPage p` (same lines invalidated,
  plus the clean) but not `iallu` (narrower invalidation scope).
- `cleanRangeIallu b s` invalidates domain-wide *and* cleans `[b, b+s)`, so it
  covers `iallu`, any `ivauPage`, a `unifyPage` whose page lies inside the
  cleaned range, and a `cleanRangeIallu` whose range it contains. -/
def ICacheInvalidation.covers : ICacheInvalidation → ICacheInvalidation → Bool
  | .iallu,              .iallu              => true
  | .iallu,              .ivauPage _         => true
  | .iallu,              .unifyPage _        => false
  | .iallu,              .cleanRangeIallu .. => false
  | .ivauPage p,         .ivauPage q         => p == q
  | .ivauPage _,         .iallu              => false
  | .ivauPage _,         .unifyPage _        => false
  | .ivauPage _,         .cleanRangeIallu .. => false
  | .unifyPage p,        .unifyPage q        => p == q
  | .unifyPage p,        .ivauPage q         => p == q
  | .unifyPage _,        .iallu              => false
  | .unifyPage _,        .cleanRangeIallu .. => false
  | .cleanRangeIallu .., .iallu              => true
  | .cleanRangeIallu .., .ivauPage _         => true
  | .cleanRangeIallu b s, .unifyPage q       => byteRangeContains b s q pageBytes
  | .cleanRangeIallu b s, .cleanRangeIallu b' s' => byteRangeContains b s b' s'

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

/-- **WS-SM SM7.D**: the range operand covers the bare domain-wide
invalidate — it issues `IC IALLUIS` too, plus the clean. -/
@[simp] theorem ICacheInvalidation.cleanRangeIallu_covers_iallu
    (b : SeLe4n.PAddr) (s : Nat) :
    (ICacheInvalidation.cleanRangeIallu b s).covers .iallu = true := rfl

/-- **WS-SM SM7.D**: and every page invalidate, for the same reason. -/
@[simp] theorem ICacheInvalidation.cleanRangeIallu_covers_ivauPage
    (b : SeLe4n.PAddr) (s : Nat) (p : SeLe4n.PAddr) :
    (ICacheInvalidation.cleanRangeIallu b s).covers (.ivauPage p) = true := rfl

/-- **WS-SM SM7.D**: the range operand covers a `unifyPage` exactly when the
cleaned extent contains that page — both halves then dominate (the clean by
containment, the invalidate because `IC IALLUIS` subsumes `IC IVAU`). -/
theorem ICacheInvalidation.cleanRangeIallu_covers_unifyPage
    {b : SeLe4n.PAddr} {s : Nat} {p : SeLe4n.PAddr}
    (h : byteRangeContains b s p pageBytes = true) :
    (ICacheInvalidation.cleanRangeIallu b s).covers (.unifyPage p) = true := h

/-- **WS-SM SM7.D** (the exclusion this constructor exists for, as a theorem):
`iallu` does **not** cover a `cleanRangeIallu`.  `IC IALLUIS` drops instruction
lines but issues no `DC CVAU`, so the scrubbed bytes stay in the data cache and
the next fetch re-fills from the pre-scrub Point-of-Unification content — the
"execute the previous owner's code after a re-type" hazard.  Stated so that a
future collapse of the range operand into `iallu` fails here rather than
silently dropping the clean. -/
theorem ICacheInvalidation.iallu_not_covers_cleanRangeIallu
    (b : SeLe4n.PAddr) (s : Nat) :
    ICacheInvalidation.iallu.covers (.cleanRangeIallu b s) = false := rfl

/-- **WS-SM SM7.D**: a page-granular clean does not cover a range operand
either — `unifyPage` invalidates one page, not the domain, so it cannot stand
in for the re-type's broadcast even when it cleans enough bytes. -/
theorem ICacheInvalidation.unifyPage_not_covers_cleanRangeIallu
    (p b : SeLe4n.PAddr) (s : Nat) :
    (ICacheInvalidation.unifyPage p).covers (.cleanRangeIallu b s) = false := rfl

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
    simp_all [ICacheInvalidation.covers] <;>
    exact byteRangeContains_trans hab hbc

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
