-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM SM7 (SM1.E.4 typed FFI wrapper for IS-variant
-- TLBI; consumed by SM7 cross-core TLB shootdown when secondaries online)
import SeLe4n.Kernel.Concurrency.Types
import SeLe4n.Platform.FFI

/-!
# WS-SM SM1.E.4 — Typed `tlbiForSharing` wrapper

This module wraps the raw `Platform.FFI.ffiTlbiForSharing` four-argument
FFI dispatcher in a typed Lean entry point that takes a
`(SharingDomain, TlbInvalidation)` pair and routes to the correct
IS or OS instruction via the Rust HAL.

## Why a typed wrapper

The Rust `tlbi_for_sharing` dispatcher takes (domainTag, opTag, asid,
vaddr) so it can be exposed across a stable C ABI.  A typed Lean
caller would otherwise have to encode the tags manually at every
call site — error-prone and obscures the semantic op.  The wrapper
here accepts the typed `SharingDomain` (from
`SeLe4n.Kernel.Concurrency.Types`) and a new typed `TlbInvalidation`
inductive, encodes both into the FFI tuple, and emits a single
`ffiTlbiForSharing` call.

## Encoding contract

The encoding **MUST** stay in lockstep with
`rust/sele4n-hal/src/ffi.rs::ffi_tlbi_for_sharing`:

  domainTag : 0 = Inner, 1 = Outer
  opTag     : 0 = Vmalle1, 1 = Vae1, 2 = Aside1, 3 = Vale1
  asid      : 16-bit ASID (RES0 for Vmalle1)
  vaddr     : page-aligned VA (RES0 for Vmalle1, Aside1)

A future encoding change requires:

  1. Updating `rust/sele4n-hal/src/ffi.rs` (the `match` arms).
  2. Updating `domainTag` / `opTag` in this file.
  3. Updating `tests/SmpFoundationsSuite.lean` runtime checks.

## Production reachability

This module is in the production import closure via
`SeLe4n/Platform/Staged.lean` (added at SM1.E for the SMP-shootdown
build closure).  The wrapper itself is unreachable at v1.0.0
(`SMP_ENABLED = false` from boot defaults are hardcoded; the cmdline
default flips this at v0.31.6, but no kernel transition currently
emits a TLBI under SMP).  SM7 (TLB shootdown) is the first runtime
exerciser.

## SMP correctness witness

The `tlbiForSharing` dispatcher is what makes a kernel TLBI **correct
under SMP**.  A direct call to `ffiTlbiByVaddr` (the AG7-A-iii
local variant) would invalidate only the calling PE's TLB — leaving
secondaries with stale entries cached against the same VA.  The
`tlbiForSharing` wrapper:

  1. Selects the IS or OS variant per the platform's binding.
  2. Issues the corresponding broadcast TLBI on the local PE.
  3. Waits for the broadcast to complete via `dsb {ish,osh}` + `isb`.

After this returns, every PE in the chosen sharing domain has had
its TLB invalidated for the requested operand.

## Anti-cycle note

This module imports `SeLe4n.Platform.FFI` (for `ffiTlbiForSharing`)
and `SeLe4n.Kernel.Concurrency.Types` (for `SharingDomain`).  Both
already coexist in the import graph (`Platform.FFI` ←
`Platform.Boot` ← `Platform.Contract` ← `Concurrency.Types`), so
there is no cycle here.
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- WS-SM SM1.E.4 — TlbInvalidation typed enum
-- ============================================================================

/-- **WS-SM SM1.E.4**: Typed TLBI operation selector.

Mirrors the Rust-side `sele4n_hal::tlb::TlbInvalidation` enum so
generic kernel code can describe a TLB invalidation without per-call
ASM-level tag arithmetic.  Each constructor carries the operand
fields the underlying ASM encoding needs:

* `vmalle1`            — full address-space flush; no operand fields.
* `vae1 asid vaddr`    — single-page invalidation including all
  intermediate levels.
* `aside1 asid`        — full ASID flush.
* `vale1 asid vaddr`   — last-level-only single-page invalidation.

The `Fin n` representation typing is intentionally avoided here —
the carrier types (`UInt16` for `asid`, `UInt64` for `vaddr`) are
the FFI-bridge widths.  A higher-level wrapper that wants to
constrain the asid to a typed `AsidId` (or vaddr to a `Page`-aligned
type) can do so in its own scope without changing this enum. -/
inductive TlbInvalidation where
  /-- TLBI VMALLE1{IS,OS} — invalidate every TLB entry at EL1. -/
  | vmalle1
  /-- TLBI VAE1{IS,OS} — invalidate by VA + ASID (all levels). -/
  | vae1 (asid : UInt16) (vaddr : UInt64)
  /-- TLBI ASIDE1{IS,OS} — invalidate every entry for the given ASID. -/
  | aside1 (asid : UInt16)
  /-- TLBI VALE1{IS,OS} — invalidate last-level only by VA + ASID. -/
  | vale1 (asid : UInt16) (vaddr : UInt64)
  deriving DecidableEq, Repr, Inhabited

-- ============================================================================
-- WS-SM SM1.E.4 — Tag encoding
-- ============================================================================

/-- **WS-SM SM1.E.4**: Encode a `SharingDomain` to its FFI discriminant.

The encoding **MUST** match the Rust dispatcher in
`rust/sele4n-hal/src/ffi.rs::ffi_tlbi_for_sharing` exactly.

Lives in the `SeLe4n.Kernel.Concurrency.SharingDomain` namespace so
dot-notation (`d.toTag`) resolves correctly when `d : SharingDomain`
is in scope.  Without this explicit namespace, Lean would create
`SeLe4n.Kernel.Architecture.SharingDomain.toTag`, and dot-notation
would not resolve because the type lives in
`SeLe4n.Kernel.Concurrency`. -/
@[inline] def _root_.SeLe4n.Kernel.Concurrency.SharingDomain.toTag :
    SharingDomain → UInt32
  | .inner => 0
  | .outer => 1

/-- **WS-SM SM1.E.4**: Encode a `TlbInvalidation` to its FFI op tag.

The op tag is `0 = Vmalle1`, `1 = Vae1`, `2 = Aside1`, `3 = Vale1`.
Operand fields are extracted by `TlbInvalidation.toAsid` and
`TlbInvalidation.toVaddr` (which return `0` for unused fields). -/
@[inline] def TlbInvalidation.toOpTag : TlbInvalidation → UInt32
  | .vmalle1     => 0
  | .vae1 _ _    => 1
  | .aside1 _    => 2
  | .vale1 _ _   => 3

/-- **WS-SM SM1.E.4**: Extract the ASID operand from a `TlbInvalidation`,
returning `0` for variants that do not carry one. -/
@[inline] def TlbInvalidation.toAsid : TlbInvalidation → UInt16
  | .vmalle1        => 0
  | .vae1 a _       => a
  | .aside1 a       => a
  | .vale1 a _      => a

/-- **WS-SM SM1.E.4**: Extract the VAddr operand from a `TlbInvalidation`,
returning `0` for variants that do not carry one. -/
@[inline] def TlbInvalidation.toVaddr : TlbInvalidation → UInt64
  | .vmalle1        => 0
  | .vae1 _ v       => v
  | .aside1 _       => 0
  | .vale1 _ v      => v

-- ============================================================================
-- WS-SM SM1.E.4 — Typed dispatcher entry point
-- ============================================================================

/-- **WS-SM SM1.E.4**: Issue a TLB invalidation broadcast in the
specified sharing domain.

Routes through the Rust HAL's `ffi_tlbi_for_sharing` dispatcher,
which selects the appropriate IS or OS variant and emits the proper
post-TLBI barrier sequence.

After this returns, every PE in the chosen sharing domain has had
its TLB invalidated for the requested operand.  The calling PE's
pipeline is also serialised (the Rust dispatcher emits `isb` after
`dsb {ish,osh}`), so subsequent translations on the calling PE
observe the new mapping.

**Usage**: call from any kernel transition that mutates a page-table
descriptor or retires an ASID.  The first such site is SM7's
cross-core TLB shootdown; until then this wrapper is staged but
unreachable from the runtime kernel.

**Performance**: on aarch64, the call cost is one indirect FFI call
plus one TLBI plus one DSB plus one ISB.  The TLBI broadcast latency
depends on platform topology (single-cluster RPi5: ~hundreds of
cycles; multi-cluster: ~thousands).  Per ARM ARM B2.7, the DSB
includes a guarantee that the broadcast has reached every PE in the
domain. -/
def tlbiForSharing (domain : SharingDomain) (op : TlbInvalidation) : BaseIO Unit :=
  Platform.FFI.ffiTlbiForSharing
    domain.toTag
    op.toOpTag
    op.toAsid
    op.toVaddr

-- ============================================================================
-- WS-SM SM1.E.4 — Tag-encoding correctness theorems
-- ============================================================================

/-- **WS-SM SM1.E.4**: `SharingDomain.toTag` is injective.

The two domain values map to distinct FFI tags (`0` vs `1`), so the
Rust dispatcher's `match domain_tag` arm is selectable without
ambiguity.  Discharged by case analysis + `decide`. -/
theorem _root_.SeLe4n.Kernel.Concurrency.SharingDomain.toTag_injective :
    ∀ d₁ d₂ : SharingDomain, d₁ ≠ d₂ → d₁.toTag ≠ d₂.toTag := by
  intro d₁ d₂ h
  cases d₁ <;> cases d₂ <;> simp_all <;> decide

/-- **WS-SM SM1.E.4**: every `SharingDomain.toTag` value is `< 2`.

Surface anchor for the Rust dispatcher's two-arm match.  A future
addition of a third sharing domain (e.g., system-shareable for some
non-ARM ports) would require updating both this bound and the Rust
dispatcher in lockstep. -/
theorem _root_.SeLe4n.Kernel.Concurrency.SharingDomain.toTag_in_range
    (d : SharingDomain) : d.toTag.toNat < 2 := by
  cases d <;> decide

/-- **WS-SM SM1.E.4**: `TlbInvalidation.toOpTag` produces every value
in `[0, 4)`.

The Rust dispatcher's four-arm match relies on every emit returning
a tag in `{0, 1, 2, 3}`.  This theorem witnesses the bound for
every constructor at elaboration.  Per-arm cases use `rfl` because
`toOpTag` is a literal-returning `match`; the four cases reduce to
the four constants `0`, `1`, `2`, `3`, all of which are `< 4` by
`decide`. -/
theorem TlbInvalidation.toOpTag_in_range (op : TlbInvalidation) : op.toOpTag.toNat < 4 := by
  cases op <;> simp [TlbInvalidation.toOpTag]

/-- **WS-SM SM1.E.4**: distinct `TlbInvalidation` constructors map to
distinct op tags.

The four constructors map to `0`, `1`, `2`, `3` respectively — all
distinct.  This is the structural witness that the Rust dispatcher's
match arms cover the typed enum without overlap. -/
theorem TlbInvalidation.toOpTag_distinct_constructors :
    (TlbInvalidation.vmalle1.toOpTag ≠ (TlbInvalidation.vae1 0 0).toOpTag) ∧
    (TlbInvalidation.vmalle1.toOpTag ≠ (TlbInvalidation.aside1 0).toOpTag) ∧
    (TlbInvalidation.vmalle1.toOpTag ≠ (TlbInvalidation.vale1 0 0).toOpTag) ∧
    ((TlbInvalidation.vae1 0 0).toOpTag ≠ (TlbInvalidation.aside1 0).toOpTag) ∧
    ((TlbInvalidation.vae1 0 0).toOpTag ≠ (TlbInvalidation.vale1 0 0).toOpTag) ∧
    ((TlbInvalidation.aside1 0).toOpTag ≠ (TlbInvalidation.vale1 0 0).toOpTag) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **WS-SM SM1.E.4**: `tlbiForSharing` is total (does not panic on
any input).

Every `(SharingDomain, TlbInvalidation)` pair maps to a well-formed
`(domainTag, opTag, asid, vaddr)` tuple by case analysis on both
arguments.  The underlying `ffiTlbiForSharing` is `BaseIO Unit` so
the wrapper inherits totality. -/
theorem tlbiForSharing_total (d : SharingDomain) (op : TlbInvalidation) :
    tlbiForSharing d op = Platform.FFI.ffiTlbiForSharing
      d.toTag op.toOpTag op.toAsid op.toVaddr := by
  rfl

/-- **WS-SM SM1.E.4 audit-pass-2**: `tlbiForSharing` always produces
FFI args within the Rust dispatcher's accepted range.

The Rust-side `ffi_tlbi_for_sharing` (in
`rust/sele4n-hal/src/ffi.rs`) PANICS on out-of-range tags
(`domain_tag >= 2` or `op_tag >= 4`) per the fail-closed contract.
This theorem proves that well-formed Lean callers — anyone using
the typed `tlbiForSharing(d, op)` wrapper — can NEVER trip the
Rust panic, because both tag-encoder values are structurally
bounded.

The theorem combines `SharingDomain.toTag_in_range` (proves
`d.toTag.toNat < 2`) and `TlbInvalidation.toOpTag_in_range` (proves
`op.toOpTag.toNat < 4`).  Together they witness the safety of the
FFI bridge: from the Lean side, the panic arm is unreachable. -/
theorem tlbiForSharing_ffi_args_in_range (d : SharingDomain)
    (op : TlbInvalidation) :
    d.toTag.toNat < 2 ∧ op.toOpTag.toNat < 4 := by
  refine ⟨?_, ?_⟩
  · exact SharingDomain.toTag_in_range d
  · exact TlbInvalidation.toOpTag_in_range op

-- ============================================================================
-- WS-SM SM1.E.4 — Per-constructor decidable witnesses
-- ============================================================================

/-- **WS-SM SM1.E.4**: `vmalle1` encodes to op tag 0. -/
theorem TlbInvalidation.vmalle1_opTag : TlbInvalidation.vmalle1.toOpTag = 0 := rfl
/-- **WS-SM SM1.E.4**: `vae1` encodes to op tag 1. -/
theorem TlbInvalidation.vae1_opTag (a : UInt16) (v : UInt64) :
    (TlbInvalidation.vae1 a v).toOpTag = 1 := rfl
/-- **WS-SM SM1.E.4**: `aside1` encodes to op tag 2. -/
theorem TlbInvalidation.aside1_opTag (a : UInt16) :
    (TlbInvalidation.aside1 a).toOpTag = 2 := rfl
/-- **WS-SM SM1.E.4**: `vale1` encodes to op tag 3. -/
theorem TlbInvalidation.vale1_opTag (a : UInt16) (v : UInt64) :
    (TlbInvalidation.vale1 a v).toOpTag = 3 := rfl

/-- **WS-SM SM1.E.4**: `Inner` encodes to domain tag 0. -/
theorem _root_.SeLe4n.Kernel.Concurrency.SharingDomain.inner_toTag :
    SharingDomain.inner.toTag = 0 := rfl
/-- **WS-SM SM1.E.4**: `Outer` encodes to domain tag 1. -/
theorem _root_.SeLe4n.Kernel.Concurrency.SharingDomain.outer_toTag :
    SharingDomain.outer.toTag = 1 := rfl

/-- **WS-SM SM1.E.4**: `vae1 a v` carries `a` as its ASID operand. -/
theorem TlbInvalidation.vae1_toAsid (a : UInt16) (v : UInt64) :
    (TlbInvalidation.vae1 a v).toAsid = a := rfl
/-- **WS-SM SM1.E.4**: `vae1 a v` carries `v` as its VAddr operand. -/
theorem TlbInvalidation.vae1_toVaddr (a : UInt16) (v : UInt64) :
    (TlbInvalidation.vae1 a v).toVaddr = v := rfl
/-- **WS-SM SM1.E.4**: `vmalle1` has zero ASID and VAddr operands. -/
theorem TlbInvalidation.vmalle1_zero_operands :
    TlbInvalidation.vmalle1.toAsid = 0 ∧ TlbInvalidation.vmalle1.toVaddr = 0 := by
  refine ⟨?_, ?_⟩ <;> rfl
/-- **WS-SM SM1.E.4**: `aside1 a` carries `a` as ASID and `0` as VAddr. -/
theorem TlbInvalidation.aside1_operands (a : UInt16) :
    (TlbInvalidation.aside1 a).toAsid = a ∧
    (TlbInvalidation.aside1 a).toVaddr = 0 := by
  refine ⟨?_, ?_⟩ <;> rfl

end SeLe4n.Kernel.Architecture
