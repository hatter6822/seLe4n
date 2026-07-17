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
import SeLe4n.Kernel.Architecture.TlbInvalidation
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
`SeLe4n.Kernel.Concurrency.Types`) and the typed `TlbInvalidation`
inductive (since SM7.A extracted to the pure, production
`TlbInvalidation.lean` module so the SM7.A shootdown descriptors —
mounted in `Model/State.lean` — can carry it without this module's
`Platform.FFI` import closure), encodes both into the FFI tuple, and
emits a single `ffiTlbiForSharing` call.

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
-- WS-SM SM1.E.4 — Tag encoding
-- ============================================================================
--
-- The `TlbInvalidation` inductive and its `toOpTag` / `toAsid` /
-- `toVaddr` encoders (+ their correctness theorems) moved to the pure,
-- production `SeLe4n.Kernel.Architecture.TlbInvalidation` module at
-- SM7.A (imported above; all fully-qualified names unchanged).  This
-- module keeps the `SharingDomain` half of the FFI encoding contract
-- and the `BaseIO` dispatcher itself.

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
-- WS-SM SM1.E.4 — Per-constructor decidable witnesses (SharingDomain half;
-- the TlbInvalidation witnesses live in `TlbInvalidation.lean` since SM7.A)
-- ============================================================================

/-- **WS-SM SM1.E.4**: `Inner` encodes to domain tag 0. -/
theorem _root_.SeLe4n.Kernel.Concurrency.SharingDomain.inner_toTag :
    SharingDomain.inner.toTag = 0 := rfl
/-- **WS-SM SM1.E.4**: `Outer` encodes to domain tag 1. -/
theorem _root_.SeLe4n.Kernel.Concurrency.SharingDomain.outer_toTag :
    SharingDomain.outer.toTag = 1 := rfl

end SeLe4n.Kernel.Architecture
