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
# WS-SM SM1.E.4 / SM7.A — Typed TLB-invalidation operation

The pure `TlbInvalidation` inductive and its FFI tag/operand encoders,
extracted from `TlbiForSharing.lean` at SM7.A so that state-layer
consumers can name a TLB-invalidation operation **without** pulling the
FFI dispatcher's import closure (`TlbiForSharing` imports
`Platform.FFI`, which sits above `Kernel.API` in the import graph —
far too high for `Model/State.lean`, which mounts the SM7.A
`TlbShootdownState` whose descriptors carry a `TlbInvalidation`).

Everything here is pure data + `rfl`-class theorems; the `BaseIO`
dispatcher `tlbiForSharing` and the `SharingDomain.toTag` half of the
FFI encoding contract remain in `TlbiForSharing.lean` (staged), which
imports this module.  All definitions keep their original
fully-qualified names (`SeLe4n.Kernel.Architecture.TlbInvalidation…`),
so every pre-existing consumer and surface anchor resolves unchanged.

## Encoding contract

The op-tag/operand encoding **MUST** stay in lockstep with
`rust/sele4n-hal/src/ffi.rs::ffi_tlbi_for_sharing`:

  opTag     : 0 = Vmalle1, 1 = Vae1, 2 = Aside1, 3 = Vale1
  asid      : 16-bit ASID (RES0 for Vmalle1)
  vaddr     : page-aligned VA (RES0 for Vmalle1, Aside1)

A future encoding change requires updating the Rust `match` arms, the
encoders here, and the `tests/SmpFoundationsSuite.lean` runtime checks
in the same PR (see `TlbiForSharing.lean` §"Encoding contract" for the
`SharingDomain` half).
-/

namespace SeLe4n.Kernel.Architecture

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
