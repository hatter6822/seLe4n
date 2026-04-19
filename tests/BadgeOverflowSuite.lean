/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Prelude
import SeLe4n.Testing.Helpers

/-! # AG9-E: Badge Overflow Hardware Validation Suite

Validates Badge Nat ↔ UInt64 round-trip behavior and overflow semantics.
Ensures the Lean model's `Badge.ofNatMasked` truncation matches ARM64 hardware
register width (64-bit).

## Test categories

- **BOV-001..005**: Round-trip identity for in-range values
- **BOV-006..009**: Overflow/truncation behavior for out-of-range values
- **BOV-010..014**: Badge bitwise OR (bor) overflow semantics
- **BOV-015..018**: Boundary values (0, max-1, max, max+1)
- **BOV-019..022**: Hardware register width cross-check theorems
-/

open SeLe4n
open SeLe4n.Testing

namespace SeLe4n.Testing.BadgeOverflowSuite

private def tag : String := "badge-overflow"

private def expect (label : String) (cond : Bool) : IO Unit :=
  expectCond tag label cond

-- ============================================================================
-- BOV-001..005: Round-trip identity for in-range values
-- ============================================================================

/-- BOV-001: Zero badge round-trip. -/
private def bov001_zeroRoundTrip : IO Unit := do
  let b := Badge.ofNatMasked 0
  expect "zero round-trip" (b.toNat == 0)

/-- BOV-002: Small value round-trip. -/
private def bov002_smallRoundTrip : IO Unit := do
  let b := Badge.ofNatMasked 42
  expect "small=42 round-trip" (b.toNat == 42)

/-- BOV-003: Max valid badge round-trip (2^64 - 1). -/
private def bov003_maxValidRoundTrip : IO Unit := do
  let maxVal := machineWordMax - 1  -- 2^64 - 1
  let b := Badge.ofNatMasked maxVal
  expect "max valid round-trip" (b.toNat == maxVal)
  expect "max valid is valid" b.isValid

/-- BOV-004: Power-of-two round-trips. -/
private def bov004_powerOfTwoRoundTrip : IO Unit := do
  -- 2^0, 2^16, 2^32, 2^48, 2^63 all fit in 64 bits
  for shift in [0, 16, 32, 48, 63] do
    let val := 1 <<< shift
    let b := Badge.ofNatMasked val
    expect s!"2^{shift} round-trip" (b.toNat == val)

/-- BOV-005: Arbitrary mid-range value round-trip. -/
private def bov005_midRangeRoundTrip : IO Unit := do
  let val := 0xDEADBEEFCAFEBABE
  let b := Badge.ofNatMasked val
  expect "mid-range round-trip" (b.toNat == val)

-- ============================================================================
-- BOV-006..009: Overflow/truncation behavior
-- ============================================================================

/-- BOV-006: Value at 2^64 wraps to 0 via modulo. -/
private def bov006_exactOverflow : IO Unit := do
  let b := Badge.ofNatMasked machineWordMax  -- 2^64
  expect "2^64 wraps to 0" (b.toNat == 0)

/-- BOV-007: Value at 2^64 + 1 wraps to 1. -/
private def bov007_overflowPlusOne : IO Unit := do
  let b := Badge.ofNatMasked (machineWordMax + 1)
  expect "2^64+1 wraps to 1" (b.toNat == 1)

/-- BOV-008: Value at 2^65 wraps to 0. -/
private def bov008_doubleOverflow : IO Unit := do
  let b := Badge.ofNatMasked (2 * machineWordMax)
  expect "2^65 wraps to 0" (b.toNat == 0)

/-- BOV-009: Very large value truncation preserves low 64 bits. -/
private def bov009_largeTruncation : IO Unit := do
  let large := machineWordMax * 3 + 42
  let b := Badge.ofNatMasked large
  expect "large value mod 2^64 == 42" (b.toNat == 42)

-- ============================================================================
-- BOV-010..014: Badge bitwise OR (bor) overflow semantics
-- ============================================================================

/-- BOV-010: bor of two in-range badges stays in-range. -/
private def bov010_borInRange : IO Unit := do
  let a := Badge.ofNatMasked 0xFF00
  let b := Badge.ofNatMasked 0x00FF
  let c := Badge.bor a b
  expect "bor in-range" (c.toNat == 0xFFFF)
  expect "bor valid" c.isValid

/-- BOV-011: bor with max valid badge. -/
private def bov011_borMaxValid : IO Unit := do
  let a := Badge.ofNatMasked (machineWordMax - 1)  -- all bits set
  let b := Badge.ofNatMasked 1
  let c := Badge.bor a b
  expect "bor with max" (c.toNat == machineWordMax - 1)
  expect "bor max valid" c.isValid

/-- BOV-012: bor is commutative (runtime check). -/
private def bov012_borCommutative : IO Unit := do
  let a := Badge.ofNatMasked 0xAAAA
  let b := Badge.ofNatMasked 0x5555
  let ab := Badge.bor a b
  let ba := Badge.bor b a
  expect "bor commutative" (ab.toNat == ba.toNat)

/-- BOV-013: bor is idempotent (runtime check). -/
private def bov013_borIdempotent : IO Unit := do
  let a := Badge.ofNatMasked 0xBEEF
  let aa := Badge.bor a a
  expect "bor idempotent" (aa.toNat == a.toNat)

/-- BOV-014: bor result always valid. -/
private def bov014_borAlwaysValid : IO Unit := do
  let a := Badge.ofNatMasked (machineWordMax - 1)
  let b := Badge.ofNatMasked (machineWordMax - 1)
  let c := Badge.bor a b
  expect "bor max|max valid" c.isValid

-- ============================================================================
-- BOV-015..018: Boundary values
-- ============================================================================

/-- BOV-015: Badge 0 is valid. -/
private def bov015_zeroValid : IO Unit := do
  let b := Badge.ofNatMasked 0
  expect "zero valid" b.isValid

/-- BOV-016: Badge max-1 is valid. -/
private def bov016_maxMinusOneValid : IO Unit := do
  let b := Badge.ofNatMasked (machineWordMax - 1)
  expect "max-1 valid" b.isValid

/-- BOV-017: Badge at machineWordMax wraps (not valid before mask). -/
private def bov017_maxWraps : IO Unit := do
  let b := Badge.ofNatMasked machineWordMax
  -- After masking, value is 0 (valid)
  expect "max wraps to 0" (b.toNat == 0)
  expect "wrapped badge valid" b.isValid

/-- BOV-018: machineWordBits is 64. -/
private def bov018_machineWordBits : IO Unit := do
  expect "machineWordBits=64" (machineWordBits == 64)
  expect "machineWordMax=2^64" (machineWordMax == 2 ^ 64)

-- ============================================================================
-- BOV-019..022: Hardware register width cross-check theorems
-- ============================================================================

/-- BOV-019: ofNatMasked round-trip for valid input. -/
private def bov019_roundTripTheorem : IO Unit := do
  -- Exercises Badge.toNat_ofNatMasked at runtime
  let n := 12345
  let rt := (Badge.ofNatMasked n).toNat
  expect "toNat∘ofNatMasked = mod" (rt == n % machineWordMax)

/-- BOV-020: ofNatMasked identity for small values. -/
private def bov020_identitySmall : IO Unit := do
  -- Small values: mod is identity
  for n in [0, 1, 100, 65535, 1000000] do
    let b := Badge.ofNatMasked n
    expect s!"identity n={n}" (b.toNat == n)

/-- BOV-021: isWord64 predicate consistency. -/
private def bov021_isWord64Consistency : IO Unit := do
  expect "isWord64 small" (isWord64Dec 42 == true)
  expect "isWord64 max-1" (isWord64Dec (machineWordMax - 1) == true)
  expect "!isWord64 max" (isWord64Dec machineWordMax == false)
  expect "!isWord64 max+1" (isWord64Dec (machineWordMax + 1) == false)

/-- BOV-022: Badge validity matches isWord64. -/
private def bov022_validityMatchesWord64 : IO Unit := do
  let b42 := Badge.ofNatMasked 42
  expect "valid↔isWord64 small" (b42.isValid == isWord64Dec b42.toNat)
  let bMax := Badge.ofNatMasked (machineWordMax - 1)
  expect "valid↔isWord64 max-1" (bMax.isValid == isWord64Dec bMax.toNat)

end SeLe4n.Testing.BadgeOverflowSuite

-- ============================================================================
-- Main entry point (must be at top-level for lake exe)
-- ============================================================================

open SeLe4n.Testing.BadgeOverflowSuite in
def main : IO Unit := do
  IO.println "=== AG9-E: Badge Overflow Hardware Validation Suite ==="
  IO.println ""
  -- Round-trip identity
  bov001_zeroRoundTrip
  bov002_smallRoundTrip
  bov003_maxValidRoundTrip
  bov004_powerOfTwoRoundTrip
  bov005_midRangeRoundTrip
  -- Overflow/truncation
  bov006_exactOverflow
  bov007_overflowPlusOne
  bov008_doubleOverflow
  bov009_largeTruncation
  -- Badge bor
  bov010_borInRange
  bov011_borMaxValid
  bov012_borCommutative
  bov013_borIdempotent
  bov014_borAlwaysValid
  -- Boundary values
  bov015_zeroValid
  bov016_maxMinusOneValid
  bov017_maxWraps
  bov018_machineWordBits
  -- Theorem cross-checks
  bov019_roundTripTheorem
  bov020_identitySmall
  bov021_isWord64Consistency
  bov022_validityMatchesWord64
  IO.println ""
  IO.println "=== All 22 badge overflow tests passed ==="
