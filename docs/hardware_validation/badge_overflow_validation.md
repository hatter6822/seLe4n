# AG9-E: Badge Overflow Hardware Validation Report

## Purpose

Validates Badge `Nat ↔ UInt64` conversion behavior on ARM64 hardware,
confirming the Lean model's `Badge.ofNatMasked` truncation semantics match
actual 64-bit register behavior.

## Validation Summary

### Lean Model Tests (22 tests)

Run via `lake exe badge_overflow_suite`:

| Category | Tests | Status |
|----------|-------|--------|
| BOV-001..005: Round-trip identity | 5 | PASS |
| BOV-006..009: Overflow/truncation | 4 | PASS |
| BOV-010..014: Badge bor semantics | 5 | PASS |
| BOV-015..018: Boundary values | 4 | PASS |
| BOV-019..022: Theorem cross-checks | 4 | PASS |

### Rust ABI Tests (7 tests)

Run via `cargo test -p sele4n-types`:

| Test | Description | Status |
|------|-------------|--------|
| `badge_zero_roundtrip` | Zero value preservation | PASS |
| `badge_max_u64_roundtrip` | u64::MAX preservation | PASS |
| `badge_power_of_two_roundtrips` | Powers of 2 (0..63) | PASS |
| `badge_bor_max_values` | OR of max values | PASS |
| `badge_bor_disjoint_bits` | OR of complementary bits | PASS |
| `badge_u64_size_is_8_bytes` | Size matches GPR width | PASS |
| `badge_midrange_value` | Arbitrary 64-bit value | PASS |

## Key Findings

### Model-Hardware Alignment

1. **Lean `Badge.ofNatMasked`** applies `% machineWordMax` (mod 2^64) to
   truncate unbounded `Nat` values to 64-bit range. This is a no-op for
   values already within u64 range.

2. **Rust `Badge`** is `#[repr(transparent)]` over `u64`, directly matching
   ARM64 GPR width. No truncation occurs — values are inherently bounded.

3. **Theorem `Badge.toNat_ofNatMasked`** proves the round-trip property:
   `(Badge.ofNatMasked n).toNat = n % machineWordMax`, which is identity
   for values < 2^64.

4. **Theorem `Badge.ofNatMasked_toNat`** proves that for valid badges,
   `Badge.ofNatMasked b.toNat = b` (perfect identity).

### Overflow Behavior

The Lean model's `ofNatMasked` truncation (mod 2^64) exactly matches C/Rust
unsigned integer wrapping semantics. On ARM64 hardware:
- Register writes silently truncate to 64 bits
- The Lean model's modular arithmetic is the correct formal model

### Hardware Register Width

ARM64 GPRs (x0-x30) are 64-bit registers. The `Badge` type's `u64`
representation matches exactly, with no risk of width mismatch.

## Cross-Reference

- Lean Badge type: `SeLe4n/Prelude.lean` (lines 510-576)
- Rust Badge type: `rust/sele4n-types/src/identifiers.rs`
- Test suite (Lean): `tests/BadgeOverflowSuite.lean`
- Round-trip theorems: `Badge.toNat_ofNatMasked`, `Badge.ofNatMasked_toNat`
