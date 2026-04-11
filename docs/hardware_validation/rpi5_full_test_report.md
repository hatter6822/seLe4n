# AG9-G: Full RPi5 Hardware Test Report

## Purpose

Records the results of executing the complete seLe4n test suite on physical
Raspberry Pi 5 hardware, validating all subsystems end-to-end.

## Test Environment

| Parameter | Value |
|-----------|-------|
| Board | Raspberry Pi 5 |
| SoC | BCM2712 |
| CPU | Cortex-A76 (4 cores @ 2.4 GHz) |
| RAM | *pending* |
| Firmware | *pending* |
| Kernel Version | 0.26.9 |
| Lean Toolchain | v4.28.0 |
| Rust Toolchain | *pending* |
| Test Date | *pending* |

## Test Results

### Phase 1: Lean Tiered Tests

| Tier | Script | Status | Duration |
|------|--------|--------|----------|
| Tier 0 | `test_tier0_hygiene.sh` | *pending* | - |
| Tier 1 | `test_tier1_build.sh` | *pending* | - |
| Tier 2 (trace) | `test_tier2_trace.sh` | *pending* | - |
| Tier 2 (negative) | `test_tier2_negative.sh` | *pending* | - |
| Tier 2 (determinism) | `test_tier2_determinism.sh` | *pending* | - |
| Tier 3 | `test_tier3_invariant_surface.sh` | *pending* | - |

### Phase 2: Rust Tests

| Step | Status | Test Count |
|------|--------|-----------|
| Build all crates | *pending* | - |
| Unit tests | *pending* | - |
| Conformance tests | *pending* | - |

### Phase 3: Badge Overflow (AG9-E)

| Status | Test Count |
|--------|-----------|
| *pending* | 22 |

### Phase 4: Hardware Cross-Check (AG9-B)

| Constant | Status |
|----------|--------|
| All 15 constants | *pending* |

### Phase 5: QEMU Integration (AG9-A)

| Check | Status |
|-------|--------|
| Boot banner | *pending* |
| No fatal exceptions | *pending* |
| QEMU stability | *pending* |

## Hardware-Specific Issues

*(To be populated after hardware execution)*

## Execution Command

```bash
sudo ./scripts/test_hw_full.sh --continue 2>&1 | tee hw_test_results.log
```

## Cross-Reference

- Test runner: `scripts/test_hw_full.sh`
- Hardware cross-check: `scripts/test_hw_crosscheck.sh`
- QEMU tests: `scripts/test_qemu.sh`
- Badge tests: `tests/BadgeOverflowSuite.lean`
