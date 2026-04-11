# AG9-F: Security Hardening — Speculation Barriers

## Purpose

Documents the Spectre v1/v2 mitigations applied to the seLe4n kernel's
Rust HAL layer, targeting the Cortex-A76 processor on Raspberry Pi 5.

## Threat Model

### Spectre v1 (Bounds Check Bypass)

An attacker triggers speculative execution past a bounds check, causing
the CPU to access out-of-bounds memory and leak data through cache
timing side channels.

**Vulnerable patterns in seLe4n:**
1. Exception class dispatch (`trap.rs:handle_synchronous_exception`)
2. GIC interrupt ID dispatch (`gic.rs:dispatch_irq`)
3. Capability address resolution (CPtr bit masking — Lean model)
4. RunQueue priority bucket lookup (Lean model)
5. Page table descriptor indexing (Lean model)

### Spectre v2 (Branch Target Injection)

An attacker poisons the branch predictor to redirect speculative execution
to an attacker-chosen gadget. Mitigated by FEAT_CSV2 (hardware) and
retpoline-style indirect branch hardening.

**Cortex-A76 mitigations:**
- FEAT_CSV2: Hardware prevents branch predictor aliasing across contexts
- Kernel runs at EL1 with separate prediction context from EL0

## Applied Mitigations

### CSDB (Conditional Speculation Dependency Barrier)

Added to `rust/sele4n-hal/src/barriers.rs` (AG9-F):

```rust
pub fn csdb() {
    #[cfg(target_arch = "aarch64")]
    unsafe { core::arch::asm!("csdb", options(nomem, nostack, preserves_flags)) }
}
```

**Deployment sites:**

| Location | File | Purpose |
|----------|------|---------|
| Exception dispatch | `trap.rs:handle_synchronous_exception` | CSDB after ESR_EL1 EC classification |
| GIC dispatch | `gic.rs:dispatch_irq` | CSDB after INTID bounds check |
| Bounds check helper | `barriers.rs:speculation_safe_bound_check` | Generic bounds check + CSDB pattern |

### SB (Speculation Barrier)

Available as `barriers::sb()`. Emits the `SB` hint instruction encoding
(`0xD503233F`, ARM ARM C6.2.245). On cores without FEAT_SB, the encoding
executes as NOP. Cortex-A76 supports FEAT_SB natively.

### FEAT_CSV2 Verification

`barriers::has_feat_csv2()` reads `ID_AA64PFR0_EL1.CSV2` to verify
hardware Spectre v2 mitigation is active. On Cortex-A76, FEAT_CSV2 is
always supported.

### speculation_safe_bound_check Helper

Generic pattern for speculative-safe bounds checking:

```rust
pub fn speculation_safe_bound_check(index: usize, bound: usize) -> bool {
    let in_bounds = index < bound;
    csdb();  // Resolve branch before data-dependent access
    in_bounds
}
```

## Not in Scope

The following mitigations are deferred (not applicable to Cortex-A76):

| Mitigation | Reason |
|-----------|--------|
| MTE (Memory Tagging Extension) | Not supported on Cortex-A76 |
| PAC (Pointer Authentication) | Deferred to WS-V |
| BTI (Branch Target Identification) | Deferred to WS-V |
| Shadow call stack | Deferred to WS-V |

## Verification

### Rust Tests (7 tests)

```
barriers::tests::csdb_no_panic
barriers::tests::sb_no_panic
barriers::tests::speculation_safe_bound_check_in_bounds
barriers::tests::speculation_safe_bound_check_out_of_bounds
barriers::tests::speculation_safe_bound_check_zero_bound
barriers::tests::has_feat_csv2_on_host
barriers::tests::barrier_nops_on_host
```

All tests pass on host (x86_64) and target (aarch64).

### Lean Model

The Lean formal model operates on pure functions with no speculative
execution. Speculation barriers are a hardware-only concern applied at
the Rust HAL layer, below the formal verification boundary.

## Cross-Reference

- CSDB: ARM ARM C6.2.49 (Consumption of Speculative Data Barrier)
- SB: ARM ARM C6.2.245 (Speculation Barrier)
- FEAT_CSV2: ARM ARM D19.2.66 (ID_AA64PFR0_EL1.CSV2)
- Cortex-A76 TRM §11.1: Speculative execution mitigations
- Barriers module: `rust/sele4n-hal/src/barriers.rs`
