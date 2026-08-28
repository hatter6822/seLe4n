# seLe4n Hardware Testing Guide (post-AN9, v0.30.10)

This document covers the hardware/QEMU validation steps that complete
WS-AN Phase AN9 (hardware-binding closure).  AN9 closes every
hardware-binding deferred item at the **proof and code** layers; the
items in this document are the **runtime validation** steps that must
be performed on a Raspberry Pi 5 board or in QEMU before declaring
the hardware-binding portfolio fully validated.

The Lean kernel + Rust HAL build, link, and pass every host unit test
without any of the steps below.  These steps verify that the **emitted
instruction sequences** produce the expected **observable hardware
effects** — coherent TLBs, ordered MMIO writes, atomic suspend
windows, and SMP secondary-core wake-up.

> **Audience.** Maintainers performing post-AN9 validation, or
> contributors validating SMP (`smp_enabled` on the kernel command
> line, default `true` since v0.32.142; the Rust-side static is
> `smp::SMP_ENABLED`) for a deployment.

---

## 1. What's already verified in AN9 (no hardware needed)

AN9 lands the following purely-static guarantees that are **already
verified** on every CI commit and **do not need hardware**:

| Sub-task     | Static guarantee                                                 | Verified by |
|--------------|------------------------------------------------------------------|-------------|
| **AN9-A**    | `pageTableUpdate_full_coherency` theorem holds end-to-end        | `lake build SeLe4n.Kernel.Architecture.TlbCacheComposition` |
| **AN9-B**    | `tlbBarrierComplete` is non-vacuous (bitmask + boolean witness)  | `lake exe an9_hardware_binding_suite` |
| **AN9-C**    | `BarrierKind.subsumes` partial order, page-table sequence, MMIO sequence | `lake build SeLe4n.Kernel.Architecture.BarrierComposition` |
| **AN9-D**    | `suspendThread_transientWindowInvariant_default` proven          | `lake exe suspend_resume_suite` |
| **AN9-E**    | VSpaceRoot boot exclusion cross-references AN7-D.2 closure       | docs cross-reference, `lake build` |
| **AN9-F**    | SVC dispatcher routes through typed `SyscallId` decode           | `cargo test -p sele4n-hal --lib svc_dispatch` |
| **AN9-G**    | `wfe_bounded` compiles + behaves correctly on host               | `cargo test -p sele4n-hal --lib cpu` |
| **AN9-H**    | `BarrierKind::emit()` covers every Lean variant (parity test)    | `cargo test -p sele4n-hal --lib barriers` |
| **AN9-I**    | `dsb_osh()`, `dsb_oshst()` callable; OSH algebra closed          | `cargo test -p sele4n-hal --lib barriers` |
| **AN9-J**    | PSCI `cpu_on` round-trip, SMP table, `bring_up_secondaries`      | `cargo test -p sele4n-hal --lib smp` |
| **WS-SM SM1.A** | PSCI full DEN0022D §5 surface — `cpu_off`, `affinity_info`, `psci_version`, `migrate_info_type`, `system_off`, `system_reset` | `cargo test -p sele4n-hal --lib psci` |
| **WS-SM SM1.B** | `PerCpuData` struct (`core_id` first field), `PER_CPU_DATA` static array, `current_per_cpu()` + `current_core_id_from_tpidr()` accessors via TPIDR_EL1, `check_per_cpu_invariants()` boot gate, FFI export `ffi_current_core_id` | `cargo test -p sele4n-hal --lib per_cpu` + `lake exe smp_foundations_suite` |
| **All AN9**  | 15 Lean surface-anchor tests + 36 Rust unit tests                | `lake exe an9_hardware_binding_suite`, `cargo test --workspace` |

The Lean theorems above are machine-checked at build time with zero
`sorry` / `axiom` / `native_decide` in the production proof surface.

---

## 2. What needs hardware/QEMU validation (this document)

The **runtime emission validation** steps below verify that the
hardware actually executes the instruction sequences the proof layer
predicts.  Each section corresponds to a specific AN9 sub-task and
states the test, the expected observable behaviour, the failure
diagnostic, and the remediation playbook if the test fails.

| Step | AN9 sub-task | Hardware effect verified                                |
|------|--------------|---------------------------------------------------------|
| 2.1  | AN9-A        | I-cache really invalidates after `dc cvac` + TLBI       |
| 2.2  | AN9-B        | `dsb ish` actually completes before subsequent TLBI     |
| 2.3  | AN9-D        | Interrupts truly masked across `suspendThread`          |
| 2.4  | AN9-F        | SVC instruction trap routes to typed dispatcher         |
| 2.5  | AN9-G        | `wfe_bounded` falls through after the configured timeout |
| 2.6  | AN9-H        | `BarrierKind::emit()` produces correct ARMv8 instructions |
| 2.7  | AN9-I        | `dsb osh` reaches outer-shareable peers (multi-cluster) |
| 2.8  | AN9-J        | PSCI `CPU_ON` brings up secondary cores under QEMU `-smp 4` |

---

## 3. Environment setup

### 3.1 Required tools

```bash
# QEMU 8.0+ with aarch64 system support
sudo apt install qemu-system-arm qemu-utils

# ARM64 cross-toolchain (for emitting hardware-target binaries)
sudo apt install gcc-aarch64-linux-gnu binutils-aarch64-linux-gnu

# OpenOCD (for on-board JTAG debugging — optional, RPi 5 only)
sudo apt install openocd

# Rust stable (the repo pins the toolchain via rust/rust-toolchain.toml).
# Run the target-add from rust/ so the pinned toolchain override applies —
# from the repo root it would land in your default toolchain instead.
(cd rust && rustup target add aarch64-unknown-none)

# Lean 4.28.0 (already installed via setup_lean_env.sh)
./scripts/setup_lean_env.sh
```

### 3.2 Setup script

A turnkey environment setup script for a fresh Ubuntu/Debian host (it
installs the apt tooling and the Rust target; OpenOCD and rustup
themselves are detect-and-warn only):

```bash
./scripts/hardware_test_env_setup.sh
```

Run this script once on a new development machine; it is idempotent
and skips any tool that is already installed.

### 3.3 Hardware: Raspberry Pi 5 board (optional but recommended)

For maximum confidence (real silicon validation):

- **Board**: Raspberry Pi 5 (BCM2712, Cortex-A76 ×4, 4 GiB+ RAM).
- **Storage**: a microSD card (≥ 8 GiB) flashed with the seLe4n
  bootloader image.
- **Console**: PL011 UART (GPIO14/15 at 115200 8N1) connected to a
  USB-to-serial adapter on the host.
- **Power**: 27 W USB-C PD (Pi 5 official supply).

Building the deployable image (`kernel8.img` + `config.txt`) is **SM10.E
scope** — the image-packaging script (`scripts/build_rpi5_image.sh`) is
registered debt tracked in
[`docs/planning/SMP_RELEASE_CLOSURE_PLAN.md`](planning/SMP_RELEASE_CLOSURE_PLAN.md)
(SM10.E ships the bootable image). There is **no interim manual path**:
`sele4n-hal` currently builds as a library crate (no `[[bin]]` target, no
`main.rs`), so `cargo build -p sele4n-hal` produces an `.rlib` for the
linker, not a flashable kernel binary — the bootable ELF target, its
linker script, and the image packaging all arrive together with SM10.E.
Once they land, flash the packaged image to the SD card and boot the
board.  All Section 2 tests
that require real silicon (TLB coherence, OSH multi-cluster,
PMCCNTR_EL0 timing) execute on this path.

---

## 4. Step-by-step validation procedures

### 4.1 AN9-A — TLB+Cache composition (page-table update coherency)

**What we're checking:** after the kernel writes a page-table descriptor
and emits the canonical `dsb ishst → dc cvac → dsb ish → tlbi → dsb ish
→ isb → ic iallu` sequence, subsequent instruction fetches must see
the new mapping.

**Procedure:**

```bash
# 1. Boot the kernel under QEMU with virt machine (8 GB RAM).
./scripts/test_qemu_tlb_cache_coherence.sh

# 2. The script:
#    a. Boots the kernel.
#    b. Maps a 4 KiB page R+W at VA 0x10_0000_0000.
#    c. Writes 0xDEADBEEF to the page.
#    d. Re-maps the SAME VA as R+X (changes permissions).
#    e. Branches to VA 0x10_0000_0000 — the byte sequence at offset 0
#       must execute as instructions, not be loaded as data.
#    f. Confirms the I-cache fetched the new mapping (no stale R+W
#       fault).
```

**Expected output:** `[PASS] TLB+Cache coherency verified`.

**Failure diagnostic:** if the test segfaults with a permission fault
on the branch, the I-cache did not invalidate.  Diagnostic steps:

1. Examine `kernel.log` for the exact `dsb`/`tlbi` sequence the kernel
   emitted (use `RUST_LOG=trace`).
2. Run with QEMU's `-d in_asm,exec` to dump the actual instruction
   trace and confirm the canonical sequence fired.
3. If the sequence fired but the fault still occurred, file a bug
   against `BarrierKind::emit_armv8_page_table_update`; QEMU's MMU
   model may be more relaxed than real silicon.

### 4.2 AN9-B — `tlbBarrierComplete` (DSB ISH + ISB after every TLBI)

**What we're checking:** every `tlbi` instruction in the HAL is
followed by `dsb ish` and `isb` (per ARM ARM D8.11).

**Procedure:**

```bash
# Static-analysis check on the HAL source (runs at build time):
cargo build --manifest-path rust/Cargo.toml -p sele4n-hal

# Unit-level barrier coverage that exists today:
cargo test --manifest-path rust/Cargo.toml -p sele4n-hal barriers
./scripts/test_qemu_tlb_cache_coherence.sh   # QEMU TLB/cache coherence exerciser
```

> **Planned** — the dedicated instruction-trace audit
> (`scripts/test_qemu_tlb_barrier_audit.sh`) is registered SM10.B debt
> (see `docs/planning/SMP_RELEASE_CLOSURE_PLAN.md`). The planned runtime check captures the `-d in_asm` trace, greps for every
`tlbi` mnemonic, and asserts the immediately-following two
instructions are `dsb ish` and `isb`.

**Expected output:** `[PASS] N TLBI instructions, all bracketed`.

**Failure diagnostic:** any `tlbi` not followed by the bracket prints
`[FAIL] TLBI at 0xPC not bracketed`.  The fix is in
`rust/sele4n-hal/src/tlb.rs`: add the missing barrier emission to the
specific `tlbi_*` helper.

### 4.3 AN9-D — `suspendThread` atomicity (interrupts masked window)

**What we're checking:** the FFI wrapper `sele4n_suspend_thread` keeps
PSTATE.I = 1 (IRQ masked) for the entire duration of the inner Lean
dispatch.

**Procedure:**

```bash
# Model-level coverage that exists today:
source ~/.elan/env && lake exe suspend_resume_suite
cargo test --manifest-path rust/Cargo.toml -p sele4n-hal cpu
```

> **Planned** — the QEMU-level stress script
> (`scripts/test_qemu_suspend_atomicity.sh`) is registered SM10.B debt
> (see `docs/planning/SMP_RELEASE_CLOSURE_PLAN.md`). The planned test:
1. Spawns 100 threads, each performing 1000 suspend/resume cycles.
2. Concurrent timer ticks try to interleave.
3. Asserts no thread is observed in a partially-cleaned state
   (e.g., `ipcState = .ready` AND `threadState = .Running`).

**Expected output:** `[PASS] 100 000 suspend cycles, 0 partial
windows observed`.

**Failure diagnostic:** if a partial window is observed, the FFI
wrapper is not actually masking IRQs.  Re-check that the
`with_interrupts_disabled` call brackets the entire inner dispatch
in `rust/sele4n-hal/src/ffi.rs::sele4n_suspend_thread`.  Verify by
disassembly that the wrapper emits `msr DAIFSet, #2` before and
`msr DAIFClr, #2` after the inner call.

### 4.4 AN9-F — SVC dispatch (userspace-to-kernel typed routing)

**What we're checking:** an `svc #0` instruction from userspace
correctly dispatches through `handle_synchronous_exception` →
`SyscallArgs::from_trap_frame` → `dispatch_svc`.

**Procedure:**

```bash
# Dispatch-layer coverage that exists today (host-side):
cargo test --manifest-path rust/Cargo.toml -p sele4n-hal svc_dispatch
./scripts/test_rust_conformance.sh   # cross-language ABI conformance
```

> **Planned** — the QEMU userspace round-trip script
> (`scripts/test_qemu_svc_roundtrip.sh`) is registered SM10.B debt
> (see `docs/planning/SMP_RELEASE_CLOSURE_PLAN.md`); it drives the
> userspace program below through every `SyscallId` variant.

The userspace test program (built with `aarch64-linux-gnu-gcc`):

```c
#include <stdint.h>

uint64_t do_svc(uint32_t syscall_id, uint64_t arg0) {
    register uint64_t x0 asm("x0") = arg0;
    register uint64_t x7 asm("x7") = syscall_id;
    asm volatile("svc #0" : "+r"(x0) : "r"(x7) : "memory");
    return x0;
}

int main(void) {
    // Each SyscallId variant 0..33 (COUNT = 34 in both Rust mirrors)
    for (uint32_t id = 0; id < 34; id++) {
        uint64_t ret = do_svc(id, 0);
        // Expect either Ok(0) or specific kernel error.
    }
    return 0;
}
```

**Expected output:** `[PASS] 25 SyscallId variants, dispatch routes
correctly`.

**Failure diagnostic:** if a syscall routes to the wrong handler,
check `rust/sele4n-hal/src/svc_dispatch.rs::SyscallId::from_u32`
matches `sele4n-types::SyscallId` discriminants.  The
`barrier_kind_lean_parity` test catches this at unit-test time but
hardware can detect a mismatch in the trap-frame extraction logic.

### 4.5 AN9-G — Bounded WFE (timeout fall-through)

**What we're checking:** `cpu::wfe_bounded(max_ticks)` falls through
after the timeout even if no event arrives.

**Procedure:**

```bash
# Unit-level coverage that exists today:
cargo test --manifest-path rust/Cargo.toml -p sele4n-hal cpu
```

> **Planned** — the QEMU boot-level script
> (`scripts/test_qemu_wfe_bounded.sh`) is registered SM10.B debt (see
> `docs/planning/SMP_RELEASE_CLOSURE_PLAN.md`). The planned test boots the kernel, masks all event sources, and enters
`wfe_bounded(540_000)` (the 10 ms RPi5 default).  If the WFE was
unconditional, the kernel would hang forever; the bounded variant
must fall through after ~10 ms (verified by host-side wallclock).

**Expected output:** `[PASS] wfe_bounded fell through in N ms (target
≤ 15 ms, actual ≤ 12 ms)`.

**Failure diagnostic:** if the test hangs, check that
`cpu::wfe_bounded` actually reads CNTPCT_EL0 before/after `wfe`.
On boards where CNTFRQ_EL0 is misconfigured, the timeout calculation
will be wrong.  AK5-J's `init_timer` already rejects CNTFRQ_EL0=0,
so this should not happen.

### 4.6 AN9-H — `BarrierKind::emit()` (instruction-level emission)

**What we're checking:** every `BarrierKind` variant produces the
expected ARMv8 instruction byte sequence.

**Procedure:**

```bash
# Emission coverage that exists today (unit tests over the emitters):
cargo test --manifest-path rust/Cargo.toml -p sele4n-hal barriers
```

> **Planned** — the objdump disassembly check
> (`scripts/test_barrier_kind_emission.sh`) is registered SM10.B debt
> (see `docs/planning/SMP_RELEASE_CLOSURE_PLAN.md`). The planned script:
1. Generates a `barrier_emission_test.rs` that calls each
   `BarrierKind::emit()` variant.
2. Compiles to an ARM64 object.
3. `aarch64-linux-gnu-objdump -d` extracts each instruction.
4. Verifies the bytes match the canonical ARMv8 encoding for
   `dsb ish` (`d5033bbf`), `dsb ishst` (`d5033abf`), `dsb osh`
   (`d5033b9f`), `dsb oshst` (`d50338bf`), `isb` (`d5033fdf`).

**Expected output:** `[PASS] All BarrierKind variants emit correct
ARMv8 encoding`.

### 4.7 AN9-I — OSH widening (cross-cluster ordering)

**What we're checking:** `dsb osh` actually reaches the outer-
shareable domain (other clusters), not just the inner-shareable
(same-cluster).  This requires multi-cluster hardware or QEMU with
explicit cluster topology.

**Procedure:**

```bash
# Emitter-level coverage that exists today:
cargo test --manifest-path rust/Cargo.toml -p sele4n-hal barriers
```

> **Planned** — the on-board latency probe
> (`scripts/test_rpi5_osh_widening.sh`) is registered SM10.B debt (see
> `docs/planning/SMP_RELEASE_CLOSURE_PLAN.md`); it requires real silicon.
> The planned test uses an MMIO write to a device register visible across
clusters and verifies that after `dsb oshst` the write is observed
by the cross-cluster reader.  On RPi 5 (single cluster) this collapses
to checking `dsb osh` doesn't crash and doesn't have larger latency
than `dsb ish` (both should be ≈ 30 ns on Cortex-A76).

**Expected output:** `[PASS] dsb osh latency: N ns (≤ 50 ns target)`.

### 4.8 AN9-J — SMP secondary-core bring-up

**What we're checking:** with SMP enabled (the default), all 4 cores reach
their per-core `core_ready` flag and execute concurrent kernel work.

**Procedure:**

```bash
# QEMU with -smp 4 and PSCI firmware.
./scripts/test_qemu_smp_bringup.sh
```

The script (requires `SELE4N_KERNEL_IMAGE` pointing at a built kernel
image; it SKIPs without one):
1. Boots QEMU `virt` with `-smp 4 -machine virt,secure=on,virtualization=on`.
2. Passes the kernel command line (`smp_enabled` defaults to `true`).
3. Captures the UART log and asserts `[smp] core N: ready, entering
   kernel` for cores 1..3 plus the `[boot] Phase 5: N secondary
   core(s) online` rollup.

The cross-core SGI round-trip is the separate
`./scripts/test_qemu_smp_sgi_roundtrip.sh` exerciser (primary signals
each secondary; each secondary acknowledges); the broader SMP behaviour
suites are orchestrated by `./scripts/test_tier4_smp_bootcheck.sh`.

**Expected output** ends with the script's
`[PASS] WS-SM SM1.H.1` line once all secondaries report ready.

**Failure diagnostic:** if any secondary fails to wake, examine the
PSCI return code (`PsciResult::Denied`, `AlreadyOn`, etc.) logged
during `bring_up_secondaries`.  `Denied` typically indicates the
firmware is not configured to accept PSCI calls from EL1; switch to
EL2 or enable PSCI in the firmware build.

### 4.9 WS-SM SM1.B — Per-CPU data + TPIDR_EL1 (closes SMP-M4)

**What we're checking:** every core's `TPIDR_EL1` points at its own
`PerCpuData` slot in the `PER_CPU_DATA` array, so a per-core
identifier lookup is a single `mrs xN, tpidr_el1` instruction.

**Boot core (always reachable, even with `smp_enabled=false` on the
kernel command line):**

```bash
# QEMU boot — primary core only.
./scripts/test_qemu.sh
```

> Note: until SM10.E lands the `sele4n-hal` bootable binary target, this
> script SKIPs gracefully at its kernel-binary check (the crate builds as
> a library today); the boot-log assertions below describe the run once
> that target exists.

The kernel boot log on the primary core MUST contain:

```
[boot] Timer initialized (54 MHz counter, 1ms ticks)
[boot] TPIDR_EL1 set early (Phase 1) to PER_CPU_DATA[0] = 0x<addr>
[boot] current_core_id_from_tpidr() = 0
[boot] IRQ delivery enabled
```

(the TPIDR_EL1 write moved to Phase 1 in audit-pass-4; a
`[boot] TPIDR_EL1 re-confirmed at Phase 4: …` line follows later).

The `PER_CPU_DATA[0]` address must be 64-byte aligned (verified by
the runtime `check_per_cpu_invariants()` immediately before the
TPIDR_EL1 write; a misaligned address would have aborted boot before
this line was emitted).  The `current_core_id_from_tpidr()` value
must equal `0` (boot core's `core_id` field).

**Secondary cores (require SMP enabled — the default):**

```bash
# QEMU with -smp 4.
./scripts/test_qemu_smp_bringup.sh
```

Each secondary core MUST emit its own `core_id = N` log line where
`N == context_id` (1, 2, or 3).  This implicitly verifies that
`boot.S::secondary_entry` correctly computed
`TPIDR_EL1 = PER_CPU_DATA + context_id * PER_CPU_DATA_SLOT_SIZE`
(the `madd` stride against the asm-visible
`PER_CPU_DATA_SLOT_SIZE_SYM` symbol).

**Host coverage (no QEMU required):**

```bash
cargo test -p sele4n-hal --lib per_cpu
```

Runs 30 unit tests in `per_cpu::tests` exercising the host stubs
(struct alignment, const-constructor semantics, layout invariants,
panic on out-of-range `context_id`, `check_per_cpu_invariants`
happy path on the production static AND on well-formed / empty
test slices, panic path on three distinct mis-population
patterns via the inner `check_per_cpu_invariants_in` form).

```bash
lake exe smp_foundations_suite
```

Runs 66 PASS checks including the SM1.B.5 typed-FFI-wrapper
surface (`Concurrency.currentCoreId : BaseIO CoreId`,
`currentCoreId_in_range_marker`, `Inhabited CoreId` default).

**Failure diagnostic:** if `check_per_cpu_invariants()` panics at
boot, the panic message identifies which slot's `core_id` field
diverges from its index (e.g.,
`"PER_CPU_DATA[2].core_id = 99 ≠ 2"`).  This indicates a
const-initialiser regression in `per_cpu.rs::PER_CPU_DATA`; revert
the offending change and ensure each slot is populated with
`PerCpuData::new(i)` where `i` matches the array index.

---

## 5. Continuous validation (CI integration)

After each AN9 hardware test passes once, wire it into Tier-2 CI
as a skip-with-log entry (CI runners typically lack QEMU):

```bash
# Add to scripts/test_tier2_negative.sh:
if command -v qemu-system-aarch64 &>/dev/null; then
    run_check "HW" ./scripts/test_qemu.sh
    run_check "HW" ./scripts/test_qemu_tlb_cache_coherence.sh
    run_check "HW" ./scripts/test_tier4_smp_bootcheck.sh
    # ... plus the SM10.B scripts as they land
else
    echo "[SKIP] QEMU not available — hardware tests SKIPPED"
fi
```

This lets full-fat CI runners exercise the runtime steps while
lightweight runners still pass.

---

## 6. Summary checklist (post-AN9 validation gate)

For each release that lands AN9-touched code, complete this
checklist before tagging:

- [ ] **Static (every commit):**
  - [ ] `lake build` (302+ jobs, 0 warnings)
  - [ ] `lake exe an9_hardware_binding_suite` (15/15 PASS)
  - [ ] `cargo test --workspace` (459+ tests PASS)
  - [ ] `cargo clippy --workspace -- -D warnings` (0 warnings)
  - [ ] `scripts/check_version_sync.sh` PASS

- [ ] **Hardware (recommended, RPi 5 board or QEMU virt):**
  - [ ] §4.1 — TLB+Cache coherency (AN9-A)
  - [ ] §4.2 — TLBI bracket audit (AN9-B)
  - [ ] §4.3 — `suspendThread` atomicity (AN9-D)
  - [ ] §4.4 — SVC round-trip (AN9-F)
  - [ ] §4.5 — Bounded WFE (AN9-G)
  - [ ] §4.6 — BarrierKind emission (AN9-H)
  - [ ] §4.7 — OSH widening (AN9-I)
  - [ ] §4.8 — SMP bring-up under `-smp 4` (AN9-J)

- [ ] **Documentation:**
  - [ ] `CHANGELOG.md` AN9 entry committed
  - [ ] `docs/dev_history/audits/AUDIT_v0.29.0_DEFERRED.md` rows marked RESOLVED
  - [ ] `CLAUDE.md` Active workstream context refreshed

After the static gate passes for the v1.0.0 commit, the project is
green to ship.  The hardware steps in §4 are the high-confidence
post-release validation that completes the AN9 portfolio.

---

## 7. Where to file issues

If any test in §4 fails:

1. Capture the failing test's full output.
2. Capture the QEMU `-d in_asm,exec,int` trace if applicable.
3. File a GitHub issue against `hatter6822/seLe4n` with:
   - Test ID (e.g., "AN9-A §4.1")
   - Hardware target (QEMU virt / RPi 5 / other)
   - Expected vs. observed behaviour
   - Trace excerpts

The maintainers will triage and either patch the kernel/HAL or update
the test to match a verified hardware behaviour.
